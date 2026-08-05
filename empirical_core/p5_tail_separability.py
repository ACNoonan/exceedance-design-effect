"""EC-01 Precondition 5 — can E3's estimator tell a design-effect FLOOR from a DECAY?

    ../../.venv/bin/python p5_tail_separability.py

WHY THIS RUNS BEFORE E3 TOUCHES REAL DATA
Proposition 3 (SW-02 §5.1) settles the theory: lim_{p->1} rho_I(p) = lambda_U, the copula's upper
tail-dependence coefficient. Gaussian has lambda_U = 0 so the attenuation is forced; t(3) has
lambda_U > 0 so the design effect has a FLOOR and shared ancestry never gets cheaper. §5.1 says
which case a system is in "is a property of its copula's tail, not of clustering per se" -- and the
paper never checks which case its own live instance is in. That is E3.

But E3 is only worth running if the estimator can SEE the difference at the sample size the release
actually provides. The released set has ~25k rows and only **500 clusters**, and at p = 0.99 the
exceedances that carry the signal are scarce. This script asks whether a floor and a decay are
distinguishable there at all.

** THIS IS NOT A RE-RUN OF verify_tail_limit.py. ** That script confirms the ANALYTIC limits at
1-p = 1e-10 and says nothing about estimation. This one estimates, from finite clustered samples on
the RELEASED size profile, with the cluster bootstrap E3 will actually report.

THE DESIGN, AND WHY IT CAN FAIL
Two synthetic worlds on the released 500-family size profile, MATCHED at rho_I(0.90):

  GAUSSIAN one-factor, r tuned so rho_I(0.90) = target      -> lambda_U = 0     (decay)
  t(nu=3)  one-factor, r tuned to the SAME rho_I(0.90)      -> lambda_U > 0     (floor)

Matched at 0.90 and divergent at 0.99 by construction, so the experiment has a built-in negative
control and a built-in positive one:

  NEGATIVE CONTROL  the two CIs must OVERLAP at p = 0.90. They were matched there. If they are
                    already disjoint at 0.90 the tuning is wrong and nothing downstream is readable.
  THE QUESTION      are the two CIs DISJOINT at p = 0.99? If not, E3 cannot answer H2 on this
                    artifact and must report that instead of a curve.

A pass here does not make H2 true. It makes H2 askable.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import brentq
from scipy.stats import chi2, multivariate_normal, multivariate_t, norm, t as tdist

# the audit lane's modules sit beside this lane in the working tree, and under
# prm/ in the published code archive. Cover both layouts.
PARENT = Path(__file__).resolve().parents[1] / "2026-07-26-sw02-exchangeability-audit"
for _p in (Path(__file__).resolve().parents[1] / "prm", PARENT):
    sys.path.insert(0, str(_p))
from prm_measurement import anova_icc, load  # noqa: E402  (same estimator as §6.1 and E3)

SEED = 20260729
NU = 3                                   # t degrees of freedom; §5.1's worked example
R_GAUSS = 0.60                           # §5's worked example (rho = 0.6)
LEVELS = (0.80, 0.90, 0.95, 0.99)
MATCH_AT = 0.90
BOOT = 400                               # cluster-bootstrap replicates per world
REALISATIONS = 12                        # independent synthetic datasets; sets sep-frac resolution


# ------------------------------------------------------------------ exact copula diagonals

def rho_I_gauss(p: float, r: float) -> float:
    z = norm.ppf(p)
    d = float(multivariate_normal.cdf([z, z], mean=[0, 0], cov=[[1, r], [r, 1]]))
    return (d - p * p) / (p * (1 - p))


def rho_I_t(p: float, r: float, nu: int = NU) -> float:
    q = tdist.ppf(p, nu)
    d = float(multivariate_t.cdf([q, q], loc=[0, 0], shape=[[1, r], [r, 1]], df=nu))
    return (d - p * p) / (p * (1 - p))


def lambda_U_t(r: float, nu: int = NU) -> float:
    """Upper tail dependence of a bivariate t. Zero for Gaussian at every |r| < 1."""
    return float(2 * tdist.cdf(-np.sqrt((nu + 1) * (1 - r) / (1 + r)), nu + 1))


# ------------------------------------------------------------------ generators

def gen_gauss(sizes, r, rng):
    Z = rng.standard_normal(len(sizes))
    return [norm.cdf(np.sqrt(r) * Z[j] + np.sqrt(1 - r) * rng.standard_normal(int(sizes[j])))
            for j in range(len(sizes))]


def gen_t(sizes, r, rng, nu=NU):
    """Exchangeable t copula within cluster: shared chi-square mixing variable per family."""
    Z = rng.standard_normal(len(sizes))
    W = chi2.rvs(nu, size=len(sizes), random_state=rng)
    out = []
    for j in range(len(sizes)):
        y = np.sqrt(r) * Z[j] + np.sqrt(1 - r) * rng.standard_normal(int(sizes[j]))
        out.append(tdist.cdf(y / np.sqrt(W[j] / nu), nu))
    return out


# ------------------------------------------------------------------ estimation

def rho_hat(fams, level):
    """rho_I at the EMPIRICAL quantile -- mirrors what E3 must do on real data."""
    q = np.quantile(np.concatenate(fams), level)
    ind = [(f <= q).astype(float) for f in fams]
    grand = np.concatenate(ind).mean()
    if not (0 < grand < 1):
        return float("nan")
    return anova_icc(ind)


def boot_ci(fams, level, rng, reps=BOOT):
    k = len(fams)
    vals = np.empty(reps)
    for b in range(reps):
        idx = rng.integers(0, k, k)
        vals[b] = rho_hat([fams[i] for i in idx], level)
    vals = vals[np.isfinite(vals)]
    return float(np.percentile(vals, 2.5)), float(np.percentile(vals, 97.5))


def main() -> int:
    rng = np.random.default_rng(SEED)
    sizes = np.array([len(f) for f in load()])
    n, k = int(sizes.sum()), len(sizes)
    m_til = float((sizes ** 2).sum() / sizes.sum())

    target = rho_I_gauss(MATCH_AT, R_GAUSS)
    r_t = brentq(lambda r: rho_I_t(MATCH_AT, r) - target, 1e-4, 0.999, xtol=1e-8)
    lam_g, lam_t = 0.0, lambda_U_t(r_t)

    print("=" * 78)
    print("EC-01 P5 — is a design-effect FLOOR separable from a DECAY at n_clusters = 500?")
    print("=" * 78)
    print(f"released size profile: k = {k} families, n = {n}, m_tilde = {m_til:.2f}, "
          f"sizes {sizes.min()}-{sizes.max()}")
    print(f"matched at p = {MATCH_AT}:  rho_I = {target:.4f}")
    print(f"  GAUSSIAN r = {R_GAUSS:.4f}   lambda_U = {lam_g:.4f}   (attenuation forced)")
    print(f"  t(nu={NU})  r = {r_t:.4f}   lambda_U = {lam_t:.4f}   (DEFF floor)")
    print(f"  DEFF floor implied for this profile: 1 + (m_tilde-1)*lambda_U = "
          f"{1 + (m_til - 1) * lam_t:.1f}\n")

    print("exact rho_I(p) by level — what the estimator is being asked to recover:")
    print(f"  {'p':>6}  {'gaussian':>9}  {'t(3)':>9}")
    exact = {}
    for p in LEVELS:
        eg, et = rho_I_gauss(p, R_GAUSS), rho_I_t(p, r_t)
        exact[p] = (eg, et)
        print(f"  {p:>6.2f}  {eg:>9.4f}  {et:>9.4f}")
    print()

    rows = {}
    for name, gen, r in (("gaussian", gen_gauss, R_GAUSS), ("t3", gen_t, r_t)):
        for p in LEVELS:
            rows[(name, p)] = {"pt": [], "lo": [], "hi": []}
        for _ in range(REALISATIONS):
            fams = gen(sizes, r, rng)
            for p in LEVELS:
                lo, hi = boot_ci(fams, p, rng)
                rows[(name, p)]["pt"].append(rho_hat(fams, p))
                rows[(name, p)]["lo"].append(lo)
                rows[(name, p)]["hi"].append(hi)

    def agg(name, p):
        d = rows[(name, p)]
        return (float(np.mean(d["pt"])), float(np.mean(d["lo"])), float(np.mean(d["hi"])))

    def disjoint_frac(p):
        """Fraction of realisations whose CIs separate. Averaging CI endpoints across
        realisations blends within-realisation uncertainty with across-realisation spread;
        E3 gets ONE dataset, so the honest statistic is how often one dataset suffices."""
        g, t = rows[("gaussian", p)], rows[("t3", p)]
        return float(np.mean([(g["hi"][i] < t["lo"][i]) or (t["hi"][i] < g["lo"][i])
                              for i in range(len(g["pt"]))]))

    print(f"estimated rho_I with 95% cluster-bootstrap CI "
          f"({REALISATIONS} realisations x {BOOT} reps):")
    print(f"  {'p':>6}  {'gaussian (CI)':>28}  {'t(3) (CI)':>28}  {'sep.frac':>9}")
    result = {"levels": {}, "meta": {
        "k": k, "n": n, "m_tilde": m_til, "nu": NU, "r_gauss": R_GAUSS, "r_t": r_t,
        "lambda_U_gauss": lam_g, "lambda_U_t": lam_t, "matched_at": MATCH_AT,
        "boot": BOOT, "realisations": REALISATIONS, "seed": SEED}}
    for p in LEVELS:
        gp, glo, ghi = agg("gaussian", p)
        tp, tlo, thi = agg("t3", p)
        frac = disjoint_frac(p)
        print(f"  {p:>6.2f}  {gp:>8.4f} [{glo:.4f},{ghi:.4f}]  "
              f"{tp:>8.4f} [{tlo:.4f},{thi:.4f}]  {frac:>9.2f}")
        result["levels"][f"{p}"] = {
            "exact_gauss": exact[p][0], "exact_t": exact[p][1],
            "gauss": {"pt": gp, "ci_lo": glo, "ci_hi": ghi},
            "t3": {"pt": tp, "ci_lo": tlo, "ci_hi": thi},
            "disjoint_frac": frac,
            "bias_gauss": gp - exact[p][0], "bias_t": tp - exact[p][1],
            "rel_bias_gauss": (gp - exact[p][0]) / exact[p][0],
            "rel_bias_t": (tp - exact[p][1]) / exact[p][1],
            "relwidth_gauss": (ghi - glo) / gp, "relwidth_t": (thi - tlo) / tp}

    print("\nESTIMATOR BIAS against the exact copula value — a finding in its own right:")
    print(f"  {'p':>6}  {'gaussian rel.bias':>18}  {'t(3) rel.bias':>18}")
    for p in LEVELS:
        r = result["levels"][f"{p}"]
        print(f"  {p:>6.2f}  {r['rel_bias_gauss']:>17.1%}  {r['rel_bias_t']:>17.1%}")
    print("  The parent lane's P4 measured the ANOVA estimator ~10% low at p=0.89 on this")
    print("  size profile. If the tail bias is materially worse, every tail rho_I in the")
    print("  paper carries an unstated downward correction.")

    print("\n" + "=" * 78)
    print("PRECONDITIONS — each could have come out wrong")
    print("=" * 78)

    gp90, glo90, ghi90 = agg("gaussian", MATCH_AT)
    pc_a = glo90 <= exact[MATCH_AT][0] <= ghi90
    print(f"  PC-a  gaussian CI at p={MATCH_AT} covers the exact rho_I "
          f"({exact[MATCH_AT][0]:.4f} in [{glo90:.4f},{ghi90:.4f}]) -> "
          f"{'PASS' if pc_a else 'FAIL'}")
    print("        would fail if: the generator, the ANOVA estimator on indicators, or the")
    print("        empirical-quantile step were wrong. Nothing below is readable without it.")

    pc_b = result["levels"][f"{MATCH_AT}"]["disjoint_frac"] <= 0.10
    print(f"  PC-b  NEGATIVE CONTROL: CIs OVERLAP at p={MATCH_AT} where they were matched "
          f"(separation fraction {result['levels'][f'{MATCH_AT}']['disjoint_frac']:.2f} "
          f"<= 0.10) -> {'PASS' if pc_b else 'FAIL'}")
    print("        would fail if: the r-tuning missed, in which case a separation at 0.99")
    print("        would be measuring the tuning error and not the tail.")

    # RELATIVE width, not absolute. The smoke run failed this check as originally written
    # because rho_I itself shrinks toward 0 in the Gaussian tail, so absolute CI width
    # shrinks with it while precision genuinely degrades. Absolute width was the wrong
    # statistic; the ratio to the estimate is what exceedance scarcity shows up in.
    rw = [result["levels"][f"{p}"]["relwidth_gauss"] for p in LEVELS]
    pc_c = rw[-1] > rw[0]
    print(f"  PC-c  RELATIVE CI width grows into the tail ({rw[0]:.2f} at 0.80 -> "
          f"{rw[-1]:.2f} at 0.99) -> {'PASS' if pc_c else 'FAIL'}")
    print("        would fail if: the bootstrap is not seeing exceedance scarcity at p=0.99,")
    print("        i.e. the interval is not measuring what it claims.")

    verdict = result["levels"]["0.99"]["disjoint_frac"] >= 0.80
    ok = pc_a and pc_b and pc_c
    result["preconditions"] = {"pc_a": bool(pc_a), "pc_b": bool(pc_b), "pc_c": bool(pc_c)}
    result["separable_at_0.99"] = bool(verdict)

    print("\n" + "=" * 78)
    if not ok:
        print("  A PRECONDITION FAILED — the separability verdict below may not be quoted.")
    print(f"  VERDICT: floor vs decay {'IS' if verdict else 'IS NOT'} separable at p = 0.99 "
          f"on the released size profile")
    print(f"           (separation fraction {result['levels']['0.99']['disjoint_frac']:.2f}, "
          f"bar 0.80 — one dataset must usually suffice, because E3 gets one).")
    if verdict:
        print("  -> E3 may proceed. H2 is askable on this artifact.")
    else:
        print("  -> E3 must report H2 as UNTESTABLE by this instrument, not as a null result.")
    print("=" * 78)

    out = Path(__file__).resolve().parent / "result_p5.json"
    out.write_text(json.dumps(result, indent=2))
    print(f"\nwrote {out.name}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
