"""SW-02 §4–§5 — verification of the clustered coverage law. Research version.

    python experiments/2026-07-26-sw02-exchangeability-audit/verify_indicator_icc.py

Regenerates every number in paper/00_draft.md §4 and §5.

NOTE: this raises NotImplementedError until L2 lands `split_conformal` in calkit. That is
deliberate — no result depending on the guarantee-bearing line is published before that line
is typed by hand. The numbers in the draft came from a reference implementation of the same
three lines and must reproduce exactly.

Per STRUCTURE.md this shares nothing with the lesson version except
`calkit.conformal.split_conformal`.

What is being tested
--------------------
Theorem 1: for b i.i.d. clusters of m within-cluster-exchangeable scores,

    sqrt(n) (C - p) -> N(0, p(1-p) * [1 + (m-1) * rho_I(p)])

where C = F(q_hat) is calibration-conditional coverage and rho_I(p) is the intra-cluster
correlation of the *exceedance indicators* at level p:

    rho_I(p) = (delta(p) - p^2) / (p(1-p)),    delta(p) = P(two same-cluster scores <= q_p).

The rival hypothesis — Kish's design effect applied to the *score* correlation, as written
down in the 2026 literature — is evaluated alongside it and falsified in check 2.

Coverage is computed exactly as F(q_hat), not estimated on a finite test sample. That removes
test-set binomial noise so the calibration-conditional law is measured directly rather than
convolved with measurement error.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from scipy.stats import beta as beta_dist, expon, multivariate_normal, norm

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from calkit.conformal import split_conformal  # noqa: E402

N_FAMILIES = 50
FAMILY_SIZE = 4
ALPHA = 0.10
N_REPS = 20_000
SEED = 0
RHOS = (0.0, 0.2, 0.4, 0.6, 0.8, 0.95, 1.0)
N = N_FAMILIES * FAMILY_SIZE


def delta_gaussian(p: float, rho: float) -> float:
    """Copula diagonal: P(both members of a same-cluster pair fall below the p-quantile)."""
    if rho >= 1.0:
        return p
    if rho <= 0.0:
        return p * p
    z = norm.ppf(p)
    return float(multivariate_normal(mean=[0, 0], cov=[[1, rho], [rho, 1]]).cdf([z, z]))


def rho_indicator(p: float, rho: float) -> float:
    """Intra-cluster correlation of the exceedance indicators at level p."""
    return (delta_gaussian(p, rho) - p**2) / (p * (1 - p))


def coverage_law_beta(p: float, n_eff: float):
    """Moment-matched Beta: the iid law with n replaced by n_eff."""
    nu = max(n_eff - 1.0, 1e-9)
    return beta_dist(p * nu, (1 - p) * nu)


def simulate(rho: float, alpha: float = ALPHA, reps: int = N_REPS, seed: int = SEED,
             marginal: str = "gauss") -> np.ndarray:
    """Exact calibration-conditional coverage, one value per replication."""
    rng = np.random.default_rng(seed)
    out = np.empty(reps)
    for r in range(reps):
        anc = rng.normal(size=(N_FAMILIES, 1))
        own = rng.normal(size=(N_FAMILIES, FAMILY_SIZE))
        gauss = (np.sqrt(rho) * anc + np.sqrt(1.0 - rho) * own).ravel()
        if marginal == "gauss":
            cal, cdf = gauss, norm.cdf
        elif marginal == "exp":                      # same copula, different marginal
            cal, cdf = expon.ppf(norm.cdf(gauss)), expon.cdf
        else:
            raise ValueError(marginal)
        out[r] = float(cdf(split_conformal(cal, alpha)))
    return out


def check_1_law_and_endpoints() -> None:
    k = int(np.ceil((N + 1) * (1 - ALPHA)))
    p = k / (N + 1)
    print(f"\n[1] THE LAW  (n={N} = {N_FAMILIES}x{FAMILY_SIZE}, alpha={ALPHA}, k={k}, "
          f"p={p:.4f}, {N_REPS} reps)")
    print(f"{'rho':>5} {'rho_I':>7} {'n_eff':>7} {'sd_sim':>7} {'sd_law':>7} {'sd_naive':>8} "
          f"{'p05_sim':>8} {'p05_law':>8} {'p95_sim':>8} {'p95_law':>8}")
    worst_law = worst_naive = 0.0
    for rho in RHOS:
        cov = simulate(rho)
        ri = rho_indicator(p, rho)
        n_eff = N / (1 + (FAMILY_SIZE - 1) * ri)
        n_naive = N / (1 + (FAMILY_SIZE - 1) * rho)
        sd_law = np.sqrt(p * (1 - p) / n_eff)
        sd_naive = np.sqrt(p * (1 - p) / n_naive)
        law = coverage_law_beta(p, n_eff)
        sd_sim = cov.std(ddof=1)
        worst_law = max(worst_law, abs(sd_sim - sd_law))
        worst_naive = max(worst_naive, abs(sd_sim - sd_naive))
        print(f"{rho:>5.2f} {ri:>7.4f} {n_eff:>7.1f} {sd_sim:>7.4f} {sd_law:>7.4f} "
              f"{sd_naive:>8.4f} {np.percentile(cov, 5):>8.4f} {law.ppf(0.05):>8.4f} "
              f"{np.percentile(cov, 95):>8.4f} {law.ppf(0.95):>8.4f}")
    print(f"\n    max |sd_sim - sd_law|   = {worst_law:.5f}   <- Theorem 1")
    print(f"    max |sd_sim - sd_naive| = {worst_naive:.5f}   <- score-ICC rival, "
          f"{worst_naive / worst_law:.1f}x worse")

    print("\n[2] ENDPOINT RECOVERY")
    iid = beta_dist(k, N + 1 - k)
    cov0 = simulate(0.0)
    print(f"    rho=0  Beta({k},{N + 1 - k}) analytic : sd={iid.std():.4f} "
          f"p05={iid.ppf(.05):.4f} p95={iid.ppf(.95):.4f}")
    print(f"           simulated              : sd={cov0.std(ddof=1):.4f} "
          f"p05={np.percentile(cov0, 5):.4f} p95={np.percentile(cov0, 95):.4f}")
    kk = int(np.ceil(k / FAMILY_SIZE))
    ramos = beta_dist(kk, N_FAMILIES + 1 - kk)
    cov1 = simulate(1.0)
    ours = coverage_law_beta(p, float(N_FAMILIES))
    print(f"    rho=1  Ramos Beta({kk},{N_FAMILIES + 1 - kk}) [2605.19024 §4.2]: "
          f"sd={ramos.std():.4f} p05={ramos.ppf(.05):.4f} p95={ramos.ppf(.95):.4f}")
    print(f"           our law at n_eff=b={N_FAMILIES}   : sd={ours.std():.4f} "
          f"p05={ours.ppf(.05):.4f} p95={ours.ppf(.95):.4f}")
    print(f"           simulated              : sd={cov1.std(ddof=1):.4f} "
          f"p05={np.percentile(cov1, 5):.4f} p95={np.percentile(cov1, 95):.4f}")
    print("    (residual at rho=1 is ceil(k/m) discreteness — see draft §7, not claimed)")


def check_3_level_dependence() -> None:
    print("\n[3] LEVEL-DEPENDENCE — same clustering (rho=0.6, m=4), three coverage targets")
    print(f"{'1-alpha':>8} {'p':>7} {'rho_I':>7} {'DEFF':>6} {'n_eff':>7} {'sd_sim':>7} {'sd_law':>7}")
    for alpha in (0.10, 0.05, 0.01):
        k = int(np.ceil((N + 1) * (1 - alpha)))
        p = k / (N + 1)
        ri = rho_indicator(p, 0.6)
        deff = 1 + (FAMILY_SIZE - 1) * ri
        cov = simulate(0.6, alpha=alpha, reps=8000)
        print(f"{1 - alpha:>8.2f} {p:>7.4f} {ri:>7.4f} {deff:>6.3f} {N / deff:>7.1f} "
              f"{cov.std(ddof=1):>7.4f} {np.sqrt(p * (1 - p) * deff / N):>7.4f}")

    print("\n[4] EXACT Phi_2 vs SMALL-rho EXPANSION rho*phi(z_p)^2/(p(1-p)) — exact/linear ratio")
    print(f"{'p':>6} {'rho=0.2':>9} {'rho=0.5':>9} {'rho=0.8':>9}")
    for p in (0.50, 0.90, 0.95, 0.99):
        cells = []
        for rho in (0.2, 0.5, 0.8):
            linear = rho * norm.pdf(norm.ppf(p)) ** 2 / (p * (1 - p))
            cells.append(f"{rho_indicator(p, rho) / linear:>9.2f}")
        print(f"{p:>6.2f} " + " ".join(cells))
    print("    the expansion is unusable in the tails — use the exact form (draft §5)")


def check_5_marginal_invariance_is_a_code_check() -> None:
    """Corollary 1 is about COPULAS. This function is a regression test, not evidence.

    Varying the marginal cannot falsify anything: under a monotone transform T,
    x <= q_p iff u <= p, so T maps the order statistic and the CDF together and F(q_hat) is
    pointwise unchanged. The two rows below are bit-identical by construction; they are run
    only to catch a coding error in the transform path. Reporting them as numerical
    confirmation of distribution-freeness was an error made on 2026-07-26 — see
    paper/integrity.md SW-05.

    The real test of Corollary 1 varies the COPULA family at matched delta(p) and lives in
    sim_validation.py Test 1 (Gaussian / t(3) / Clayton, sd within 1.9%).
    """
    print("\n[5] MARGINAL INVARIANCE — a code check, NOT evidence (see integrity.md SW-05)")
    k = int(np.ceil((N + 1) * (1 - ALPHA)))
    p = k / (N + 1)
    g = simulate(0.6, reps=8000, marginal="gauss")
    e = simulate(0.6, reps=8000, marginal="exp")
    deff = 1 + (FAMILY_SIZE - 1) * rho_indicator(p, 0.6)
    print(f"    Gaussian marginal : mean={g.mean():.4f} sd={g.std(ddof=1):.4f}")
    print(f"    Exp(1)   marginal : mean={e.mean():.4f} sd={e.std(ddof=1):.4f}")
    print(f"    predicted by law  : sd={np.sqrt(p * (1 - p) * deff / N):.4f}")
    assert np.allclose(g, e), "monotone-transform path is broken"
    print("    (identical by construction — the copula test is in sim_validation.py Test 1)")


def main() -> int:
    check_1_law_and_endpoints()
    check_3_level_dependence()
    check_5_marginal_invariance_is_a_code_check()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
