"""EC-01 P5b — how many CLUSTERS does it take to see a design-effect floor at all?

    ../../.venv/bin/python p5b_cluster_budget.py

P5 established that a floor (t(3), lambda_U > 0) and a decay (Gaussian, lambda_U = 0) are NOT
separable at p = 0.99 on the released 500-question profile: separation fraction 0.25 against a bar
of 0.80, with the bootstrap CI running ~79% of the point estimate. The estimator is close to
unbiased there (+6.4% Gaussian, -0.4% t3) -- the obstruction is variance, not bias.

"Untestable" is a weak thing to publish. This turns it into a DESIGN REQUIREMENT: sweep the number
of clusters and find where separation becomes reliable. Two payoffs, both concrete:

  FOR E2   the beam sweep generates its own data, so b is ours to choose. This sets the generation
           budget. Without it we would pick a round number and hope.
  FOR THE  §8 recommends estimating rho_I(p) from same-cluster pairs "at every level
  PAPER    simultaneously" and §5 offers the comfort that shared ancestry costs less in the tail.
           If that comfort cannot be VERIFIED below some cluster count, practitioners deploying at
           b in the hundreds cannot check which regime they are in -- a caveat the paper does not
           currently state.

Size profile is resampled from the released one, so m_tilde is held at the released value while b
varies. That isolates cluster count from size structure, which is the point.

Uses a vectorised one-way ANOVA on indicator counts, algebraically identical to
prm_measurement.anova_icc: for 0/1 data with per-family counts c_j and sizes m_j,
  ssb = sum_j m_j (c_j/m_j - grand)^2      ssw = sum_j (c_j - c_j^2/m_j)
Precondition P1 below checks the two agree on real inputs rather than assuming the algebra.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import brentq
from scipy.stats import chi2, norm, t as tdist

HERE = Path(__file__).resolve().parent
# the audit lane's modules sit beside this lane in the working tree, and under
# prm/ in the published code archive. Cover both layouts.
PARENT = HERE.parent / "2026-07-26-sw02-exchangeability-audit"
for _p in (HERE.parent / "prm", PARENT):
    sys.path.insert(0, str(_p))
from prm_measurement import anova_icc, load  # noqa: E402

sys.path.insert(0, str(HERE))
from p5_tail_separability import lambda_U_t, rho_I_gauss, rho_I_t  # noqa: E402

SEED = 20260729
NU = 3
R_GAUSS = 0.60
MATCH_AT = 0.90
TEST_AT = 0.99
B_GRID = (500, 1000, 2000, 4000, 8000)
BOOT = 300
REALISATIONS = 20
BAR = 0.80


def icc_from_counts(c: np.ndarray, m: np.ndarray) -> float:
    """Vectorised one-way random-effects ICC for 0/1 data. Same estimator as anova_icc."""
    k = len(m)
    n = m.sum()
    grand = c.sum() / n
    means = c / m
    ssb = float((m * (means - grand) ** 2).sum())
    ssw = float((c - c * c / m).sum())
    msb, msw = ssb / (k - 1), ssw / (n - k)
    m0 = (n - (m ** 2).sum() / n) / (k - 1)
    return float((msb - msw) / (msb + (m0 - 1) * msw))


def gen(kind, sizes, r, rng, nu=NU):
    """Flat score array plus family boundaries. One factor per family; t shares chi2 per family."""
    b = len(sizes)
    Z = np.repeat(rng.standard_normal(b), sizes)
    E = rng.standard_normal(int(sizes.sum()))
    y = np.sqrt(r) * Z + np.sqrt(1 - r) * E
    if kind == "gaussian":
        return norm.cdf(y)
    W = np.repeat(chi2.rvs(nu, size=b, random_state=rng), sizes)
    return tdist.cdf(y / np.sqrt(W / nu), nu)


def rho_hat_flat(flat, sizes, starts, level):
    q = np.quantile(flat, level)
    ind = (flat <= q).astype(np.int64)
    c = np.add.reduceat(ind, starts[:-1]).astype(float)
    if not (0 < c.sum() / sizes.sum() < 1):
        return float("nan")
    return icc_from_counts(c, sizes.astype(float))


def boot_ci(flat, sizes, starts, level, rng, reps=BOOT):
    b = len(sizes)
    vals = np.empty(reps)
    for i in range(reps):
        pick = rng.integers(0, b, b)
        samp = np.concatenate([flat[starts[j]:starts[j + 1]] for j in pick])
        sz = sizes[pick]
        st = np.concatenate([[0], np.cumsum(sz)])
        vals[i] = rho_hat_flat(samp, sz, st, level)
    vals = vals[np.isfinite(vals)]
    return float(np.percentile(vals, 2.5)), float(np.percentile(vals, 97.5))


def main() -> int:
    rng = np.random.default_rng(SEED)
    released = np.array([len(f) for f in load()])
    m_til_rel = float((released ** 2).sum() / released.sum())

    target = rho_I_gauss(MATCH_AT, R_GAUSS)
    r_t = brentq(lambda r: rho_I_t(MATCH_AT, r) - target, 1e-4, 0.999, xtol=1e-8)
    exact_g, exact_t = rho_I_gauss(TEST_AT, R_GAUSS), rho_I_t(TEST_AT, r_t)

    print("=" * 78)
    print("EC-01 P5b — cluster budget for separating a DEFF floor from a decay")
    print("=" * 78)
    print(f"matched at p={MATCH_AT}: rho_I = {target:.4f}   "
          f"(gaussian r={R_GAUSS:.4f}, t{NU} r={r_t:.4f}, lambda_U={lambda_U_t(r_t):.4f})")
    print(f"at p={TEST_AT} the truth to be separated: gaussian {exact_g:.4f} vs "
          f"t{NU} {exact_t:.4f}   (gap {exact_t - exact_g:.4f})")
    print(f"released profile m_tilde = {m_til_rel:.2f}, held fixed while b varies\n")

    # P1 — the vectorised estimator must agree with the published one on a real input.
    probe_fams = [np.asarray(f) for f in load()]
    q0 = np.quantile(np.concatenate(probe_fams), MATCH_AT)
    ind_fams = [(f <= q0).astype(float) for f in probe_fams]
    ref = anova_icc(ind_fams)
    c0 = np.array([float((f <= q0).sum()) for f in probe_fams])
    m0 = np.array([float(len(f)) for f in probe_fams])
    fast = icc_from_counts(c0, m0)
    p1 = abs(ref - fast) < 1e-10
    print(f"P1  vectorised ICC == prm_measurement.anova_icc on the released set "
          f"({fast:.12f} vs {ref:.12f}) -> {'PASS' if p1 else 'FAIL'}")
    print("    would fail if: the count-form algebra is not the same estimator, in which case")
    print("    every number below is from a different instrument than the paper's.\n")
    if not p1:
        print("  PRECONDITION FAILED — no number below may be quoted.")
        return 1

    print(f"  {'b':>7}  {'n':>8}  {'gaussian (CI)':>26}  {'t3 (CI)':>26}  {'sep':>5}")
    rows = {}
    for b in B_GRID:
        sizes = rng.choice(released, size=b, replace=True)
        starts = np.concatenate([[0], np.cumsum(sizes)])
        seps, gs, ts = [], [], []
        for _ in range(REALISATIONS):
            fg = gen("gaussian", sizes, R_GAUSS, rng)
            ft = gen("t", sizes, r_t, rng)
            glo, ghi = boot_ci(fg, sizes, starts, TEST_AT, rng)
            tlo, thi = boot_ci(ft, sizes, starts, TEST_AT, rng)
            seps.append((ghi < tlo) or (thi < glo))
            gs.append((rho_hat_flat(fg, sizes, starts, TEST_AT), glo, ghi))
            ts.append((rho_hat_flat(ft, sizes, starts, TEST_AT), tlo, thi))
        sep = float(np.mean(seps))
        gm = np.mean(gs, axis=0)
        tm = np.mean(ts, axis=0)
        print(f"  {b:>7}  {int(sizes.sum()):>8}  {gm[0]:>7.4f} [{gm[1]:.4f},{gm[2]:.4f}]  "
              f"{tm[0]:>7.4f} [{tm[1]:.4f},{tm[2]:.4f}]  {sep:>5.2f}")
        rows[b] = {"n": int(sizes.sum()), "sep_frac": sep,
                   "gauss": {"pt": float(gm[0]), "ci_lo": float(gm[1]), "ci_hi": float(gm[2])},
                   "t3": {"pt": float(tm[0]), "ci_lo": float(tm[1]), "ci_hi": float(tm[2])}}

    passing = [b for b in B_GRID if rows[b]["sep_frac"] >= BAR]
    b_star = min(passing) if passing else None

    print("\n" + "=" * 78)
    if b_star is None:
        print(f"  No b in {B_GRID} reaches separation {BAR:.2f}. "
              f"Best: {max(rows[b]['sep_frac'] for b in B_GRID):.2f} at "
              f"b = {max(B_GRID, key=lambda b: rows[b]['sep_frac'])}.")
        print("  -> the requirement is ABOVE this grid; E2 must budget accordingly or E3's")
        print("     tail question is out of reach at any realistic generation cost.")
    else:
        print(f"  CLUSTER BUDGET: b >= {b_star} clusters (n ~ {rows[b_star]['n']:,}) to separate")
        print(f"  a design-effect floor from a decay at p = {TEST_AT}, at the released m_tilde.")
        print(f"  The released artifact has b = 500 — short by {b_star / 500:.1f}x.")
    print("=" * 78)

    out = HERE / "result_p5b.json"
    out.write_text(json.dumps({
        "meta": {"b_grid": list(B_GRID), "boot": BOOT, "realisations": REALISATIONS,
                 "bar": BAR, "test_at": TEST_AT, "matched_at": MATCH_AT,
                 "r_gauss": R_GAUSS, "r_t": r_t, "lambda_U_t": lambda_U_t(r_t),
                 "exact_gauss": exact_g, "exact_t": exact_t, "m_tilde": m_til_rel,
                 "seed": SEED},
        "preconditions": {"p1_estimator_identical": bool(p1)},
        "rows": {str(k): v for k, v in rows.items()},
        "b_star": b_star,
    }, indent=2))
    print(f"\nwrote {out.name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
