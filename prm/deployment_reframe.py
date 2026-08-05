"""SW-02 — the deployment reframe (2) and the un-clustered negative control (3).

    python experiments/2026-07-26-sw02-exchangeability-audit/deployment_reframe.py

WHY THIS EXISTS
The standing objection to this paper is that its effect is invisible in the statistic the field
reports and therefore has no consequence: "everyone averages coverage, the average barely moves,
so nothing is wrong." Two measurements on the released PRM set answer it, and they only mean
anything as a pair.

  (2) THE DEPLOYMENT REFRAME. Mean coverage is an average over calibration draws to which no user
      is exposed — each deployment gets ONE draw. So the quantity carrying consequences is the
      fraction of deployments landing below the level that was promised. That is not a metric
      invented here; it is the promise being broken, counted. Measured end to end from the
      cluster bootstrap and never plugged in from sqrt(DEFF), which is SW-24's lesson.

  (3) THE NEGATIVE CONTROL. All of (2) is worthless if the harness manufactures dispersion. So
      the same release, the same operating rule and the SAME code path are run with the
      clustering removed by construction: one prefix per question, 500 genuinely independent
      units, no shared ancestry, every cluster of size 1. If clustering is what inflates
      dispersion, this arm MUST return 1.0x and MUST match the i.i.d. Beta law in absolute terms.

WHAT WOULD FALSIFY THE PAIR — stated before the run, and reported whatever it says
  - singleton arm inflates       -> the harness generates dispersion; (2) is void.
  - clustered arm does not       -> the effect is not in this release; (2) is void.
  - singleton sd != Beta sd      -> the reference law is wrong on this substrate, and every
                                    "wider than i.i.d. implies" statement loses its reference.

SCOPE — inherited from prm_dispersion.py and not re-argued here
  Clusters are QUESTIONS (a lower bound on family correlation); `success_prob` is the calibrated
  TARGET rather than the unreleased nonconformity score; tie-breaking jitter is required because
  the raw score has 9 atoms and violates (A2). Every number below is "measured on this release",
  not "a property of that system".
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
from scipy.stats import beta as beta_dist

sys.path.insert(0, str(Path(__file__).resolve().parent))
from prm_dispersion import (  # noqa: E402
    ATOM_SPACING, JITTER, _flatten, coverage_dist, operating_level, plugin_ratio,
)
from prm_measurement import load, size_profile  # noqa: E402

SEED = 20260731
REPS = 4000
N_SINGLETON_DRAWS = 3      # which prefix is kept is a choice; average over it
SHORTFALLS = (0.005, 0.010, 0.020, 0.030)


def beta_law(n: int, level: float):
    """The i.i.d. reference: realised coverage of the k-th order statistic is Beta(k, n+1-k)."""
    k = min(max(int(math.ceil((n + 1) * level)), 1), n)
    return beta_dist(k, n + 1 - k)


def singleton_population(fams, rng):
    """One prefix per question: 500 units with no shared ancestry, drawn from the real release."""
    return np.array([f[rng.integers(0, len(f))] for f in fams], dtype=float)


def main() -> int:
    rng = np.random.default_rng(SEED)
    fams = load()
    scores, sizes, starts = _flatten(fams)
    n, b = len(scores), len(sizes)
    _, m_bar, m_til = size_profile(fams)
    t_star, level = operating_level(scores)
    jit = scores + rng.random(n) * JITTER

    print("=" * 78)
    print("PRECONDITIONS — a failure in any one invalidates every number below")
    print("=" * 78)
    ok = True

    p0 = (n == 25028 and b == 500)
    print(f"  P0 release composition: n = {n} (25028), b = {b} (500), "
          f"m_bar {m_bar:.2f}, m_tilde {m_til:.2f}  -> {'PASS' if p0 else 'FAIL'}")
    print("     would fail if: the cached release changed, or families were keyed differently.")
    ok &= p0

    p1 = JITTER < ATOM_SPACING
    print(f"  P1 jitter {JITTER} < atom spacing {ATOM_SPACING}  -> {'PASS' if p1 else 'FAIL'}")
    print("     would fail if: jitter could move a score past the next atom, changing the CDF")
    print("     rather than merely breaking ties inside it.")
    ok &= p1

    c = coverage_dist(jit, starts, sizes, level, "CLUSTER", rng, reps=REPS)
    i = coverage_dist(jit, starts, sizes, level, "IID", rng, reps=REPS)
    infl = c.std(ddof=1) / i.std(ddof=1)
    p2 = 4.2 < infl < 4.7
    print(f"  P2 POSITIVE control — clustered/i.i.d. sd ratio = {infl:.2f} "
          f"(published 4.46)  -> {'PASS' if p2 else 'FAIL'}")
    print("     would fail if: the effect is not in this release, or the harness drifted from")
    print("     the one that produced the published figure. Without this the negative control")
    print("     below is uninformative — a harness that inflates NOTHING would also pass it.")
    ok &= p2

    if not ok:
        print("\n  A PRECONDITION FAILED. No number below may be quoted.")
        return 1
    print("  all pass.\n")

    # ---------------------------------------------------------------- (3) negative control
    print("=" * 78)
    print("[3] NEGATIVE CONTROL — clustering removed by construction, same code path")
    print("=" * 78)
    print(f"    {'draw':<8}{'n':>6}{'level':>9}{'measured sd':>13}{'Beta sd':>10}"
          f"{'meas/Beta':>11}{'clust/iid':>11}")
    ratios_beta, ratios_arm = [], []
    for d in range(N_SINGLETON_DRAWS):
        s = singleton_population(fams, rng)
        s = s + rng.random(len(s)) * JITTER
        s_sizes = np.ones(len(s), dtype=int)
        s_starts = np.arange(len(s) + 1)
        _, lvl_s = operating_level(s)
        cs = coverage_dist(s, s_starts, s_sizes, lvl_s, "CLUSTER", rng, reps=REPS)
        is_ = coverage_dist(s, s_starts, s_sizes, lvl_s, "IID", rng, reps=REPS)
        bsd = beta_law(len(s), lvl_s).std()
        r_beta, r_arm = cs.std(ddof=1) / bsd, cs.std(ddof=1) / is_.std(ddof=1)
        ratios_beta.append(r_beta), ratios_arm.append(r_arm)
        print(f"    {d + 1:<8}{len(s):>6}{lvl_s:>9.4f}{cs.std(ddof=1):>13.5f}"
              f"{bsd:>10.5f}{r_beta:>11.3f}{r_arm:>11.3f}")
    rb, ra = float(np.mean(ratios_beta)), float(np.mean(ratios_arm))
    p3 = 0.90 < rb < 1.10 and 0.95 < ra < 1.05
    print(f"\n    mean measured/Beta = {rb:.3f}, mean clustered-arm/i.i.d.-arm = {ra:.3f}"
          f"   -> {'PASS' if p3 else 'FAIL'}")
    print("    Same 500 questions, same operating rule, same coverage_dist() call — the only")
    print("    change is that each family now holds one prefix instead of 8-135.")
    print(f"    The identical harness returns {infl:.2f}x on the clustered release and "
          f"{ra:.2f}x here.")
    if not p3:
        print("\n    NEGATIVE CONTROL FAILED — the harness inflates dispersion on independent")
        print("    units, so section [2] below is measuring the instrument. Do not quote it.")
        return 1

    # ---------------------------------------------------------------- (2) deployment reframe
    print()
    print("=" * 78)
    print("[2] DEPLOYMENT REFRAME — what one draw looks like, not what the average looks like")
    print("=" * 78)
    plug, rho, _, p_ach = plugin_ratio(jit, starts, sizes, level=level)
    print(f"    operating point: threshold nearest {level:.4f}; rho_I {rho:.4f}, "
          f"m_tilde {m_til:.2f}, plug-in sqrt(DEFF) {plug:.2f} vs measured {infl:.2f}")
    print()
    print(f"    {'':32s}{'worst 1 in 100':>16}{'typical':>10}{'best 1 in 100':>16}")
    for lbl, arm in (("what exchangeability implies", i), ("what the release delivers", c)):
        print(f"    {lbl:32s}{np.percentile(arm, 1):>15.1%}{np.percentile(arm, 50):>10.1%}"
              f"{np.percentile(arm, 99):>15.1%}")
    print(f"    {'mean coverage':32s}{'':>15}{i.mean():>10.4f} / {c.mean():.4f}"
          f"   <- the statistic papers report")
    print()
    print("    Deployments per 1,000 landing short of the level they were calibrated to:")
    print(f"    {'shortfall':>12}{'threshold':>12}{'exchangeable':>15}{'delivered':>12}")
    for d in SHORTFALLS:
        thr = level - d
        print(f"    {d:>11.1%}{thr:>12.4f}{1000 * (i < thr).mean():>15.1f}"
              f"{1000 * (c < thr).mean():>12.1f}")
    print()
    print("    Both columns come from the same 4,000-replicate bootstrap over the same 500")
    print("    released questions. The only difference is whether prefixes are resampled with")
    print("    their question (delivered) or independently (exchangeable).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
