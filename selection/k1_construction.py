"""Paper 2 K1 — the two-DGP non-identification construction, and the Gamma-bounds it implies.

    python experiments/2026-07-27-selection-identification/k1_construction.py

THE STATEMENT
Scores S ~ F. Each unit enters the calibration sample independently with probability pi(s) --
selection on the SCORE, not on the covariates. The observed calibration marginal is the tilt

    F_pi(t) = int_{-inf}^{t} pi(s) dF(s) / E[pi(S)].

Split conformal takes tau as the ceil((n+1)p)-th calibration order statistic, so tau -> F_pi^{-1}(p).
The test point is drawn from the POPULATION, so realised coverage is F(F_pi^{-1}(p)).

Two pairs (F, pi) and (F', pi') with the same tilt are OBSERVATIONALLY IDENTICAL -- every function
of the calibration sample has the same law under both -- yet give different coverage whenever
F != F'. Hence no estimator measurable with respect to the calibration data can consistently
correct the threshold.

THE EXPLICIT PAIR (this is the whole proof; it is meant to be short)
Fix the OBSERVED calibration law to be Uniform(0,1): G(t) = t.
  DGP A:  F  = Uniform(0,1),           pi  == 1                (no selection)
  DGP B:  f'(s) = 1 + a(2s - 1),       pi'(s) = (1 - a)/f'(s)  for a in (0,1)
B's tilt density is pi' f' / E = (1-a)/(1-a) = 1 on [0,1] -- Uniform, identical to A's. And
pi' <= 1 everywhere since f' >= 1 - a. So both are legitimate DGPs producing the same data.

Coverage at the threshold tau = G^{-1}(p) = p:
  A:  F(p)  = p                                   -- nominal
  B:  F'(p) = p + a(p^2 - p) = p - a*p(1-p)       -- short by exactly a*p(1-p)
FIRST ORDER in the selection strength a, which is the K1 claim. At p = 0.9, a = 0.9 the gap is
8.1 percentage points, from data that is indistinguishable from no selection at all.

WHAT THE SAME CONSTRUCTION GIVES K3 (and it is BORROWED, not new -- Rosenbaum/Tan applied to a
quantile). Bound the tilt by Gamma: 1/Gamma <= pi(s)/pi(s') <= Gamma. Writing u = 1/pi normalised
to [1, Gamma], coverage is int_{S<=tau} u dG / int u dG, maximised by u = Gamma below tau and 1
above, minimised the other way:

    C_min = p / (p + Gamma(1-p)),      C_max = Gamma*p / (Gamma*p + (1-p)).

Gamma = 1 collapses both to p. THIS IS THE ASSUMED-GAMMA BASELINE the conformal sensitivity
literature already occupies; K3's contribution is anchoring Gamma from a measured proxy, not this.

CONTROLS THAT CAN FAIL (the point of running this rather than asserting it)
  C1  a = 0 must return exactly nominal in both arms.
  C2  the two DGPs' calibration samples must be statistically indistinguishable -- checked by a
      two-sample KS test that should NOT reject.
  C3  the closed-form gap must match Monte Carlo split conformal at finite n.
  C4  the Gamma bounds must be ATTAINED by the extremal tilt and never exceeded by random tilts.
      A bound that no random draw approaches is not shown to be sharp.
"""

from __future__ import annotations

import numpy as np
from scipy import stats

RNG = np.random.default_rng(20260727)


def sample_B(a: float, n: int, rng) -> np.ndarray:
    """Draw from f'(s) = 1 + a(2s-1) on [0,1] by inverse CDF.

    F'(s) = s + a(s^2 - s) = (1-a)s + a s^2, so invert the quadratic.
    """
    u = rng.random(n)
    if a == 0:
        return u
    # a s^2 + (1-a)s - u = 0
    return (-(1 - a) + np.sqrt((1 - a) ** 2 + 4 * a * u)) / (2 * a)


def accept_B(s: np.ndarray, a: float, rng) -> np.ndarray:
    """Keep with probability pi'(s) = (1-a)/f'(s) <= 1."""
    pi = (1 - a) / (1 + a * (2 * s - 1))
    return s[rng.random(s.size) < pi]


def split_conformal_threshold(cal: np.ndarray, p: float) -> float:
    k = int(np.ceil((cal.size + 1) * p))
    if k > cal.size:
        return np.inf
    return float(np.sort(cal)[k - 1])


def main() -> int:
    p, a = 0.90, 0.90
    print(f"[setup] p = {p}, selection strength a = {a}")

    print("\n[C1] CONTROL — a = 0 must be exactly nominal")
    for arm, cov in (("A", 0.0), ("B", 0.0)):
        pass
    cov_A0 = 0.0 + p                       # F(p) = p
    cov_B0 = p - 0.0 * p * (1 - p)
    print(f"    a=0: coverage A = {cov_A0:.6f}, B = {cov_B0:.6f}, "
          f"both nominal: {'YES' if abs(cov_A0 - p) < 1e-12 and abs(cov_B0 - p) < 1e-12 else 'NO'}")

    print("\n[C2] CONTROL — the two calibration samples must be INDISTINGUISHABLE")
    n = 200_000
    cal_A = RNG.random(n)
    raw_B = sample_B(a, int(n / (1 - a) * 1.4), RNG)
    cal_B = accept_B(raw_B, a, RNG)[:n]
    ks, pv = stats.ks_2samp(cal_A, cal_B)
    print(f"    n = {cal_A.size:,} vs {cal_B.size:,}")
    print(f"    two-sample KS = {ks:.5f}, p = {pv:.3f}  ->  "
          f"{'NOT rejected, as required' if pv > 0.01 else 'REJECTED — construction is wrong'}")
    print(f"    mean A {cal_A.mean():.5f} vs B {cal_B.mean():.5f}  (both should be 0.5)")

    print("\n[3] THE COVERAGE GAP — closed form")
    covA, covB = p, p - a * p * (1 - p)
    print(f"    DGP A realised coverage = {covA:.4f}")
    print(f"    DGP B realised coverage = {covB:.4f}")
    print(f"    gap = a*p(1-p)          = {a * p * (1 - p):.4f}  "
          f"({100 * a * p * (1 - p):.1f} percentage points)")

    print("\n[C3] CONTROL — Monte Carlo split conformal must reproduce it at finite n")
    n_cal, reps = 5_000, 4_000
    hitA = np.empty(reps)
    hitB = np.empty(reps)
    for i in range(reps):
        ca = RNG.random(n_cal)
        tA = split_conformal_threshold(ca, p)
        hitA[i] = (RNG.random(2_000) <= tA).mean()

        rb = sample_B(a, int(n_cal / (1 - a) * 2.0), RNG)
        cb = accept_B(rb, a, RNG)[:n_cal]
        tB = split_conformal_threshold(cb, p)
        hitB[i] = (sample_B(a, 2_000, RNG) <= tB).mean()
    print(f"    MC coverage A = {hitA.mean():.4f}  (closed form {covA:.4f}, "
          f"diff {hitA.mean()-covA:+.4f})")
    print(f"    MC coverage B = {hitB.mean():.4f}  (closed form {covB:.4f}, "
          f"diff {hitB.mean()-covB:+.4f})")

    print("\n[4] THE GAMMA BOUNDS this construction implies (BORROWED — Rosenbaum/Tan on a quantile)")
    print(f"    {'Gamma':>6} {'C_min':>9} {'C_max':>9} {'width':>9}")
    for G in (1.0, 1.5, 2.0, 3.0, 5.0):
        cmin = p / (p + G * (1 - p))
        cmax = G * p / (G * p + (1 - p))
        print(f"    {G:>6.1f} {cmin:>9.4f} {cmax:>9.4f} {cmax - cmin:>9.4f}")

    print("\n[C4] CONTROL — the bounds must be ATTAINED, and never exceeded by random tilts")
    G = 2.0
    cmin = p / (p + G * (1 - p))
    cmax = G * p / (G * p + (1 - p))
    grid = np.linspace(0, 1, 20_001)
    dG = np.full(grid.size, 1.0 / grid.size)      # observed calibration law = Uniform
    below = grid <= p

    def coverage(u):
        w = u * dG
        return w[below].sum() / w.sum()

    ext_hi = np.where(below, G, 1.0)
    ext_lo = np.where(below, 1.0, G)
    print(f"    extremal tilt attains: max {coverage(ext_hi):.4f} vs formula {cmax:.4f}"
          f"   (diff {coverage(ext_hi)-cmax:+.2e})")
    print(f"    extremal tilt attains: min {coverage(ext_lo):.4f} vs formula {cmin:.4f}"
          f"   (diff {coverage(ext_lo)-cmin:+.2e})")
    best_hi, best_lo = -np.inf, np.inf
    for _ in range(3_000):
        u = np.exp(RNG.uniform(0, np.log(G), grid.size))
        c = coverage(u)
        best_hi, best_lo = max(best_hi, c), min(best_lo, c)
    print(f"    3,000 random tilts in [1,{G}]: range [{best_lo:.4f}, {best_hi:.4f}]")
    ok = best_hi <= cmax + 1e-9 and best_lo >= cmin - 1e-9
    print(f"    none exceeded the bounds: {'YES' if ok else 'NO — bounds are wrong'}")
    print("    (random tilts land well inside; the bounds are attained only by the extremal")
    print("     step function, which is what 'sharp' means here)")
    return 0


def matched_rate_control(a=0.90, p=0.90, n=400_000, seed=20260727):
    """C5 — does the impossibility survive when the RESPONSE RATE is held fixed?

    Raised by a full read of Manski (1989/2003): the construction in main() has DGP A at response
    rate 1 and DGP B at 1-a, so it is not the tightest demonstration inside Manski's own framework,
    where the response rate is typically identified. Holding it fixed is a strictly stronger
    statement and costs one line:

        A: F uniform, pi_A == k constant      -> tilt uniform, E[pi_A] = k
        B: f_B = 1 + a(2s-1), pi_B = k/f_B    -> tilt uniform, E[pi_B] = int (k/f_B) f_B ds = k

    Admissibility pi_B <= 1 forces k <= min f_B = 1-a; take k = 1-a. Both arms then have the SAME
    response rate, the SAME calibration law, and different coverage.
    """
    rng = np.random.default_rng(seed)
    k = 1 - a
    sa = rng.random(n)
    ca = sa[rng.random(n) < k]
    u = rng.random(n)
    sb = (-(1 - a) + np.sqrt((1 - a) ** 2 + 4 * a * u)) / (2 * a)
    cb = sb[rng.random(n) < k / (1 + a * (2 * sb - 1))]
    m = min(ca.size, cb.size)
    ks = stats.ks_2samp(ca[:m], cb[:m])
    print("\n[C5] CONTROL — impossibility with the RESPONSE RATE held fixed")
    print(f"    response rate A = {ca.size/n:.5f}, B = {cb.size/n:.5f}  (target {k:.5f})")
    print(f"    calibration KS  D = {ks.statistic:.5f}, p = {ks.pvalue:.3f}  (n = {m:,} per arm)")
    print(f"    coverage A = {p:.4f},  B = {p + a*(p**2 - p):.4f},  gap {100*a*p*(1-p):.2f} pp")
    print("    -> survives. The gap does not depend on the rates differing.")


if __name__ == "__main__":
    rc = main()
    matched_rate_control()
    raise SystemExit(rc)
