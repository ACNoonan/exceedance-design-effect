"""SW-02 — the O(1/b) mean-drift coefficient: derivation and test.

    python experiments/2026-07-26-sw02-exchangeability-audit/drift_coefficient.py

Runs today: uses `experiments/_conformal.py`, the research copy of `split_conformal`, which
carries `check_agrees_with_calkit()` to assert equivalence once L2 lands.

THE RESULT
----------
Coverage is exactly the k-th order statistic of the probability-transformed scores,
C = F(S_(k)) = U_(k), so

    E[C] = int_0^1 P(N(t) <= k-1) dt,   N(t) = #{i: U_i <= t} = sum_j M_j(t),

with M_j i.i.d. across the b clusters, E N(t) = n t and Var N(t) = n t(1-t) D(t),
D(t) = 1 + (m-1) rho_I(t). The design effect depends on the LEVEL t, and that is the entire
source of the drift.

Normal approximation with continuity correction, g(t) = (k - 1/2 - n t)/sigma(t); substituting
t = t* + s with t* = (k-1/2)/n and z = n s/sigma* gives g ~= -z + (sigma'/n) z^2, hence

    E[C] ~= (k-1/2)/n + (1/(2n)) d/dt[ t(1-t) D(t) ]|_{t*}.

The Edgeworth skewness term drops out because int phi(z)(z^2 - 1) dz = 0. Using
(k-1/2)/n - k/(n+1) = (p - 1/2)/n and D = 1 + (m-1) rho_I:

    E[C] - p = ((m-1)/(2n)) { p(1-p) rho_I'(p) - (2p-1) rho_I(p) } + O(n^-2)

    b * drift = ((m-1)/(2m)) { p(1-p) rho_I'(p) - (2p-1) rho_I(p) }            (*)

WHAT (*) EXPLAINS
-----------------
1. Order. Drift is O(1/n) = O(1/b) with a coefficient free of b.  [matches the measurement]
2. Sign. For p > 1/2 with rho_I > 0 and rho_I' < 0 -- the tail attenuation established in the
   level-dependence result -- BOTH terms are negative. Clustering biases coverage BELOW
   nominal: the unsafe direction. The paper's level-dependence finding is what forces the sign.
3. Vanishing under exchangeability. rho_I == 0 gives drift exactly 0, consistent with the exact
   i.i.d. Beta mean k/(n+1) = p. This is the control the estimator must pass.

ON THE RESIDUAL — a correction worth keeping
Individual rows land within ~2 SE of prediction. Do NOT attribute that scatter to the dropped
O(n^-2) term: a second-order term in the drift contributes O(1/b) to b*drift, so it must DECAY
in b. A residual flat in b is the signature of a wrong constant or of noise, not of a dropped
higher-order term. Fitting b*drift = A + B/b gives B = -0.032 +/- 0.215 (nothing detectable)
and intercept -0.1755 +/- 0.0061, 0.56 sigma from prediction; two independent implementations
bracket the prediction from opposite sides. Claim: the constant is confirmed to ~2%, and a
second-order term is neither detected nor excluded at this precision (low power -- |B| < 0.43
at 2 sigma still permits ~10% of the drift at b=25).
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from scipy.optimize import brentq
from scipy.stats import multivariate_normal, norm

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from _conformal import split_conformal  # noqa: E402

CHUNK = 20_000


def rho_I(p: float, r: float) -> float:
    """Indicator ICC at level p, equicorrelated Gaussian copula with correlation r."""
    if r >= 1.0:
        return 1.0
    if r <= 0.0:
        return 0.0
    z = norm.ppf(p)
    d = float(multivariate_normal(mean=[0, 0], cov=[[1, r], [r, 1]]).cdf([z, z]))
    return (d - p * p) / (p * (1 - p))


def rho_I_prime(p: float, r: float, h: float = 1e-4) -> float:
    """d rho_I / d p — the level-dependence slope. Negative in the upper tail."""
    return (rho_I(p + h, r) - rho_I(p - h, r)) / (2 * h)


def predicted_b_drift(p: float, m: int, r: float) -> float:
    """Equation (*). No free parameters."""
    return ((m - 1) / (2 * m)) * (
        p * (1 - p) * rho_I_prime(p, r) - (2 * p - 1) * rho_I(p, r)
    )


def solve_r_for_rho_I(target: float, p: float) -> float:
    return brentq(lambda r: rho_I(p, r) - target, 1e-6, 1 - 1e-9, xtol=1e-12)


def simulate_drift(b: int, m: int, r: float, alpha: float, reps: int, seed: int = 0):
    """Mean of C = Phi(threshold) minus p, computed exactly — no finite test set."""
    n = b * m
    k = int(np.ceil((n + 1) * (1 - alpha)))
    p = k / (n + 1)
    rng = np.random.default_rng(seed)
    tot = tot2 = 0.0
    done = 0
    while done < reps:
        c = min(CHUNK, reps - done)
        anc = rng.normal(size=(c, b, 1))
        own = rng.normal(size=(c, b, m))
        s = (np.sqrt(r) * anc + np.sqrt(1 - r) * own).reshape(c, n)
        cov = np.array([norm.cdf(split_conformal(row, alpha)) for row in s])
        tot += cov.sum()
        tot2 += (cov ** 2).sum()
        done += c
    mean = tot / reps
    sd = np.sqrt(max(tot2 / reps - mean ** 2, 0.0))
    return mean - p, sd / np.sqrt(reps), p


def main() -> int:
    P, M, ALPHA = 0.9, 4, 0.10
    R = solve_r_for_rho_I(0.5, P)

    print(f"\n[0] CONFIG  p={P}, m={M}, rho_I=0.5  ->  Gaussian r={R:.4f}")
    print(f"    rho_I(p)  = {rho_I(P, R):+.6f}")
    print(f"    rho_I'(p) = {rho_I_prime(P, R):+.6f}  <- level-dependence slope, negative")
    print(f"    predicted b*drift from (*) = {predicted_b_drift(P, M, R):+.4f}")
    print(f"      term  -(2p-1) rho_I  = {-(2*P-1)*rho_I(P, R):+.4f}   (dominant)")
    print(f"      term  p(1-p) rho_I'  = {P*(1-P)*rho_I_prime(P, R):+.4f}")

    print("\n[1] IS b*drift FLAT, AND AT THE PREDICTED VALUE?")
    print(f"{'b':>5} {'n':>6} {'drift':>10} {'SE':>9} {'b*drift':>9} {'pred':>9} {'sigma':>7}")
    for b in (25, 50, 100, 200):
        reps = 400_000 if b <= 50 else 200_000
        d, se, p_eff = simulate_drift(b, M, R, ALPHA, reps)
        pr = predicted_b_drift(p_eff, M, R)
        print(f"{b:>5} {b*M:>6} {d:>+10.5f} {se:>9.5f} {d*b:>+9.4f} {pr:>+9.4f} "
              f"{(d*b - pr)/(se*b):>+7.2f}")

    print("\n[2] FALSIFICATION — (*) at other (m, 1-alpha, rho_I). A fit would not travel.")
    print(f"{'m':>3} {'1-alpha':>8} {'rho_I':>7} {'b*drift':>9} {'pred':>9} {'sigma':>7}")
    for m_, a_, ri_ in [(4, 0.10, 0.25), (8, 0.10, 0.50), (4, 0.05, 0.50), (2, 0.10, 0.60)]:
        n_tmp = 50 * m_
        p_ = int(np.ceil((n_tmp + 1) * (1 - a_))) / (n_tmp + 1)
        r_ = solve_r_for_rho_I(ri_, p_)
        d, se, p_eff = simulate_drift(50, m_, r_, a_, 400_000)
        pr = predicted_b_drift(p_eff, m_, r_)
        print(f"{m_:>3} {1-a_:>8.2f} {ri_:>7.2f} {d*50:>+9.4f} {pr:>+9.4f} "
              f"{(d*50 - pr)/(se*50):>+7.2f}")

    print("\n[3] CONTROL — exchangeable (rho_I=0). (*) says drift is exactly zero.")
    for b in (25, 200):
        d, se, _ = simulate_drift(b, M, 0.0, ALPHA, 400_000)
        print(f"    b={b:>4}  drift={d:>+.6f}  SE={se:.6f}  ({abs(d)/se:.1f} sigma from 0)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
