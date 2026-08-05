"""SW-02 — independent check of the drift-coefficient prediction and its residual.

Not a re-derivation. The proposition is:

    b * drift  ->  (m-1)/(2m) * [ p(1-p) * rho_I'(p)  -  (2p-1) * rho_I(p) ]

and its author reports measured drift sitting "consistently 1-2 sigma above prediction",
attributed to the dropped O(n^-2) term and written into the paper as a stated limitation.

A limitation that isn't real is its own kind of error, so this checks it from a separate
implementation (`experiments/_conformal.py`, coverage computed exactly as Phi(threshold),
different RNG stream) and asks two questions the author cannot easily ask from inside their
own code path:

  Q1. Does the pooled estimate of b*drift agree with prediction, and with what error bar?
  Q2. Is there a residual b-DEPENDENCE? If a second-order term exists then
          b*drift = A + B/b
      so regressing b*drift on 1/b gives slope B != 0. A constant offset with no slope is
      not evidence of an O(n^-2) term; it is a disagreement about A.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from scipy.optimize import brentq
from scipy.stats import norm
from scipy.stats import multivariate_normal as mvn

# calkit/ and _conformal.py sit at the code-archive root; in the paper's working
# tree they are vendored under external/. Cover both layouts.
_HERE = Path(__file__).resolve().parent
for _p in (_HERE.parent / "external", _HERE.parent, _HERE / "external", _HERE):
    sys.path.insert(0, str(_p))
from _conformal import nominal_rank_coverage, split_conformal  # noqa: E402

M, ALPHA = 4, 0.10
P = 1 - ALPHA
TARGET_RHO_I = 0.5


def rho_I(p: float, r: float) -> float:
    z = norm.ppf(p)
    d = float(mvn(mean=[0, 0], cov=[[1, r], [r, 1]]).cdf([z, z]))
    return (d - p * p) / (p * (1 - p))


def rho_I_prime(p: float, r: float, h: float = 1e-4) -> float:
    """d/dp at FIXED dependence structure r."""
    return (rho_I(p + h, r) - rho_I(p - h, r)) / (2 * h)


def predicted_coefficient(p: float, m: int, r: float) -> tuple[float, float, float]:
    ri, rip = rho_I(p, r), rho_I_prime(p, r)
    pre = (m - 1) / (2 * m)
    term_prime = p * (1 - p) * rip
    term_level = -(2 * p - 1) * ri
    return pre * (term_prime + term_level), term_prime, term_level


def coverage_sample(b: int, r: float, reps: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    cov = np.full((M, M), r)
    np.fill_diagonal(cov, 1.0)
    L = np.linalg.cholesky(cov)
    out = np.empty(reps)
    for i in range(reps):
        x = (rng.normal(size=(b, M)) @ L.T).ravel()
        out[i] = norm.cdf(split_conformal(x, ALPHA))
    return out


def main() -> int:
    r = brentq(lambda rr: rho_I(P, rr) - TARGET_RHO_I, 1e-9, 0.99999)
    coef, t_prime, t_level = predicted_coefficient(P, M, r)
    ri, rip = rho_I(P, r), rho_I_prime(P, r)
    print(f"p={P}  m={M}  gaussian r={r:.4f}")
    print(f"rho_I={ri:.4f}   rho_I'={rip:.4f}   (author states -0.657)")
    print(f"prefactor (m-1)/2m = {(M-1)/(2*M):.4f}")
    print(f"  p(1-p)*rho_I'      = {t_prime:+.4f}   (author: -0.059)")
    print(f"  -(2p-1)*rho_I      = {t_level:+.4f}   (author: -0.400)")
    print(f"PREDICTED COEFFICIENT = {coef:+.4f}   (author: -0.1722)\n")

    # More reps at larger b, where the drift itself is small.
    plan = [(25, 60_000), (50, 60_000), (100, 80_000), (200, 120_000), (400, 200_000)]
    print(f"{'b':>5} {'reps':>8} {'drift':>11} {'SE':>9} {'b*drift':>10} {'SE':>8} {'z vs pred':>10}")
    bs, y, sy = [], [], []
    for b, reps in plan:
        c = coverage_sample(b, r, reps, seed=1000 + b)
        n = b * M
        d = c.mean() - nominal_rank_coverage(n, ALPHA)
        se = c.std() / np.sqrt(reps)
        bs.append(b); y.append(d * b); sy.append(se * b)
        print(f"{b:>5} {reps:>8} {d:>+11.6f} {se:>9.6f} {d*b:>+10.4f} {se*b:>8.4f} "
              f"{(d*b - coef)/(se*b):>+10.2f}")

    bs, y, sy = np.array(bs, float), np.array(y), np.array(sy)
    w = 1.0 / sy**2

    # Q1 — pooled constant
    A = float(np.sum(w * y) / np.sum(w))
    seA = float(1.0 / np.sqrt(np.sum(w)))
    print(f"\nQ1  pooled b*drift = {A:+.4f} +/- {seA:.4f}"
          f"   vs predicted {coef:+.4f}   ->  {abs(A-coef)/seA:.2f} sigma")

    # Q2 — weighted linear fit of b*drift on 1/b : intercept A, slope B
    x = 1.0 / bs
    Sw, Sx, Sy = w.sum(), (w*x).sum(), (w*y).sum()
    Sxx, Sxy = (w*x*x).sum(), (w*x*y).sum()
    det = Sw*Sxx - Sx*Sx
    B = (Sw*Sxy - Sx*Sy) / det
    A2 = (Sxx*Sy - Sx*Sxy) / det
    seB = float(np.sqrt(Sw/det))
    seA2 = float(np.sqrt(Sxx/det))
    print(f"Q2  fit b*drift = A + B/b :  A={A2:+.4f}+/-{seA2:.4f}   B={B:+.3f}+/-{seB:.3f}")
    print(f"    slope significance = {abs(B)/seB:.2f} sigma  -> "
          f"{'second-order term DETECTED' if abs(B) > 2*seB else 'NO detectable O(1/b^2) term'}")
    print(f"    intercept vs prediction = {abs(A2-coef)/seA2:.2f} sigma")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
