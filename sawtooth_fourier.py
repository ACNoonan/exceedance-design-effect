"""The sawtooth term is exponentially small, not merely o(1/n).

Round 1 (sawtooth_integral.py) failed its own quadrature precondition: the
trapezoidal value halved with every refinement, the signature of O(h) error on a
discontinuous integrand, so its exponent was meaningless. Diagnosing that gives
the real answer.

Centre t = t* + s and put u = -n s. Then

    I_saw = (1/n) * int g(u) Q_1(u) du ,   g(u) = phi(u/sigma_b)/sigma_b

and Q_1(u) = -sum_{j>=1} sin(2 pi j u)/(pi j). Each Fourier mode integrates
against a GAUSSIAN envelope of width sigma_b ~ sqrt(n):

    int (1/sigma) phi(u/sigma) e^{2 pi i j u} du  =  exp(-2 pi^2 j^2 sigma^2)

so the sawtooth's entire contribution is bounded by exp(-2 pi^2 sigma_b^2) with
sigma_b^2 = O(n). That is not an oscillatory-integral estimate buying one power
of n -- it is exponential decay, and it is the classical reason the lattice
correction is invisible to smooth functionals.

PRECONDITIONS:
  R1  Richardson: the direct quadrature must extrapolate to 0 as h -> 0,
      confirming round 1 measured only its own error.
  R2  the analytic bound exp(-2 pi^2 sigma_b^2) must be below double precision
      at every n tested -- i.e. the term cannot matter at any size we simulate.
  R3  SANITY CONTROL. The same Fourier identity applied at an ARTIFICIALLY
      NARROW envelope (sigma = 0.3, so the lattice is NOT resolved) must give a
      NON-negligible value. If the formula returns ~0 for every sigma, it is
      not measuring anything.
"""
import numpy as np
from scipy.stats import norm
from scipy.special import comb

M, Q, P_TARGET = 4, 0.30, 0.90


def sigma_b(t, b, m=M, q=Q):
    j = np.arange(m + 1)
    binom = comb(m, j) * t**j * (1 - t) ** (m - j)
    atom = np.zeros(m + 1); atom[0] = 1 - t; atom[m] = t
    w = q * atom + (1 - q) * binom
    mu = (w * j).sum()
    return np.sqrt(b * (w * (j - mu) ** 2).sum())


def direct(b, k, pts_per_period, m=M):
    """Round 1's estimator, at a given resolution."""
    n = b * m
    t0 = (k - 0.5) / n
    half = 30.0 / np.sqrt(n)
    N = int(max(pts_per_period * 2 * half * n, 20001)) | 1
    s = np.linspace(-half, half, N)
    sb = sigma_b(t0, b)
    z = (-n * s) / sb
    saw = (-n * s) - np.floor(-n * s) - 0.5
    return np.trapezoid(norm.pdf(z) * saw / sb, t0 + s)


def fourier_bound(sig, jmax=6):
    """sum_j (1/(pi j)) exp(-2 pi^2 j^2 sig^2) -- bounds |int g Q_1 du|."""
    j = np.arange(1, jmax + 1)
    return float(np.sum(np.exp(-2 * np.pi**2 * j**2 * sig**2) / (np.pi * j)))


print("=" * 78)
print("The lattice sawtooth under the integral: exponentially small")
print("=" * 78)

b0, n0 = 400, 1600
k0 = int(np.ceil((n0 + 1) * P_TARGET))
vals = [(p, direct(b0, k0, p)) for p in (16, 32, 64, 128, 256)]
print("  R1  direct quadrature vs resolution (must head to 0):")
for p, v in vals:
    print(f"        {p:>4d} pts/period -> {v:>12.4e}")
ratios = [abs(vals[i + 1][1] / vals[i][1]) for i in range(len(vals) - 1)]
r1 = all(0.35 < r < 0.65 for r in ratios) and abs(vals[-1][1]) < abs(vals[0][1]) / 8
print(f"        successive ratios {['%.2f' % r for r in ratios]} ~ 0.5 => value is O(h), true integral 0")
print(f"  R1  {'PASS' if r1 else 'FAIL'}")

print()
print(f"{'b':>6} {'n':>7} {'sigma_b':>9} {'exp bound on |int g Q1 du|':>28} {'/n':>12}")
ok2 = True
for b in (100, 200, 400, 800, 1600):
    n = b * M
    k = int(np.ceil((n + 1) * P_TARGET))
    sb = sigma_b((k - 0.5) / n, b)
    bd = fourier_bound(sb)
    ok2 &= bd < 1e-300
    print(f"{b:>6d} {n:>7d} {sb:>9.2f} {bd:>28.3e} {bd / n:>12.3e}")
print()
print(f"  R2  bound below double precision at every n                : {'PASS' if ok2 else 'FAIL'}")

narrow = fourier_bound(0.3)
r3 = narrow > 1e-6
print(f"  R3  SANITY: same formula at sigma=0.3 gives {narrow:.3e} (non-negligible) : "
      f"{'PASS' if r3 else 'FAIL'}")
print()
print("READING")
print(f"  At n=1600, sigma_b = {sigma_b((k0-0.5)/n0, b0):.1f}, so the first Fourier mode is")
print(f"  suppressed by exp(-2 pi^2 sigma_b^2) = exp(-{2*np.pi**2*sigma_b((k0-0.5)/n0,b0)**2:.3e}).")
print("  The sawtooth does not need an oscillatory-integral estimate. It is killed")
print("  by the Gaussian characteristic function at the lattice frequencies.")
