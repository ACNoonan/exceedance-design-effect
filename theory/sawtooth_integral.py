"""SW-12, the last piece: does Esseen's lattice sawtooth integrate away?

After the skewness term is handled (edgeworth_terms.py: O(n^-2) on two models,
with a control showing the orthogonality is load-bearing), the only term left
between Proposition 1 and a proof is Esseen's discontinuous correction.

Esseen (1945) Thm 4 / Kolassa-McCullagh (1990) quoting Bhattacharya-Rao p.238:
for a lattice sum the CDF carries, beyond the Edgeworth polynomials, a periodic
term built from Q_1(x) = x - floor(x) - 1/2. Pointwise it is O(b^-1/2) -- the
same order as the skewness term, hence the same O(1/n) threat after integration.

THE MECHANISM TO TEST. Its argument is (k - 1/2 - n t), which sweeps one full
period every 1/n in t, while the envelope phi(z(t)) varies on the scale of the
transition window, width O(n^-1/2). So the sawtooth completes ~sqrt(n) periods
inside the one region where the envelope is non-negligible: a fast mean-zero
oscillation against a slow envelope, which integrates to far less than its
amplitude. Predicted o(1/n).

NUMERICS. Centring t = t* + s makes the argument exactly -n*s, avoiding the
catastrophic cancellation in (k - 1/2 - n t) at large n.

PRECONDITIONS (each can come out wrong):
  P1  Q_1 is mean zero over a period, and is exactly 0 at half-integers -- the
      property the continuity correction exploits.
  P2  QUADRATURE CONTROL. Refining the grid must not move I_saw. An oscillatory
      integrand is exactly where a quadrature reports its own error as signal,
      so this gates everything below.
  P3  I_saw must scale faster than n^-1.
  P4  DECISIVE NEGATIVE CONTROL. Replace Q_1 by its amplitude (a constant 1/2,
      same size, no oscillation). That must come out O(n^-1) -- the threat we
      are claiming the oscillation removes. If both scale alike, the mechanism
      is not oscillation and the argument is wrong.
"""
import numpy as np
from scipy.stats import norm
from scipy.special import comb

M, Q, P_TARGET = 4, 0.30, 0.90


def moments(t, m=M, q=Q):
    j = np.arange(m + 1)
    binom = comb(m, j) * t**j * (1 - t) ** (m - j)
    atom = np.zeros(m + 1); atom[0] = 1 - t; atom[m] = t
    w = q * atom + (1 - q) * binom
    mu = (w * j).sum()
    c2 = (w * (j - mu) ** 2).sum()
    return mu, c2


def Q1(y):
    """Esseen's sawtooth: y - floor(y) - 1/2. Mean zero, period 1."""
    return y - np.floor(y) - 0.5


def I_sawtooth(b, k, oscillate=True, m=M, pts_per_period=64):
    n = b * m
    t0 = (k - 0.5) / n
    half = 30.0 / np.sqrt(n)                       # window, >> O(n^-1/2)
    nper = 2 * half * n                            # periods inside the window
    N = int(max(pts_per_period * nper, 20001)) | 1
    s = np.linspace(-half, half, N)                # centred: arg = -n*s exactly
    ts = t0 + s
    ok = (ts > 1e-9) & (ts < 1 - 1e-9)
    ts, s = ts[ok], s[ok]
    vals = np.empty(ts.size)
    for i, t in enumerate(ts):
        mu, c2 = moments(t, m)
        sb = np.sqrt(b * c2)
        z = (k - 0.5 - b * mu) / sb
        saw = Q1(-n * s[i]) if oscillate else 0.5
        vals[i] = norm.pdf(z) * saw / sb
    return np.trapezoid(vals, ts), int(nper), N


print("=" * 80)
print("SW-12 last piece: Esseen's sawtooth term under the integral")
print("=" * 80)

y = np.array([0.5, 1.5, 2.5, -0.5, 7.5])
p1a = np.allclose(Q1(y), 0.0)
grid = np.linspace(0, 1, 1_000_001)[:-1]
p1b = abs(np.trapezoid(Q1(grid), grid)) < 1e-6
print(f"  P1  Q_1 vanishes at half-integers, mean zero over a period : "
      f"{'PASS' if (p1a and p1b) else 'FAIL'}")

# P2 -- quadrature refinement
b0, n0 = 400, 1600
k0 = int(np.ceil((n0 + 1) * P_TARGET))
ref = [I_sawtooth(b0, k0, True, pts_per_period=p)[0] for p in (32, 64, 128)]
scale = abs(ref[1]) if abs(ref[1]) > 0 else 1.0
p2 = max(abs(ref[i] - ref[-1]) for i in range(2)) < 0.05 * max(scale, 1e-12)
print(f"  P2  refinement 32/64/128 pts-per-period: {ref[0]:.3e} {ref[1]:.3e} "
      f"{ref[2]:.3e}  : {'PASS' if p2 else 'FAIL'}")

print()
print(f"{'b':>6} {'n':>7} {'periods':>8} {'I_saw':>13} {'I_const(ctl)':>14} {'drift':>12}")
rows = []
for b in (100, 200, 400, 800, 1600):
    n = b * M
    k = int(np.ceil((n + 1) * P_TARGET))
    Is, nper, _ = I_sawtooth(b, k, True)
    Ic, _, _ = I_sawtooth(b, k, False)
    d = (M - 1) / (2.0 * n) * (-(2 * P_TARGET - 1) * Q)
    rows.append((n, Is, Ic, d))
    print(f"{b:>6d} {n:>7d} {nper:>8d} {Is:>13.3e} {Ic:>14.3e} {d:>12.3e}")

lg = lambda a: np.log(np.abs(np.array(a)))
ns = np.array([r[0] for r in rows], float)
e_s = np.polyfit(np.log(ns), lg([r[1] for r in rows]), 1)[0]
e_c = np.polyfit(np.log(ns), lg([r[2] for r in rows]), 1)[0]
print()
print(f"  fitted exponent, I_saw  (oscillating) : n^{e_s:+.2f}")
print(f"  fitted exponent, I_const (control)    : n^{e_c:+.2f}")
print()
p3 = e_s < -1.4
print(f"  P3  I_saw scales faster than n^-1 (fit {e_s:+.2f} < -1.4)     : {'PASS' if p3 else 'FAIL'}")
p4 = (-1.4 < e_c < -0.6) and (e_s < e_c - 0.4)
print(f"  P4  NEG CTRL: constant-amplitude is n^-1 (fit {e_c:+.2f})      : {'PASS' if p4 else 'FAIL'}")
r = max(abs(x[1] / x[3]) for x in rows)
print(f"  P5  |I_saw| stays below 5% of the drift (max {r:.3%})        : {'PASS' if r < 0.05 else 'FAIL'}")
