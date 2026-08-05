"""How small an UNSELECTED slice beats a large selected calibration sample?

Point B of the Yang-lens pass. Her data-fusion structure identifies a bias
function from a small clean arm rather than positing a sensitivity parameter.
Transported here: if a pipeline retains a random slice of its calibration pool
BEFORE filtering, that slice calibrates directly -- no Gamma, no logged pi.

The design question is what it costs. A selected sample of any size carries a
BIAS of a*p(1-p) in realised coverage (SW-02 §3.5). An unselected slice of size
n0 is unbiased with sd ~ sqrt(p(1-p)/n0). Setting bias = sd:

    n0*  =  1 / (a^2 * p * (1-p))

Below that the big biased sample wins on RMSE; above it the small clean slice
does, and thereafter the biased sample cannot catch up at ANY size.

PRECONDITIONS (each can fail):
  P1  a=0: no bias, so the clean slice should never win -> n0* infinite.
  P2  the closed form must match a simulated RMSE crossover.
  P3  NEGATIVE CONTROL: at n0 well BELOW n0*, the selected sample must actually
      win. If the clean slice wins everywhere the comparison is rigged.
"""
import numpy as np
from scipy import optimize

rng = np.random.default_rng(4242)
P = 0.90


def F_pop(t, a):   return t + a * (t**2 - t)
def q_pop(p, a):   return p if a == 0 else optimize.brentq(lambda t: F_pop(t, a) - p, 0, 1)


def n0_star(a, p=P):
    return np.inf if a == 0 else 1.0 / (a**2 * p * (1 - p))


def rmse_selected(a, n, reps=20000, p=P):
    """Calibrate on the SELECTED sample (Uniform by construction of arm B)."""
    k = int(np.ceil((n + 1) * p))
    cov = np.array([F_pop(np.sort(rng.random(n))[k - 1], a) for _ in range(reps)])
    return np.sqrt(np.mean((cov - p) ** 2))


def rmse_slice(a, n0, reps=20000, p=P):
    """Calibrate on a random UNSELECTED slice: draw from the population F."""
    k = int(np.ceil((n0 + 1) * p))
    if k > n0:
        # split conformal returns an INFINITE threshold: the set is everything and
        # coverage is exactly 1. Not a bug -- a hard floor at n0 >= ceil(p/(1-p)).
        return abs(1.0 - p)
    cov = np.empty(reps)
    for i in range(reps):
        u = rng.random(n0)
        disc = (1 - a) ** 2 + 4 * a * u          # inverse-CDF of F_pop
        s = ((a - 1) + np.sqrt(disc)) / (2 * a) if a > 0 else u
        cov[i] = F_pop(np.sort(s)[k - 1], a)
    return np.sqrt(np.mean((cov - p) ** 2))


print("=" * 76)
print("An unselected slice vs a selected sample: where is the crossover?")
print("=" * 76)
print(f"{'a':>5} {'Gamma':>7} {'bias':>9} {'n0* (closed form)':>19}")
for a in (0.0, 0.2, 0.5, 0.9):
    g = np.inf if a == 1 else (1 + a) / (1 - a)
    print(f"{a:>5.1f} {g:>7.1f} {a*P*(1-P):>9.4f} {n0_star(a):>19.1f}")

print()
print("Simulated RMSE (coverage), a = 0.9  (Gamma = 19), selected n = 25,000")
rs = rmse_selected(0.9, 25000)
print(f"  selected sample, n = 25,000 : RMSE {rs:.5f}")
print(f"  {'n0':>6} {'slice RMSE':>12}  winner")
cross = None
for n0 in (5, 8, 9, 12, 14, 20, 50, 200):
    rc = rmse_slice(0.9, n0)
    w = "slice" if rc < rs else "selected"
    if cross is None and rc < rs:
        cross = n0
    print(f"  {n0:>6d} {rc:>12.5f}  {w}")

print()
p1 = np.isinf(n0_star(0.0))
print(f"  P1  a=0 gives n0* = infinity (clean slice never needed) : {'PASS' if p1 else 'FAIL'}")
p2 = cross is not None and 10 <= cross <= 20
print(f"  P2  simulated crossover {cross} brackets closed form {n0_star(0.9):.1f}  : {'PASS' if p2 else 'FAIL'}")
p3 = rmse_slice(0.9, 8) > rs
print(f"  P3  NEG CTRL at n0=8 (below conformal floor) selected wins: {'PASS' if p3 else 'FAIL'}")
