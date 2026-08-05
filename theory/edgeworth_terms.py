"""SW-12: which analytic term makes Proposition 1's remainder O(n^-2)?

Proposition 1's proof is a formal expansion. §10 calls it a well-tested
conjecture because the Edgeworth/lattice step is argued, not proved. The
argument's load-bearing claim is that the leading Edgeworth SKEWNESS correction
integrates to zero over t. This script tests that claim directly, which is
different from testing Proposition 1's total (already done in prop1_exact.py).

WHY IT MATTERS. E[C] = int_0^1 P(N(t) <= k-1) dt, and the integrand turns over a
window of width O(n^-1/2). A pointwise error eps contributes ~ eps * n^-1/2. The
Edgeworth skewness term is pointwise O(b^-1/2), so it contributes O(1/n) --
EXACTLY the size of the drift being computed. Proposition 1 is therefore correct
only if that term integrates away rather than merely being small.

THE MECHANISM. With z(t) = (k - 1/2 - n t)/sigma_b(t) and dt ~ -(sigma_b/n) dz,

    int skew dt  ~  -(gamma1/6)(sigma_b/n) int phi(z)(z^2 - 1) dz  =  0

since int phi (z^2-1) dz = 0 -- He_2 is orthogonal to the Gaussian weight. What
survives is the t-dependence of gamma1 and sigma, one order down: O(n^-2).

PRECONDITIONS (each can come out wrong):
  P1  moments: at q=0 the cluster law is Binomial(m,t); sigma^2 and kappa_3 from
      the pmf must match the closed forms. Validates the moment pipeline.
  P2  I_skew must scale as n^-2. Fitted exponent near -2, not -1.
  P3  DECISIVE NEGATIVE CONTROL. Drop the (z^2-1) factor and integrate
      phi(z)*gamma1/6 alone. That has no orthogonality and MUST come out O(n^-1)
      -- same order as the drift. If both scale alike, the orthogonality
      argument is doing no work and the mechanism is not what we claim.
  P4  I_skew must be far below the drift itself at every n.
"""
import numpy as np
from scipy.stats import norm
from scipy.special import comb

M, Q, P_TARGET = 4, 0.30, 0.90


def pmf_atom(t, m=M, q=Q):
    """P(X=j): w.p. q all m share one draw, else m iid Bernoulli(t)."""
    j = np.arange(m + 1)
    binom = comb(m, j) * t**j * (1 - t) ** (m - j)
    atom = np.zeros(m + 1); atom[0] = 1 - t; atom[m] = t
    return q * atom + (1 - q) * binom


def moments(t, m=M, q=Q):
    j = np.arange(m + 1); w = pmf_atom(t, m, q)
    mu = (w * j).sum()
    c2 = (w * (j - mu) ** 2).sum()
    c3 = (w * (j - mu) ** 3).sum()
    return mu, c2, c3


def terms(t, b, k, m=M, q=Q):
    mu, c2, c3 = moments(t, m, q)
    sb = np.sqrt(b * c2)
    z = (k - 0.5 - b * mu) / sb
    g1 = c3 / (np.sqrt(b) * c2**1.5)          # skewness of the b-fold sum
    return z, g1


def integrate(b, k, with_He2=True, m=M, q=Q, N=200001):
    """int over t of the Edgeworth skewness term (or of phi*gamma1/6 alone)."""
    n = b * m
    t0 = (k - 0.5) / n
    half = 40.0 / np.sqrt(n)                   # window >> O(n^-1/2)
    ts = np.linspace(max(t0 - half, 1e-9), min(t0 + half, 1 - 1e-9), N)
    vals = np.empty(N)
    for i, t in enumerate(ts):
        z, g1 = terms(t, b, k, m, q)
        f = (z * z - 1.0) if with_He2 else 1.0
        vals[i] = -norm.pdf(z) * (g1 / 6.0) * f
    return np.trapezoid(vals, ts)


def prop1_drift(b, m=M, q=Q, p=P_TARGET):
    """(m-1)/(2n) * {p(1-p) rho_I' - (2p-1) rho_I}; rho_I = q, rho_I' = 0."""
    n = b * m
    return (m - 1) / (2.0 * n) * (-(2 * p - 1) * q)


print("=" * 78)
print("SW-12: does the Edgeworth skewness term integrate away?")
print("=" * 78)

# P1 -- moment pipeline against Binomial closed forms at q=0
t = 0.37
mu, c2, c3 = moments(t, q=0.0)
ok1 = (abs(mu - M * t) < 1e-12 and abs(c2 - M * t * (1 - t)) < 1e-12
       and abs(c3 - M * t * (1 - t) * (1 - 2 * t)) < 1e-12)
print(f"  P1  q=0 moments match Binomial(m,t): mu {mu:.6f}, var {c2:.6f}, k3 {c3:.6f} : "
      f"{'PASS' if ok1 else 'FAIL'}")

print()
print(f"{'b':>6} {'n':>7} {'drift(P1)':>12} {'I_skew':>13} {'I_noHe2':>13} "
      f"{'|I_skew/drift|':>15}")
rows = []
for b in (100, 200, 400, 800, 1600):
    n = b * M
    k = int(np.ceil((n + 1) * P_TARGET))
    Is = integrate(b, k, True)
    In = integrate(b, k, False)
    d = prop1_drift(b)
    rows.append((n, Is, In, d))
    print(f"{b:>6d} {n:>7d} {d:>12.3e} {Is:>13.3e} {In:>13.3e} {abs(Is/d):>15.4f}")

lg = lambda a: np.log(np.abs(np.array(a)))
ns = np.array([r[0] for r in rows], float)
e_sk = np.polyfit(np.log(ns), lg([r[1] for r in rows]), 1)[0]
e_no = np.polyfit(np.log(ns), lg([r[2] for r in rows]), 1)[0]

print()
print(f"  fitted exponent, I_skew  (with He_2) : n^{e_sk:+.2f}")
print(f"  fitted exponent, I_noHe2 (control)   : n^{e_no:+.2f}")
print()
p2 = e_sk < -1.6
print(f"  P2  I_skew scales as n^-2 (fit {e_sk:+.2f} < -1.6)             : {'PASS' if p2 else 'FAIL'}")
p3 = e_no > -1.4 and (e_sk < e_no - 0.5)
print(f"  P3  NEG CTRL: control is n^-1 (fit {e_no:+.2f}) and separated   : {'PASS' if p3 else 'FAIL'}")
p4 = all(abs(r[1] / r[3]) < 0.05 for r in rows)
print(f"  P4  |I_skew| < 5% of the drift at every n                  : {'PASS' if p4 else 'FAIL'}")


# ============================================================================
# The one-factor Gaussian model: rho_I' != 0, so BOTH terms of Proposition 1
# are live. §10 records that the O(n^-2) evidence "is checked for one dependence
# model, and the model with rho_I' = 0, so it does not cover the derivative
# term." This section covers it.
# ============================================================================
import prop1_exact as PE

RHO = 0.40


def moments_gauss(t, m=M, rho=RHO):
    w = PE.cluster_pmf_gauss(np.array([t]), m, rho)[0]
    j = np.arange(m + 1)
    mu = (w * j).sum()
    c2 = (w * (j - mu) ** 2).sum()
    c3 = (w * (j - mu) ** 3).sum()
    return mu, c2, c3


def integrate_gauss(b, k, with_He2=True, m=M, rho=RHO, N=4001):
    n = b * m
    t0 = (k - 0.5) / n
    half = 40.0 / np.sqrt(n)
    ts = np.linspace(max(t0 - half, 1e-9), min(t0 + half, 1 - 1e-9), N)
    vals = np.empty(N)
    for i, t in enumerate(ts):
        mu, c2, c3 = moments_gauss(t, m, rho)
        sb = np.sqrt(b * c2)
        z = (k - 0.5 - b * mu) / sb
        g1 = c3 / (np.sqrt(b) * c2 ** 1.5)
        f = (z * z - 1.0) if with_He2 else 1.0
        vals[i] = -norm.pdf(z) * (g1 / 6.0) * f
    return np.trapezoid(vals, ts)


print()
print("=" * 78)
print("Same test on the one-factor Gaussian, where rho_I' != 0 (§10's stated gap)")
print("=" * 78)
rI = PE.rho_I_gauss(np.array([P_TARGET]), RHO)[0]
rIp = PE.rho_I_prime(lambda x: PE.rho_I_gauss(np.atleast_1d(x), RHO), P_TARGET)
print(f"  rho_I({P_TARGET}) = {rI:.4f}   rho_I'({P_TARGET}) = {rIp:+.4f}  (nonzero: the derivative")
print(f"  term is live, unlike the atom mixture)")
print()
print(f"{'b':>6} {'n':>7} {'drift(P1)':>12} {'I_skew':>13} {'I_noHe2':>13}")
gr = []
for b in (100, 200, 400, 800):
    n = b * M
    k = int(np.ceil((n + 1) * P_TARGET))
    Is = integrate_gauss(b, k, True)
    In = integrate_gauss(b, k, False)
    d = (M - 1) / (2.0 * n) * (P_TARGET * (1 - P_TARGET) * rIp - (2 * P_TARGET - 1) * rI)
    gr.append((n, Is, In, d))
    print(f"{b:>6d} {n:>7d} {d:>12.3e} {Is:>13.3e} {In:>13.3e}")

gn = np.array([r[0] for r in gr], float)
ge_s = np.polyfit(np.log(gn), lg([r[1] for r in gr]), 1)[0]
ge_n = np.polyfit(np.log(gn), lg([r[2] for r in gr]), 1)[0]
print()
print(f"  fitted exponent, I_skew  : n^{ge_s:+.2f}")
print(f"  fitted exponent, control : n^{ge_n:+.2f}")
p5 = ge_s < -1.6 and ge_n > -1.4
print(f"  P5  same separation with rho_I' != 0                       : {'PASS' if p5 else 'FAIL'}")
p6 = all(abs(r[1] / r[3]) < 0.05 for r in gr)
print(f"  P6  |I_skew| < 5% of the drift at every n (Gaussian)       : {'PASS' if p6 else 'FAIL'}")
