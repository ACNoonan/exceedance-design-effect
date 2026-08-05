"""Two stress tests on the assumptions the law rests on. Exact, no Monte Carlo.

    python experiments/2026-07-26-sw02-exchangeability-audit/assumption_stress.py

TEST 1 — ACROSS-FAMILY DEPENDENCE, the assumption SW-19 left untouched
(A1) asks that clusters be i.i.d. Every within-family variant checked in SW-19 kept that. But a
shared base model, a shared prompt distribution, or overlapping retrieval pools induce dependence
BETWEEN families, which is the threat that inflates b itself. Model it with a global factor:

    X_ji = sqrt(g) W + sqrt(a) Z_j + sqrt(1-g-a) eps_ji,

so the within-family score correlation is g+a and the ACROSS-family correlation is g > 0.

The question that decides everything is whether the test point sees the same W.

  BRANCH A — it does (one deployment, one base model, calibration and test drawn together).
    Conditional on W every score shifts by the same sqrt(g) W, and coverage is invariant to a
    common location shift, so C is distributed exactly as the ordinary one-factor model at the
    CONDITIONAL within-family correlation r_cond = a/(1-g), independent of W. Across-family
    dependence is then completely harmless -- but the ICC you would estimate by pooling calibration
    data is the MARGINAL one, g+a, which is too large. Using it understates n_eff.

  BRANCH B — it does not (the test point is a fresh draw with its own W'). Then
    C = Phi( Phi^-1(V) + xi ),  xi ~ N(0, 2g/(1-g)) independent of V,
    where V is the branch-A coverage. This is not a clustering effect at all and no n_eff repairs
    it; it is distribution shift wearing a clustering costume.

TEST 2 — CAN THE SCORE-CORRELATION RIVAL BE ANTI-CONSERVATIVE?
Section 4.2 says the rival design effect is conservative "here" but "not conservative by design."
Across Gaussian and Clayton at every level checked, rho_I < rho_score, so the rival always
overstates dispersion and merely wastes calibration data. If that were universal the paper's claim
would be right but low-stakes. It is not universal, and the counterexample is exact rather than
numerical: take a cluster of m=2 with

    with probability q,  U2 = U1        (comonotone)
    otherwise,           U2 = 1 - U1    (countermonotone)

Both marginals stay uniform, so this is a valid copula. Then rho_score = 2q - 1, which is ZERO at
q = 1/2 and NEGATIVE below it, while delta(p) = q p + (1-q)(2p-1) for p > 1/2 leaves rho_I(p)
strictly positive. A practitioner reading the score correlation sees no dependence, or apparent
negative dependence inviting a variance BONUS, while the true design effect exceeds 1.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.stats import norm

sys.path.insert(0, str(Path(__file__).resolve().parent))
from prop1_exact import (GL_NODES, N_SIGMA, Z_CUT, cluster_pmf_gauss,  # noqa: E402
                         rho_I_gauss, exact_EC)

GQ = 400


def _znodes():
    x, w = leggauss(GQ)
    z = Z_CUT * x
    return z, Z_CUT * w * norm.pdf(z)


def phi2(x, r):
    """Phi_2(x, x; r) by one-factor quadrature."""
    z, w = _znodes()
    return float(norm.cdf((x - np.sqrt(r) * z) / np.sqrt(1.0 - r)) ** 2 @ w)


# ---------------------------------------------------------------- shared survival machinery

def survival_grid(pmf_fn, rho_fn, b, m, k, chunk=200):
    """(ts, wq, tail) with tail(t) = P(N(t) <= k-1) = P(V > t) on a Gauss-Legendre grid."""
    n = b * m
    p = k / (n + 1.0)
    D = 1.0 + (m - 1.0) * float(np.atleast_1d(rho_fn(p))[0])
    w_t = np.sqrt(p * (1.0 - p) * D / n)
    lo, hi = max(1e-13, p - N_SIGMA * w_t), min(1.0 - 1e-13, p + N_SIGMA * w_t)
    x, wq = leggauss(GL_NODES)
    ts = 0.5 * (hi - lo) * x + 0.5 * (hi + lo)
    wq = 0.5 * (hi - lo) * wq
    L = 1 << int(np.ceil(np.log2(n + 1)))
    tail = np.empty(ts.size)
    for s in range(0, ts.size, chunk):
        sl = slice(s, min(s + chunk, ts.size))
        pmf = pmf_fn(ts[sl])
        pad = np.zeros((pmf.shape[0], L))
        pad[:, : m + 1] = pmf
        tot = np.fft.irfft(np.fft.rfft(pad, axis=1) ** b, n=L, axis=1)
        tail[sl] = tot[:, :k].sum(axis=1)
    return ts, wq, tail, lo


def Eh(h, hp, ts, wq, tail, lo):
    """E[h(V)] = h(lo) + int_lo^hi h'(v) P(V > v) dv, exact for V supported in [lo, hi]."""
    return h(lo) + float((hp(ts) * tail) @ wq)


# ---------------------------------------------------------------- test 1

def test1(b=200, m=4, p_target=0.90):
    print("[1] ACROSS-FAMILY DEPENDENCE — a global factor shared by every cluster")
    n = b * m
    k = int(round(p_target * (n + 1)))
    p = k / (n + 1.0)
    print(f"    b={b} clusters of m={m}, n={n}, p={p:.5f}\n")
    print(f"    {'g (across)':>11} {'a':>6} {'within':>7} {'r_cond':>7} "
          f"{'rhoI(cond)':>10} {'rhoI(marg)':>10} {'n_eff true':>11} {'n_eff if pooled':>15}")
    for g, a in ((0.00, 0.40), (0.10, 0.30), (0.20, 0.25), (0.35, 0.20), (0.50, 0.15)):
        within = g + a
        r_cond = a / (1.0 - g)
        ri_c = float(rho_I_gauss(np.array([p]), r_cond)[0])
        ri_m = float(rho_I_gauss(np.array([p]), within)[0])
        ne_c = n / (1.0 + (m - 1.0) * ri_c)
        ne_m = n / (1.0 + (m - 1.0) * ri_m)
        print(f"    {g:>11.2f} {a:>6.2f} {within:>7.2f} {r_cond:>7.4f} "
              f"{ri_c:>10.4f} {ri_m:>10.4f} {ne_c:>11.1f} {ne_m:>15.1f}")
    print("\n    BRANCH A (test point shares W): coverage is invariant to the common shift, so the")
    print("    law holds EXACTLY at r_cond. Across-family dependence costs nothing. But an ICC")
    print("    estimated from pooled calibration data is the marginal one, so n_eff is understated")
    print("    (last column) — conservative, and by a lot at large g.\n")

    print("    BRANCH B (test point has its own W'): C = Phi(Phi^-1(V) + xi), xi ~ N(0, 2g/(1-g))")
    print(f"    {'g':>6} {'sd(V) branch A':>15} {'sd(C) branch B':>15} {'inflation':>10}")
    for g, a in ((0.00, 0.40), (0.05, 0.35), (0.10, 0.30), (0.20, 0.25), (0.35, 0.20)):
        r_cond = a / (1.0 - g)
        ts, wq, tail, lo = survival_grid(lambda t: cluster_pmf_gauss(t, m, r_cond),
                                         lambda t: rho_I_gauss(t, r_cond), b, m, k)
        m1 = Eh(lambda v: v, lambda v: np.ones_like(v), ts, wq, tail, lo)
        m2 = Eh(lambda v: v * v, lambda v: 2.0 * v, ts, wq, tail, lo)
        sd_a = np.sqrt(max(m2 - m1 * m1, 0.0))
        if g == 0.0:
            sd_b = sd_a
        else:
            s2 = 2.0 * g / (1.0 - g)                       # Var(xi)
            c = 1.0 / np.sqrt(1.0 + s2)
            h1 = lambda v: norm.cdf(norm.ppf(v) * c)                       # noqa: E731
            h1p = lambda v: c * norm.pdf(norm.ppf(v) * c) / norm.pdf(norm.ppf(v))   # noqa: E731
            r2 = s2 / (1.0 + s2)
            h2 = lambda v: np.array([phi2(norm.ppf(vv) * c, r2) for vv in np.atleast_1d(v)])  # noqa: E731
            eps = 1e-6
            h2p = lambda v: (h2(np.clip(v + eps, 1e-12, 1 - 1e-12))                 # noqa: E731
                             - h2(np.clip(v - eps, 1e-12, 1 - 1e-12))) / (2 * eps)
            b1 = Eh(h1, h1p, ts, wq, tail, lo)
            b2 = Eh(lambda v: h2(v)[0] if np.isscalar(v) else h2(v), h2p, ts, wq, tail, lo)
            sd_b = np.sqrt(max(b2 - b1 * b1, 0.0))
        print(f"    {g:>6.2f} {sd_a:>15.6f} {sd_b:>15.6f} {sd_b/sd_a:>10.2f}x")
    print("\n    Branch B is not a clustering effect and no n_eff repairs it — the inflation comes")
    print("    from the calibration set and the test point sitting under different draws of W.")


# ---------------------------------------------------------------- test 2

def delta_flip(t, q):
    """delta(t) for the comonotone/countermonotone mixture, m = 2."""
    t = np.atleast_1d(t)
    return q * t + (1.0 - q) * np.maximum(0.0, 2.0 * t - 1.0)


def rho_I_flip(t, q):
    t = np.atleast_1d(t)
    return (delta_flip(t, q) - t * t) / (t * (1.0 - t))


def cluster_pmf_flip(t, q):
    """pmf of the m=2 cluster count. N in {0,1,2}."""
    t = np.atleast_1d(t)
    d = delta_flip(t, q)
    return np.stack([1.0 - 2.0 * t + d, 2.0 * (t - d), d], axis=1)


def test2(b=400, p_target=0.90):
    print("\n[2] CAN THE SCORE-CORRELATION RIVAL BE ANTI-CONSERVATIVE?")
    m, n = 2, 2 * b
    k = int(round(p_target * (n + 1)))
    p = k / (n + 1.0)
    print(f"    m=2, b={b}, n={n}, p={p:.5f}")
    print(f"    {'q':>6} {'rho_score':>10} {'rho_I(p)':>9} {'DEFF true':>10} {'DEFF rival':>11} "
          f"{'sd exact':>10} {'sd law':>9} {'sd rival':>9} {'verdict':>16}")
    bad = False
    # The grid must straddle q = 1 - p, where rho_I(p) = [q - (1-p)]/p changes sign.
    # Stopping at 0.10 = 1 - p (as this did through v7) meant the printed claim
    # "below q=0.5 the truth is still inflation" could not be contradicted by the sweep.
    for q in (1.00, 0.75, 0.50, 0.30, 0.10, 0.05, 0.02):
        rs = 2.0 * q - 1.0
        ri = float(rho_I_flip(np.array([p]), q)[0])
        deff_t = 1.0 + (m - 1.0) * ri
        deff_r = 1.0 + (m - 1.0) * rs
        ec = exact_EC(lambda t: cluster_pmf_flip(t, q), lambda t: rho_I_flip(t, q), b, m, k)
        # exact sd via the survival grid
        ts, wq, tail, lo = survival_grid(lambda t: cluster_pmf_flip(t, q),
                                         lambda t: rho_I_flip(t, q), b, m, k)
        m1 = Eh(lambda v: v, lambda v: np.ones_like(v), ts, wq, tail, lo)
        m2 = Eh(lambda v: v * v, lambda v: 2.0 * v, ts, wq, tail, lo)
        sd_ex = np.sqrt(max(m2 - m1 * m1, 0.0))
        sd_law = np.sqrt(p * (1 - p) * deff_t / n)
        sd_riv = np.sqrt(p * (1 - p) * max(deff_r, 1e-9) / n)
        anti = sd_riv < sd_ex * 0.999
        bad |= anti
        print(f"    {q:>6.2f} {rs:>10.3f} {ri:>9.4f} {deff_t:>10.4f} {deff_r:>11.4f} "
              f"{sd_ex:>10.6f} {sd_law:>9.6f} {sd_riv:>9.6f} "
              f"{'ANTI-CONSERVATIVE' if anti else 'conservative':>16}")
    print(f"\n    -> the rival is {'NOT ' if bad else ''}conservative by design"
          f"{': counterexample found' if bad else ''}")
    print("    At q=0.5 the score correlation is exactly 0 — a practitioner applying the rival")
    print("    applies no correction at all — while rho_I(p) > 0 and the true design effect")
    print(f"    exceeds 1. Throughout {1 - p:.2f} < q < 0.50 the score correlation is NEGATIVE,")
    print("    which reads as a variance bonus, while the true design effect still exceeds 1.")
    print(f"    Below q = 1 - p = {1 - p:.2f} the two agree in sign and the bonus is real:")
    print("    rho_I(p) = [q - (1-p)]/p, so the crossing is exactly at q = 1 - p.")


def main() -> int:
    test1()
    test2()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
