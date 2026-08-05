"""Three gaps the mean-pairwise-ICC argument does NOT close. Exact, no Monte Carlo.

    python experiments/2026-07-26-sw02-exchangeability-audit/composition_check.py

The algebra behind §3.3 is airtight for the VARIANCE: Var(sum of a family's exceedance indicators)
= m t(1-t)[1 + (m-1) rhobar_I(t)] for any within-family structure whatever, because a sum's
variance depends only on the sum of its covariances. Theorem 1 runs on that variance and is
therefore clear.

Proposition 1 is not. Its derivation also passes through an Edgeworth step whose third cumulant is
NOT determined by pairwise correlations, so its structure-independence was verified numerically
(§4.4) rather than proved -- and every structure tested there was a balanced, positively
correlated, Gaussian FACTOR model. Three gaps remain, and each is cheap to close.

GAP 1 -- COMPOSITION. The paper makes two substitutions in separate places: ragged family sizes
replace m with the size-biased mean m~ (§3.4, Proposition 2), and non-exchangeable structure
replaces rho_I with the mean pairwise rhobar_I (§3.3). Real calibration data has both at once --
the PRM set has sizes from 8 to 135 AND within-question structure. Nobody has checked the two
substitutions compose. They are derived independently and could interact: m~ reweights families by
size, and rhobar_I is itself a per-family quantity, so a size-correlated structure could break the
factorisation.

GAP 2 -- NEGATIVE CORRELATION. Every test so far used rho_I > 0. The law as stated permits
rho_I < 0, which means n_eff > n: clustering that HELPS. That is not exotic -- it is what
antithetic or stratified calibration sampling deliberately produces. If the law holds there it is
worth one sentence; if it breaks there it is worth a limitation. Currently the paper says nothing.

GAP 3 -- UNBALANCED STRUCTURE. §4.4's nested tests split families into equal subgroups. Unequal
subgroups make rhobar_I an average over pairs with very different weights, which is the closest
within-family analogue of the informative-size problem §3.5 warns about.

METHOD
Ragged families break the b-fold convolution power used elsewhere: clusters are no longer
identically distributed, so N(t)'s pmf is the product of per-family characteristic functions rather
than one raised to the b. Everything else is unchanged and still exact.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.special import comb

sys.path.insert(0, str(Path(__file__).resolve().parent))
from prop1_exact import GL_NODES, N_SIGMA, rho_I_gauss, rho_I_prime  # noqa: E402
from nested_structure import nested_cluster_pmf, rho_bar_I  # noqa: E402
from assumption_stress import cluster_pmf_flip, rho_I_flip  # noqa: E402


def ragged_moments(pmfs_fn, sizes, k, rbar_p, p, chunk=120):
    """(E[C], sd) for families of DIFFERENT sizes. pmfs_fn(t) -> list of (T, m_j+1) arrays."""
    n = int(sum(sizes))
    lo_scale = np.sqrt(p * (1 - p) * (1 + (max(sizes) - 1) * max(rbar_p, 0.0)) / n)
    lo = max(1e-13, p - N_SIGMA * lo_scale)
    hi = min(1 - 1e-13, p + N_SIGMA * lo_scale)
    x, wq = leggauss(GL_NODES)
    ts = 0.5 * (hi - lo) * x + 0.5 * (hi + lo)
    wq = 0.5 * (hi - lo) * wq
    L = 1 << int(np.ceil(np.log2(n + 1)))
    tail = np.empty(ts.size)
    for s in range(0, ts.size, chunk):
        sl = slice(s, min(s + chunk, ts.size))
        acc = None
        for pmf in pmfs_fn(ts[sl]):
            pad = np.zeros((pmf.shape[0], L))
            pad[:, : pmf.shape[1]] = pmf
            f = np.fft.rfft(pad, axis=1)
            acc = f if acc is None else acc * f
        tot = np.fft.irfft(acc, n=L, axis=1)
        tail[sl] = tot[:, :k].sum(axis=1)
    m1 = lo + float(tail @ wq)
    m2 = lo**2 + 2.0 * float((ts * tail) @ wq)
    return m1, np.sqrt(max(m2 - m1 * m1, 0.0))


def m_tilde(sizes):
    s = np.asarray(sizes, float)
    return float((s**2).sum() / s.sum())


def split(m):
    """Two subgroups, as even as possible."""
    return [m // 2, m - m // 2]


def gap1_composition():
    print("[1] COMPOSITION — ragged sizes AND nested structure at the same time")
    print("    Law fed m~ (size-biased mean) and rhobar_I (mean pairwise). Both substitutions at once.\n")
    print(f"    {'profile':<26} {'m~':>6} {'rhobar_I':>9} {'sd exact':>10} {'sd law':>9} {'ratio':>7} "
          f"{'drift ex':>11} {'drift law':>11} {'ratio':>7}")
    profiles = [
        ("uniform m=4 (control)",   [4] * 200,               0.40, 0.00),
        ("ragged 2/4/8, exch",      ([2] * 80 + [4] * 80 + [8] * 80), 0.40, 0.00),
        ("ragged 2/4/8, nested",    ([2] * 80 + [4] * 80 + [8] * 80), 0.25, 0.35),
        ("ragged 2/6/16, nested",   ([2] * 70 + [6] * 70 + [16] * 70), 0.20, 0.45),
    ]
    out = []
    for label, sizes, a, c in profiles:
        n = int(sum(sizes)); k = int(round(0.90 * (n + 1))); p = k / (n + 1.0)
        mt = m_tilde(sizes)
        uniq = sorted(set(sizes))
        # rhobar_I averaged over families, weighted the way m~ weights them: by m_j(m_j-1),
        # which is the number of pairs each family contributes to the total covariance.
        wts = {u: sizes.count(u) * u * (u - 1) for u in uniq}
        tot = sum(wts.values())

        def rbar(t, uniq=uniq, wts=wts, tot=tot, a=a, c=c):
            acc = 0.0
            for u in uniq:
                if u == 1:
                    continue
                r = (rho_bar_I(t, 2, u // 2, a, c) if c > 0 and u >= 2
                     else rho_I_gauss(t, a))
                acc = acc + wts[u] / tot * np.atleast_1d(r)
            return acc

        def pmfs(ts, sizes=sizes, a=a, c=c):
            cache = {}
            for u in sorted(set(sizes)):
                cache[u] = (nested_cluster_pmf(ts, 2, u // 2, a, c) if c > 0 and u >= 2
                            else nested_cluster_pmf(ts, 1, u, a, 0.0))
            return [cache[u] for u in sizes]

        rb = float(np.atleast_1d(rbar(p))[0])
        ec, sd = ragged_moments(pmfs, sizes, k, rb, p)
        sd_law = np.sqrt(p * (1 - p) * (1 + (mt - 1) * rb) / n)
        rbp = rho_I_prime(rbar, p)
        d_law = (mt - 1) / (2 * n) * (p * (1 - p) * rbp - (2 * p - 1) * rb)
        d_ex = ec - p
        out.append((label, sd / sd_law, d_ex / d_law))
        print(f"    {label:<26} {mt:>6.2f} {rb:>9.4f} {sd:>10.6f} {sd_law:>9.6f} {sd/sd_law:>7.4f} "
              f"{d_ex:>11.3e} {d_law:>11.3e} {d_ex/d_law:>7.4f}")
    return out


def gap2_negative():
    print("\n[2] NEGATIVE rho_I — does the law hold when clustering HELPS?")
    print("    Flip copula at q -> 0 gives rho_I(p) = -(1-p)/p < 0, so n_eff > n.\n")
    print(f"    {'q':>6} {'rho_I(p)':>10} {'n_eff/n':>9} {'sd exact':>10} {'sd law':>9} {'ratio':>7}")
    m, b = 2, 400
    n = m * b; k = int(round(0.90 * (n + 1))); p = k / (n + 1.0)
    out = []
    for q in (0.20, 0.10, 0.05, 0.00):
        ri = float(rho_I_flip(np.array([p]), q)[0])
        deff = 1 + (m - 1) * ri
        _, sd = ragged_moments(lambda ts, q=q: [cluster_pmf_flip(ts, q)] * b, [m] * b, k, ri, p)
        sd_law = np.sqrt(p * (1 - p) * deff / n)
        out.append((q, sd / sd_law))
        print(f"    {q:>6.2f} {ri:>10.4f} {1/deff:>9.4f} {sd:>10.6f} {sd_law:>9.6f} {sd/sd_law:>7.4f}")
    return out


def gap3_unbalanced():
    print("\n[3] UNBALANCED SUBGROUPS — rhobar_I averaging over very unequal pair weights")
    print(f"    {'structure':<28} {'rhobar_I':>9} {'sd ratio':>9} {'drift ratio':>12}")
    b = 200
    out = []
    for label, ns, ks, a, c in [("m=8 balanced 2x4",   2, 4, 0.05, 0.75),
                                ("m=8 as 4x2",         4, 2, 0.05, 0.75),
                                ("m=9 as 3x3",         3, 3, 0.05, 0.75),
                                ("m=10 as 5x2",        5, 2, 0.02, 0.85)]:
        m = ns * ks; n = b * m; k = int(round(0.90 * (n + 1))); p = k / (n + 1.0)
        rbar = lambda t, ns=ns, ks=ks, a=a, c=c: rho_bar_I(t, ns, ks, a, c)  # noqa: E731
        rb = float(np.atleast_1d(rbar(p))[0])
        ec, sd = ragged_moments(
            lambda ts, ns=ns, ks=ks, a=a, c=c: [nested_cluster_pmf(ts, ns, ks, a, c)] * b,
            [m] * b, k, rb, p)
        sd_law = np.sqrt(p * (1 - p) * (1 + (m - 1) * rb) / n)
        rbp = rho_I_prime(rbar, p)
        d_law = (m - 1) / (2 * n) * (p * (1 - p) * rbp - (2 * p - 1) * rb)
        out.append((label, sd / sd_law, (ec - p) / d_law))
        print(f"    {label:<28} {rb:>9.4f} {sd/sd_law:>9.4f} {(ec-p)/d_law:>12.4f}")
    return out


def main() -> int:
    g1 = gap1_composition()
    g2 = gap2_negative()
    g3 = gap3_unbalanced()
    print("\nVERDICT")
    print(f"  1 composition : sd ratios {min(r[1] for r in g1):.4f}-{max(r[1] for r in g1):.4f}, "
          f"drift {min(r[2] for r in g1):.4f}-{max(r[2] for r in g1):.4f}")
    print(f"  2 negative    : sd ratios {min(r[1] for r in g2):.4f}-{max(r[1] for r in g2):.4f}")
    print(f"  3 unbalanced  : sd ratios {min(r[1] for r in g3):.4f}-{max(r[1] for r in g3):.4f}, "
          f"drift {min(r[2] for r in g3):.4f}-{max(r[2] for r in g3):.4f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
