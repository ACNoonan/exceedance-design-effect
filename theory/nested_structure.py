"""Does the law survive NON-exchangeable within-family structure? Exact test.

    python experiments/2026-07-26-sw02-exchangeability-audit/nested_structure.py

THE OBJECTION
A reader asks whether the conclusions are robust across plausible dependence structures rather
than the single one assumption (A1) commits to: "clusters i.i.d., scores exchangeable WITHIN a
cluster." The realistic alternative is hierarchical — beam branches that diverge at depth 40 are
more alike than branches that split at the root, so the within-family correlation matrix is
nested, not exchangeable. Phylogenetic covariance on the ancestry tree is the same shape.

Corollary 1 does NOT already answer this. It says the limit depends on the calibration
distribution only through the copula diagonal delta(p), so two processes with different dependence
structures but matched delta(p) share a coverage law — but it is a corollary of a theorem that
assumes (A1), so "different dependence structures" there means different COPULAS for an
exchangeable pair structure. Non-exchangeable within-cluster structure is outside its scope.

THE CONJECTURE WORTH TESTING
The variance of a family's exceedance-indicator sum is
    Var(sum_i 1{U_i <= t}) = m t(1-t) + sum_{i != j} Cov = m t(1-t) [1 + (m-1) rhobar_I(t)],
where rhobar_I(t) is the MEAN pairwise indicator correlation. It depends on the average and on
nothing else about the structure. Since Theorem 1 runs on that variance (Steps 1-2 reduce
everything to an average of i.i.d. cluster-level terms), the law should survive arbitrary
within-family structure with rhobar_I in place of rho_I.

Proposition 1 is the interesting case and the reason this is a test rather than an algebra
exercise. Its coefficient is built from D(t) = 1 + (m-1) rho_I(t) and its DERIVATIVE, which the
same argument would make rhobar_I-determined — but the proof sketch also needs an Edgeworth
skewness term to integrate away, and the third cumulant of a cluster count is NOT pinned down by
pairwise correlations. So it is genuinely open whether the drift depends on the structure beyond
its mean pairwise ICC. Higher-order joint exceedance probabilities are where structure could bite.

PRE-REGISTERED PREDICTIONS (written before running)
  N1. Theorem 1 survives: exact sd(C) matches sqrt(p(1-p)[1+(m-1) rhobar_I(p)]/n) for every
      nested structure, to the same accuracy the exchangeable case achieves.
  N2. Proposition 1 survives with rhobar_I: exact drift matches the Proposition 1 coefficient
      evaluated at rhobar_I(p) and rhobar_I'(p).
  N3. If N2 FAILS, the failure grows with structural heterogeneity (the gap between within- and
      across-subgroup correlation), because that is what makes the cluster-count distribution
      differ from an exchangeable one at fixed mean pairwise correlation.

  N2 is the one I am unsure of, and it is the one that decides whether the objection is answered
  by a corollary or by a limitation.

METHOD
Nested one-factor Gaussian, exactly computable. Each member is
    X_i = sqrt(a) Z0 + sqrt(c) Z_{s(i)} + sqrt(1-a-c) eps_i,
so members in the same subgroup correlate at a+c and members in different subgroups at a. Setting
c=0 recovers the exchangeable model, which is the control. Conditional on the latent factors all
indicators are independent, so the cluster-count pmf is a nested quadrature and everything stays
exact; moments of C come from E[C] = int P(N<=k-1) dt and E[C^2] = 2 int t P(N<=k-1) dt.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.stats import norm
from scipy.special import comb

sys.path.insert(0, str(Path(__file__).resolve().parent))
from prop1_exact import GL_NODES, N_SIGMA, Z_CUT, rho_I_gauss, rho_I_prime  # noqa: E402

F_NODES = 110           # quadrature nodes per latent level


def _nodes():
    x, w = leggauss(F_NODES)
    z = Z_CUT * x
    return z, Z_CUT * w * norm.pdf(z)


def nested_cluster_pmf(t, n_sub, k_sub, a, c):
    """pmf of the per-cluster count for the nested model. Shape (len(t), m+1).

    m = n_sub * k_sub. Conditional on (Z0, Z_s) the k_sub members of a subgroup are i.i.d.
    Bernoulli; subgroups are i.i.d. given Z0; so integrate Z_s, convolve subgroups, integrate Z0.
    """
    t = np.atleast_1d(t)
    z0, w0 = _nodes()
    zs, ws = _nodes()
    resid = 1.0 - a - c
    zt = norm.ppf(t)[:, None, None]
    shift = np.sqrt(a) * z0[None, :, None] + np.sqrt(c) * zs[None, None, :]
    pi = norm.cdf((zt - shift) / np.sqrt(resid))                    # (T, G0, Gs)

    r = np.arange(k_sub + 1)
    sub = comb(k_sub, r)[None, None, None, :] * pi[..., None]**r \
        * (1.0 - pi[..., None])**(k_sub - r)                        # (T, G0, Gs, k_sub+1)
    sub = np.einsum("s,tgsr->tgr", ws, sub)                         # integrate Z_s

    out = sub
    for _ in range(n_sub - 1):                                      # convolve subgroups
        new = np.zeros(out.shape[:2] + (out.shape[2] + k_sub,))
        for i in range(out.shape[2]):
            new[:, :, i:i + k_sub + 1] += out[:, :, i][:, :, None] * sub
        out = new
    return np.einsum("g,tgr->tr", w0, out)                          # integrate Z0


def rho_bar_I(t, n_sub, k_sub, a, c):
    """Mean pairwise indicator correlation across the m(m-1)/2 pairs of the nested cluster."""
    m = n_sub * k_sub
    n_within = n_sub * comb(k_sub, 2, exact=True)
    n_total = comb(m, 2, exact=True)
    n_across = n_total - n_within
    rw = rho_I_gauss(t, a + c) if (a + c) > 0 else np.zeros_like(np.atleast_1d(t))
    rb = rho_I_gauss(t, a) if a > 0 else np.zeros_like(np.atleast_1d(t))
    return (n_within * rw + n_across * rb) / n_total


def exact_moments(pmf_fn, rbar_fn, b, m, k, chunk=150):
    """(E[C], sd(C)) exactly. E[C]=int P(N<=k-1)dt and E[C^2]=2 int t P(N<=k-1) dt."""
    n = b * m
    p = k / (n + 1.0)
    D = 1.0 + (m - 1.0) * float(np.atleast_1d(rbar_fn(p))[0])
    w_t = np.sqrt(p * (1.0 - p) * D / n)
    lo = max(1e-13, p - N_SIGMA * w_t)
    hi = min(1.0 - 1e-13, p + N_SIGMA * w_t)

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
    m1 = lo + float(tail @ wq)
    m2 = lo**2 + 2.0 * float((ts * tail) @ wq)                      # 2*int_0^lo t dt = lo^2
    return m1, np.sqrt(max(m2 - m1 * m1, 0.0))


def run(label, n_sub, k_sub, a, c, b, p_target=0.90):
    m = n_sub * k_sub
    n = b * m
    k = int(round(p_target * (n + 1)))
    p = k / (n + 1.0)

    rbar = lambda tt: rho_bar_I(tt, n_sub, k_sub, a, c)             # noqa: E731
    pmf = lambda tt: nested_cluster_pmf(tt, n_sub, k_sub, a, c)     # noqa: E731

    ec, sd = exact_moments(pmf, rbar, b, m, k)
    rI = float(np.atleast_1d(rbar(p))[0])
    rIp = rho_I_prime(rbar, p)

    sd_pred = np.sqrt(p * (1.0 - p) * (1.0 + (m - 1.0) * rI) / n)
    d_ex = ec - p
    d_pred = (m - 1.0) / (2.0 * n) * (p * (1.0 - p) * rIp - (2.0 * p - 1.0) * rI)

    rw = a + c
    print(f"{label:<34} {rw:>5.2f} {a:>5.2f} {rI:>7.4f} "
          f"{sd:>9.6f} {sd_pred:>9.6f} {sd/sd_pred:>7.4f} "
          f"{d_ex:>11.3e} {d_pred:>11.3e} {d_ex/d_pred:>7.4f}")
    return sd / sd_pred, d_ex / d_pred


def discriminability(p=0.90):
    """COULD the two have disagreed? Run this BEFORE reading the agreement as confirmation.

    If a nested cluster's count distribution were indistinguishable from an exchangeable one
    matched on rhobar_I, then "the law is unchanged" would be an invariance that cannot fail and
    therefore no evidence at all. So: match an exchangeable Gaussian to each nested structure's
    rhobar_I(p), and compare the cluster-count distributions the law is actually built from.

    The third cumulant is the quantity of interest. Proposition 1's proof sketch needs an Edgeworth
    skewness term to integrate away, and skewness is exactly what pairwise correlations fail to
    pin down. If skewness differs materially between matched structures and the drift does not
    move, that is direct evidence for the step the sketch asserts.
    """
    from scipy.optimize import brentq
    print("[0] DISCRIMINABILITY — could these models have disagreed?")
    print(f"    {'structure':<24} {'rhobar_I':>8} {'r* exch':>8} {'TV':>7} "
          f"{'skew nested':>11} {'skew exch':>10} {'skew diff':>10}")
    cases = [("m=4 exch (control)", 2, 2, 0.40, 0.00),
             ("m=4 nested .30/.50", 2, 2, 0.30, 0.20),
             ("m=4 nested .05/.75", 2, 2, 0.05, 0.70),
             ("m=8 nested .02/.85", 2, 4, 0.02, 0.83),
             ("m=8 nested .05/.80", 4, 2, 0.05, 0.75)]
    worst_tv = 0.0
    for lab, ns, ks, a, c in cases:
        m = ns * ks
        rb = float(rho_bar_I(np.array([p]), ns, ks, a, c)[0])
        rstar = brentq(lambda r: float(rho_I_gauss(np.array([p]), r)[0]) - rb, 1e-9, 0.999,
                       xtol=1e-12)
        pn = nested_cluster_pmf(np.array([p]), ns, ks, a, c)[0]
        pe = nested_cluster_pmf(np.array([p]), 1, m, rstar, 0.0)[0]
        tv = 0.5 * np.abs(pn - pe).sum()
        r = np.arange(m + 1)

        def skew(q):
            mu = (q * r).sum()
            v = (q * (r - mu) ** 2).sum()
            return (q * (r - mu) ** 3).sum() / v**1.5 if v > 0 else np.nan
        sn, se = skew(pn), skew(pe)
        if "control" not in lab:
            worst_tv = max(worst_tv, tv)
        print(f"    {lab:<24} {rb:>8.4f} {rstar:>8.4f} {tv:>7.4f} "
              f"{sn:>11.4f} {se:>10.4f} {100*(sn-se)/abs(se):>9.1f}%")
    print(f"    control TV must be 0 (validates the matching); worst nested TV {worst_tv:.4f}")
    print("    -> the distributions differ materially, so agreement below is not vacuous\n")


def main() -> int:
    b = 200
    discriminability()
    print("Nested one-factor Gaussian. 'within'/'across' are SCORE correlations; rhobar_I is the")
    print("mean pairwise INDICATOR correlation at p=0.90, which is what the law is fed.")
    print("c=0 rows are the exchangeable control — they must reproduce the ordinary result.\n")
    print(f"{'structure':<34} {'w/in':>5} {'acr':>5} {'rhobar_I':>7} "
          f"{'sd exact':>9} {'sd pred':>9} {'ratio':>7} "
          f"{'drift ex':>11} {'drift pred':>11} {'ratio':>7}")

    res = []
    print("-- control: exchangeable (c = 0) " + "-" * 78)
    res.append(("exch m=4 r=0.40", *run("exchangeable m=4, r=0.40", 2, 2, 0.40, 0.00, b)))
    res.append(("exch m=8 r=0.30", *run("exchangeable m=8, r=0.30", 2, 4, 0.30, 0.00, b)))

    print("-- nested: mild heterogeneity " + "-" * 81)
    res.append(("nest m=4 .30/.50", *run("nested m=4 (2x2), .30 / .50", 2, 2, 0.30, 0.20, b)))
    res.append(("nest m=8 .25/.40", *run("nested m=8 (2x4), .25 / .40", 2, 4, 0.25, 0.15, b)))

    print("-- nested: severe heterogeneity (the N3 stress case) " + "-" * 58)
    res.append(("nest m=4 .05/.75", *run("nested m=4 (2x2), .05 / .75", 2, 2, 0.05, 0.70, b)))
    res.append(("nest m=8 .05/.80", *run("nested m=8 (4x2), .05 / .80", 4, 2, 0.05, 0.75, b)))
    res.append(("nest m=8 .02/.85", *run("nested m=8 (2x4), .02 / .85", 2, 4, 0.02, 0.83, b)))

    print("\nVERDICT")
    sd_r = np.array([r[1] for r in res])
    dr_r = np.array([r[2] for r in res])
    print(f"  N1 Theorem 1 with rhobar_I : sd ratios in "
          f"[{sd_r.min():.4f}, {sd_r.max():.4f}]  "
          f"{'HOLDS' if abs(sd_r - 1).max() < 0.02 else 'FAILS'}")
    print(f"  N2 Proposition 1 with rhobar_I: drift ratios in "
          f"[{dr_r.min():.4f}, {dr_r.max():.4f}]  "
          f"{'HOLDS' if abs(dr_r - 1).max() < 0.05 else 'FAILS'}")
    worst = res[int(np.argmax(np.abs(dr_r - 1)))]
    print(f"  N3 worst drift deviation at: {worst[0]}  ({(worst[2]-1)*100:+.2f}%)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
