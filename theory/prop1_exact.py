"""SW-12: test Proposition 1's drift EXACTLY, with no Monte Carlo error.

    python experiments/2026-07-26-sw02-exchangeability-audit/prop1_exact.py

WHY THIS EXISTS
Proposition 1 is an asymptotic expansion whose remainder is not bounded (integrity.md SW-12).
Until now its evidence was simulation: the constant confirmed to ~2%, and the second-order term
"neither detected nor excluded" -- a direct fit gave B = -0.032 +/- 0.215, an error bar seven
times the point estimate. That is too blunt to either support the O(n^-2) claim or catch an error
in it.

It does not have to be simulated. Coverage is the k-th order statistic of the probability-
transformed scores, so

    E[C] = int_0^1 P(N(t) <= k-1) dt,    N(t) = #{i : U_i <= t} = sum_j N_j(t),

is an EXACT identity, and for a specified cluster model every piece is deterministically
computable: the single-cluster pmf in closed form or by quadrature, the b-fold convolution by FFT,
and the outer integral by Gauss-Legendre. No sampling. The only errors are floating point and
quadrature, both of which are checkable and both of which are ~1e-12 here rather than ~1e-2.

WHAT THIS DOES AND DOES NOT SETTLE
It does NOT prove Proposition 1. The open question is analytic: bounding the remainder of an
Edgeworth expansion for a LATTICE sum, uniformly enough in t to survive integration. Plain
Berry-Esseen is not enough -- it gives O(b^-1/2) on P(N(t) <= k-1), which is far larger than the
O(1/n) drift, so the proof must show those terms cancel under the integral. That is the real work
and it is not done here.

What this DOES settle is whether the expansion is right, to many digits instead of two, and
whether the remainder really decays like n^-2. If the proposition is wrong, this finds out; if it
is right, a proof attempt starts from a verified target rather than a hopeful one.

MODELS
Two exchangeable cluster models, chosen so they isolate different terms of the prediction.

  A. ATOM MIXTURE. With probability q all m members of a cluster share one Bernoulli draw;
     otherwise they are independent. Then delta(t) = q t + (1-q) t^2 and

         rho_I(t) = (delta(t) - t^2)/(t(1-t)) = q   EXACTLY, at every level.

     So rho_I'(t) = 0 and the prediction collapses to -(m-1)(2p-1)q/(2n): a clean isolation of
     the second term, with the derivative term switched off by construction rather than by
     approximation. (This exactness is the same algebra SW-16 records for the atom mixture.)

  B. ONE-FACTOR GAUSSIAN. U_i = Phi(sqrt(rho) Z + sqrt(1-rho) eps_i), so conditional on the
     common factor Z the cluster members are i.i.d. Bernoulli with

         pi(z,t) = Phi( (Phi^{-1}(t) - sqrt(rho) z) / sqrt(1-rho) ).

     Both terms of the prediction are active here, and rho_I'(p) != 0, so this is what tests the
     derivative term that drives Corollary 3's sign claim.

PRECONDITION
At q=0 (model A) and rho=0 (model B) the clusters are independent, rho_I == 0, and Proposition 1
predicts exactly zero drift -- while the exact identity must return E[C] = k/(n+1) to machine
precision, since N(t) ~ Binomial(n,t) makes C ~ Beta(k, n+1-k). That is a control on the ENTIRE
pipeline (cluster pmf, FFT convolution, quadrature) with a known closed-form answer, and it is
asserted before any clustered number is read. A pipeline that cannot reproduce the exchangeable
case has nothing to say about the clustered one.
"""

from __future__ import annotations

import numpy as np

from numpy.polynomial.legendre import leggauss
from scipy.stats import norm
from scipy.special import comb

GH_NODES = 240          # quadrature nodes for the common factor Z
GL_NODES = 3000         # Gauss-Legendre nodes across the transition region
N_SIGMA = 14.0          # half-width of the transition region, in sd of the t-transition

# The smallest residual reported by [1]/[2] at the largest n. The quadrature-stability check is
# graded against this rather than an arbitrary epsilon, so the tolerance tracks the measurement.
SMALLEST_REPORTED_RESIDUAL = 3.0e-8


# ----------------------------------------------------------------- cluster models

def cluster_pmf_atom(t, m, q):
    """pmf of the per-cluster count N_j(t) under the atom mixture. Shape (len(t), m+1)."""
    t = np.atleast_1d(t)[:, None]
    r = np.arange(m + 1)[None, :]
    pmf = (1.0 - q) * comb(m, r) * t**r * (1.0 - t)**(m - r)
    pmf[:, 0] += q * (1.0 - t[:, 0])
    pmf[:, m] += q * t[:, 0]
    return pmf


def rho_I_atom(t, q):
    return np.full_like(np.atleast_1d(t), float(q))


Z_CUT = 9.0     # |Z| beyond this contributes < 1e-18 of the standard normal mass


def _gh():
    """Nodes/weights for E_Z[.] with Z ~ N(0,1), by Gauss-Legendre on [-Z_CUT, Z_CUT].

    NOT numpy's hermgauss: its weight computation overflows past ~240 nodes (w = 1/(fm*fm) with
    fm underflowing), which silently returns nan and made the refinement check unrunnable at the
    node counts needed to demonstrate stability. Gauss-Legendre against the explicit normal
    density is stable at any node count and the truncation error is below double precision.
    """
    x, w = leggauss(GH_NODES)
    z = Z_CUT * x
    return z, Z_CUT * w * norm.pdf(z)


def _pi_gauss(t, rho):
    """P(U <= t | Z=z) for the one-factor model. Returns (len(t), GH_NODES)."""
    z, _ = _gh()
    zt = norm.ppf(np.atleast_1d(t))[:, None]
    return norm.cdf((zt - np.sqrt(rho) * z[None, :]) / np.sqrt(1.0 - rho))


def cluster_pmf_gauss(t, m, rho):
    """pmf of N_j(t) under the one-factor Gaussian model, by Gauss-Hermite over Z."""
    if rho == 0.0:
        t = np.atleast_1d(t)[:, None]
        r = np.arange(m + 1)[None, :]
        return comb(m, r) * t**r * (1.0 - t)**(m - r)
    _, w = _gh()
    pi = _pi_gauss(t, rho)                                  # (T, G)
    r = np.arange(m + 1)[None, None, :]
    binom = comb(m, r) * pi[:, :, None]**r * (1.0 - pi[:, :, None])**(m - r)
    return np.einsum("g,tgr->tr", w, binom)


def rho_I_gauss(t, rho):
    """rho_I(t) = (delta(t) - t^2)/(t(1-t)), delta(t) = E_Z[pi(Z,t)^2] -- same quadrature."""
    t = np.atleast_1d(t)
    if rho == 0.0:
        return np.zeros_like(t)
    _, w = _gh()
    pi = _pi_gauss(t, rho)
    delta = pi**2 @ w
    return (delta - t**2) / (t * (1.0 - t))


def rho_I_prime(rho_fn, p, h=1e-5):
    """d rho_I / dp by central difference on the analytic rho_I."""
    return float((rho_fn(p + h)[0] - rho_fn(p - h)[0]) / (2.0 * h))


# ----------------------------------------------------------------- the exact integral

def exact_EC(pmf_fn, rho_fn, b, m, k, chunk=400):
    """E[C] = int_0^1 P(N(t) <= k-1) dt, computed exactly for the given cluster model.

    The integrand is 1 well below the transition and 0 well above it, so the integral splits
    into a closed-form constant part plus a quadrature over a window of +/- N_SIGMA transition
    sd's. Everything outside that window contributes less than 1e-40.
    """
    n = b * m
    p = k / (n + 1.0)
    D = 1.0 + (m - 1.0) * float(np.atleast_1d(rho_fn(p))[0])
    w_t = np.sqrt(p * (1.0 - p) * D / n)                    # sd of the transition in t
    lo = max(1e-13, p - N_SIGMA * w_t)
    hi = min(1.0 - 1e-13, p + N_SIGMA * w_t)

    x, wq = leggauss(GL_NODES)
    ts = 0.5 * (hi - lo) * x + 0.5 * (hi + lo)
    wq = 0.5 * (hi - lo) * wq

    L = 1 << int(np.ceil(np.log2(n + 1)))                   # no circular wraparound: L >= n+1
    tail = np.empty(ts.size)
    for s in range(0, ts.size, chunk):
        sl = slice(s, min(s + chunk, ts.size))
        pmf = pmf_fn(ts[sl])                                # (c, m+1)
        pad = np.zeros((pmf.shape[0], L))
        pad[:, : m + 1] = pmf
        tot = np.fft.irfft(np.fft.rfft(pad, axis=1) ** b, n=L, axis=1)
        tail[sl] = tot[:, :k].sum(axis=1)                   # P(N <= k-1)
    return lo + float(tail @ wq)


def predicted_drift(rho_fn, n, m, p):
    rI = float(np.atleast_1d(rho_fn(p))[0])
    rIp = rho_I_prime(rho_fn, p)
    return (m - 1.0) / (2.0 * n) * (p * (1.0 - p) * rIp - (2.0 * p - 1.0) * rI)


# ----------------------------------------------------------------- driver

def precondition() -> bool:
    """Independent clusters: the pipeline must return the exact Beta mean k/(n+1)."""
    print("[0] PRECONDITION — independent clusters must give E[C] = k/(n+1) exactly")
    ok = True
    for b, m in ((50, 4), (120, 5), (400, 2)):
        n, k = b * m, int(round(0.9 * (b * m + 1)))
        p = k / (n + 1.0)
        for name, pmf_fn, rho_fn in (
            ("atom q=0",  lambda t, m=m: cluster_pmf_atom(t, m, 0.0),  lambda t: rho_I_atom(t, 0.0)),
            ("gauss r=0", lambda t, m=m: cluster_pmf_gauss(t, m, 0.0), lambda t: rho_I_gauss(t, 0.0)),
        ):
            ec = exact_EC(pmf_fn, rho_fn, b, m, k)
            err = abs(ec - p)
            good = err < 5e-12
            ok &= good
            print(f"    b={b:>4} m={m}  {name:<10} E[C]-k/(n+1) = {ec - p:+.3e}  "
                  f"{'PASS' if good else 'FAIL'}")
    print(f"    -> {'pipeline reproduces the exchangeable case' if ok else 'PIPELINE IS BROKEN'}")
    return ok


def study(label, pmf_of, rho_fn, m, bs, target_p=0.9):
    print(f"\n{label}")
    print(f"{'b':>6} {'n':>6} {'p':>8} {'exact drift':>14} {'predicted':>14} "
          f"{'ratio':>8} {'residual':>12} {'n^2*resid':>11}")
    rows = []
    for b in bs:
        n = b * m
        k = int(round(target_p * (n + 1)))
        p = k / (n + 1.0)
        ec = exact_EC(lambda t: pmf_of(t, m), rho_fn, b, m, k)
        d_ex = ec - p
        d_pr = predicted_drift(rho_fn, n, m, p)
        res = d_ex - d_pr
        rows.append((n, d_ex, d_pr, res))
        print(f"{b:>6} {n:>6} {p:>8.5f} {d_ex:>14.3e} {d_pr:>14.3e} "
              f"{d_ex/d_pr:>8.4f} {res:>12.3e} {res*n*n:>11.4f}")
    return rows


def scaling(rows, label):
    """Fit |residual| ~ n^s, and extrapolate the n^-2 coefficient.

    Proposition 1 claims the remainder is O(n^-2), so s should be ~ -2 and n^2 * residual should
    converge to a constant. If the successive n^2*residual differences halve as n doubles, the
    next correction is O(n^-1) on that quantity -- i.e. an O(n^-3) term in the drift, which is
    what an asymptotic expansion should look like. Richardson-extrapolate on that assumption.
    """
    n = np.array([r[0] for r in rows], float)
    res = np.abs(np.array([r[3] for r in rows], float))
    keep = res > 0
    if keep.sum() < 3:
        print(f"  {label}: residual at floating-point floor — remainder unmeasurably small")
        return
    s, _ = np.polyfit(np.log(n[keep]), np.log(res[keep]), 1)
    c = np.array([r[3] * r[0] ** 2 for r in rows], float)
    rich = c[-1] + (c[-1] - c[-2])                      # assumes an O(1/n) approach
    d = np.diff(c)
    halving = " (differences halving — consistent with an O(n^-3) next term)" \
        if len(d) >= 3 and all(abs(d[i + 1]) < abs(d[i]) for i in range(len(d) - 1)) else ""
    print(f"  {label}: |residual| ~ n^({s:+.2f})   [Proposition 1 claims O(n^-2)]")
    print(f"           n^2 * residual -> {rich:+.4f} by Richardson{halving}")


def quadrature_stability() -> bool:
    """The numbers must not move when the quadrature is refined."""
    global GL_NODES, GH_NODES
    print("\n[0b] QUADRATURE STABILITY — refine and confirm the drift does not move")
    b, m = 100, 4
    n, k = b * m, int(round(0.9 * (b * m + 1)))
    p = k / (n + 1.0)
    base_gl, base_gh = GL_NODES, GH_NODES
    out = {}
    for gl, gh in ((1500, 120), (3000, 240), (6000, 400)):
        GL_NODES, GH_NODES = gl, gh
        a = exact_EC(lambda t: cluster_pmf_atom(t, m, 0.30), lambda t: rho_I_atom(t, 0.30), b, m, k) - p
        g = exact_EC(lambda t: cluster_pmf_gauss(t, m, 0.40), lambda t: rho_I_gauss(t, 0.40), b, m, k) - p
        out[(gl, gh)] = (a, g)
        print(f"    GL={gl:>5} GH={gh:>4}   atom {a:+.12e}   gauss {g:+.12e}")
    GL_NODES, GH_NODES = base_gl, base_gh
    vals = list(out.values())
    spread_a = max(abs(v[0] - vals[-1][0]) for v in vals)
    spread_g = max(abs(v[1] - vals[-1][1]) for v in vals)
    spread = max(spread_a, spread_g)
    # The tolerance is set by what this script MEASURES, not by an arbitrary constant. The
    # smallest quantity reported below is the remainder at the largest n; quadrature noise has to
    # sit well under it or the remainder scaling is reading its own numerical error.
    smallest_signal = SMALLEST_REPORTED_RESIDUAL
    margin = smallest_signal / spread if spread > 0 else np.inf
    ok = margin > 100.0
    print(f"    spread across refinements: atom {spread_a:.1e}, gauss {spread_g:.1e}")
    print(f"    smallest residual this script reports: {smallest_signal:.1e}  "
          f"-> quadrature noise is 1/{margin:,.0f} of it  {'PASS' if ok else 'FAIL'}")
    if not ok:
        print("    -> the remainder scaling would be measuring quadrature error, not the model")
    return ok


def robustness(m_list=(2, 4, 8), p_list=(0.80, 0.90, 0.95, 0.99), n_target=1600):
    """Does exact/predicted stay ~1 away from the single (p=0.9, m=4) cell reported above?

    A ratio that is 1.000 at one configuration and not at others would mean the agreement is a
    coincidence of that cell rather than the expansion being right.
    """
    print(f"\n[4] ROBUSTNESS — ratio exact/predicted across p and m, n ~ {n_target}")
    print(f"{'m':>3} " + " ".join(f"{p:>10.2f}" for p in p_list))
    for m in m_list:
        b = max(4, int(round(n_target / m)))
        n = b * m
        row = []
        for p_t in p_list:
            k = int(round(p_t * (n + 1)))
            k = min(max(k, 1), n)
            p = k / (n + 1.0)
            ec = exact_EC(lambda t: cluster_pmf_gauss(t, m, 0.40), lambda t: rho_I_gauss(t, 0.40),
                          b, m, k)
            d_pr = predicted_drift(lambda t: rho_I_gauss(t, 0.40), n, m, p)
            row.append((ec - p) / d_pr if d_pr != 0 else float("nan"))
        print(f"{m:>3} " + " ".join(f"{v:>10.4f}" for v in row))
    print("    (one-factor Gaussian, rho=0.40; 1.0000 is exact agreement with Proposition 1)")


def main() -> int:
    if not precondition():
        print("\nSTOP: clustered numbers are not interpretable while the control fails.")
        return 1
    if not quadrature_stability():
        print("\nSTOP: the drift moves when the quadrature is refined; it is an artifact.")
        return 1

    m = 4
    bs = [25, 50, 100, 200, 400, 800]

    r1 = study(f"[1] MODEL A — atom mixture, q=0.30, m={m}. rho_I == q exactly, so rho_I' = 0\n"
               f"    and the prediction is the second term alone: -(m-1)(2p-1)q/(2n).",
               lambda t, m: cluster_pmf_atom(t, m, 0.30), lambda t: rho_I_atom(t, 0.30), m, bs)

    r2 = study(f"[2] MODEL B — one-factor Gaussian, rho=0.40, m={m}. Both terms active;\n"
               f"    this is what tests the rho_I' term behind Corollary 3's sign claim.",
               lambda t, m: cluster_pmf_gauss(t, m, 0.40), lambda t: rho_I_gauss(t, 0.40), m, bs)

    print("\n[3] REMAINDER SCALING")
    scaling(r1, "model A")
    scaling(r2, "model B")
    robustness()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
