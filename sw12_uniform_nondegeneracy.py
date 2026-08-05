#!/usr/bin/env python3
"""SW-12 step (1): uniform non-degeneracy of the cluster-count law over a window of t.

§10 records the residual as a two-step lemma. Step (1) is "establish uniform
non-degeneracy over a compact window of t", which the note guessed would follow
from continuity plus compactness. This script tests that guess, and tests the
identity that makes it checkable rather than abstract.

THE CLAIM UNDER TEST.  Write X(t) = #{i <= m : S_i <= q_t} for the exceedance
count of one cluster at level t.  Then

    Var X(t) = m t (1-t) [ 1 + (m-1) rho_I(t) ]                            (V)

-- the cluster-count variance IS m t(1-t) times the design effect.  If (V)
holds, "non-degenerate" and "design effect bounded away from zero" are the same
statement, so step (1) is not a new hypothesis: it is the paper's own object,
and rho_I >= 0 (every regime the paper works in) makes it automatic.

What a lattice Edgeworth expansion needs from the summand law is exactly three
things -- variance bounded below, moments bounded above (automatic here, since
0 <= X <= m), and the lattice Cramer condition sup_{eta<=|theta|<=pi} |phi| <= 1-kappa.
Uniformity in t of the FIRST and THIRD is what step (1) has to supply.

PRECONDITIONS -- each states what a failure would have looked like.

  P1  (V) reproduces a directly computed variance to ~1e-12 across the window
      and across copulas.  WOULD HAVE FAILED IF: rho_I were the score
      correlation rather than the indicator ICC, or if the m(m-1) pair count
      were wrong -- both give visibly wrong numbers, not small ones.

  P2  NEGATIVE CONTROL on non-degeneracy.  The countermonotone pair (m=2,
      U_2 = 1-U_1) has X(1/2) = 1 almost surely.  The check must report
      Var = 0 and rho_I = -1 = -1/(m-1) there.  If the script reported this
      case as non-degenerate, the compactness argument would be proving
      something false.

  P3  NEGATIVE CONTROL on the Cramer-lattice constant.  The comonotone cluster
      (all m scores equal) is supported on {0, m}: span m, not 1.  Its
      characteristic function must return |phi(2pi/m)| = 1, i.e. kappa = 0, so
      the check REFUSES to certify it.  This is the case the paper already
      excludes as the tied endpoint, and it must show up here as the lattice
      degenerating rather than as a passing test.

  P4  Lipschitz continuity of t -> pi_j(t), the input compactness needs.  Every
      copula is 1-Lipschitz in each argument, so the finite-difference
      quotients must stay bounded by a constant depending only on m, uniformly
      over the window -- INCLUDING for the atom mixture, whose rho_I is
      constant in t but whose pi_j still move.

  P5  The uniform constants must be attained, not assumed: report argmin over
      the window, and confirm the min over a fine grid is below the min over a
      coarse one (a sup taken over too few points is not a sup).
"""
from __future__ import annotations
import numpy as np
from scipy.stats import norm
from math import comb

# ---------------------------------------------------------------- machinery
# One-factor Gaussian: S_i = sqrt(r) Z + sqrt(1-r) eps_i.  Given Z = z the m
# indicators are i.i.d. Bernoulli(p_z), so X | Z ~ Binomial(m, p_z) and every
# quantity below is a ONE-dimensional Gaussian quadrature.  This is deliberate:
# scipy's multivariate_t.cdf saturates at 1.0 in the tail and returned an
# impossible rho_I = 2.0 when it was used for this family, so the paper's own
# verify_tail_limit.py uses the 1-D route and so does this.
# hermegauss(400) overflows: its weights are formed as 1/(fm*fm) and go inf,
# giving nan pmfs. Worse, the first run of this script REPORTED P1 AS PASSING
# on those nans, because Python's max(0.0, nan) returns 0.0 -- a precondition
# that silently skips nan cannot fail. Fixed both ways: a stable fixed grid
# here, and an explicit finiteness gate (P0) below.
_NODE = np.linspace(-9.0, 9.0, 3001)
_W = norm.pdf(_NODE)
_W = _W / _W.sum()


def pmf_gauss(t: float, m: int, r: float) -> np.ndarray:
    """pi_j(t) for the one-factor Gaussian copula with score correlation r."""
    if r <= 0.0:
        p = np.full_like(_NODE, t)
    elif r >= 1.0:
        p = (_NODE <= norm.ppf(t)).astype(float)      # comonotone: p_z in {0,1}
    else:
        p = norm.cdf((norm.ppf(t) - np.sqrt(r) * _NODE) / np.sqrt(1.0 - r))
    j = np.arange(m + 1)
    binom = np.array([comb(m, int(jj)) for jj in j])
    return binom * (_W @ (p[:, None] ** j * (1.0 - p[:, None]) ** (m - j)))


def pmf_atom(t: float, m: int, q: float) -> np.ndarray:
    """Atom mixture: with prob q all m scores are identical, else independent.
    rho_I(t) = q identically -- the level-INDEPENDENT case, so it separates a
    genuine t-dependence from an artefact of the quadrature."""
    out = np.zeros(m + 1)
    out[m] += q * t
    out[0] += q * (1.0 - t)
    for j in range(m + 1):
        out[j] += (1.0 - q) * comb(m, j) * t ** j * (1.0 - t) ** (m - j)
    return out


def pmf_counter(t: float) -> np.ndarray:
    """Countermonotone pair, m = 2: U_2 = 1 - U_1.  Both below q_t iff
    U_1 <= t and U_1 >= 1-t, so P(X=2) = max(0, 2t-1)."""
    both = max(0.0, 2.0 * t - 1.0)
    none = max(0.0, 1.0 - 2.0 * t)
    return np.array([none, 1.0 - both - none, both])


def moments(pmf: np.ndarray):
    j = np.arange(len(pmf))
    mu = float(j @ pmf)
    return mu, float((j ** 2) @ pmf) - mu ** 2


def rho_I_of(pmf: np.ndarray, t: float, m: int) -> float:
    """ICC of the exceedance INDICATOR, from the cluster count's second moment.
    E[X(X-1)] = m(m-1) P(two given scores both below), so delta = that / m(m-1)."""
    j = np.arange(len(pmf))
    delta = float((j * (j - 1)) @ pmf) / (m * (m - 1))
    return (delta - t * t) / (t * (1.0 - t))


def cramer_kappa(pmf: np.ndarray, eta: float = 0.35, n_theta: int = 4001):
    """1 - sup_{eta <= theta <= pi} |phi(theta)|.  Zero (or negative) means the
    law sits on a proper sublattice and no span-1 expansion applies."""
    th = np.linspace(eta, np.pi, n_theta)
    j = np.arange(len(pmf))
    phi = np.abs(np.exp(1j * np.outer(th, j)) @ pmf)
    k = int(np.argmax(phi))
    return 1.0 - float(phi[k]), float(th[k])


# ---------------------------------------------------------------- checks
def main() -> None:
    print("=" * 76)
    print("SW-12 step (1): uniform non-degeneracy over a compact window of t")
    print("=" * 76)

    m, WIN = 4, (0.80, 0.98)
    fams = [("one-factor Gaussian r=0.6", lambda t: pmf_gauss(t, m, 0.6)),
            ("one-factor Gaussian r=0.2", lambda t: pmf_gauss(t, m, 0.2)),
            ("atom mixture q=0.25", lambda t: pmf_atom(t, m, 0.25))]

    # ---- P0: nothing under test may be nan or inf ----------------------
    allf = True
    for name, f in fams + [("countermonotone", lambda t: pmf_counter(t)),
                           ("comonotone", lambda t: pmf_gauss(t, m, 1.0))]:
        for t in np.linspace(*WIN, 61):
            pmf = f(t)
            allf &= bool(np.all(np.isfinite(pmf))) and abs(float(pmf.sum()) - 1) < 1e-9
    print(f"\n  P0  every pmf finite and sums to 1 : {'PASS' if allf else 'FAIL'}")
    if not allf:
        print("      -- refusing to report the rest; a nan silently passes a max()-based check.")
        return

    # ---- P1: the variance identity ------------------------------------
    worst = 0.0
    for name, f in fams:
        for t in np.linspace(*WIN, 61):
            pmf = f(t)
            _, var = moments(pmf)
            pred = m * t * (1 - t) * (1 + (m - 1) * rho_I_of(pmf, t, m))
            d = abs(var - pred)
            assert np.isfinite(d), f'non-finite residual at {name} t={t}'
            worst = max(worst, d)
    print(f"\n  P1  Var X(t) == m t(1-t)[1+(m-1)rho_I(t)]   max abs err {worst:.3e}"
          f"   : {'PASS' if worst < 1e-11 else 'FAIL'}")

    # ---- P2: negative control, the degenerate law ----------------------
    pmf = pmf_counter(0.5)
    _, var0 = moments(pmf)
    r0 = rho_I_of(pmf, 0.5, 2)
    ok2 = abs(var0) < 1e-12 and abs(r0 + 1.0) < 1e-12
    print(f"  P2  countermonotone pair at t=1/2: Var {var0:.3e}, rho_I {r0:+.6f} "
          f"(= -1/(m-1)) -- degenerate, correctly refused : {'PASS' if ok2 else 'FAIL'}")

    # ---- P3: negative control, the lattice collapsing -------------------
    pmf_co = pmf_gauss(0.9, m, 1.0)
    k_co, th_co = cramer_kappa(pmf_co)
    ok3 = k_co < 1e-9
    print(f"  P3  comonotone cluster is supported on {{0,{m}}}: kappa {k_co:.2e} at "
          f"theta {th_co:.4f} (2pi/{m} = {2*np.pi/m:.4f}) -- span {m}, refused : "
          f"{'PASS' if ok3 else 'FAIL'}")

    # ---- P4: Lipschitz continuity of the pmf ---------------------------
    worstL = 0.0
    for name, f in fams:
        ts = np.linspace(*WIN, 401)
        P = np.array([f(t) for t in ts])
        worstL = max(worstL, float(np.abs(np.diff(P, axis=0)).max() / (ts[1] - ts[0])))
    ok4 = worstL < 10 * m
    print(f"  P4  max |dpi_j/dt| over all families {worstL:.3f} (bound 10m = {10*m}) "
          f"-- t -> pi(t) Lipschitz : {'PASS' if ok4 else 'FAIL'}")

    # ---- P5: the uniform constants, coarse vs fine ----------------------
    print(f"\n  UNIFORM CONSTANTS over t in [{WIN[0]}, {WIN[1]}], m = {m}")
    print(f"    {'family':<28} {'min DEFF':>9} {'min Var':>9} {'min kappa':>10} "
          f"{'argmin t':>9}")
    ok5 = True
    for name, f in fams:
        rows = []
        for ngrid in (25, 400):
            ts = np.linspace(*WIN, ngrid)
            V, K, D = [], [], []
            for t in ts:
                pmf = f(t)
                _, v = moments(pmf)
                V.append(v)
                D.append(1 + (m - 1) * rho_I_of(pmf, t, m))
                K.append(cramer_kappa(pmf)[0])
            rows.append((min(V), min(K), min(D), ts[int(np.argmin(K))]))
        (vC, kC, _, _), (vF, kF, dF, tF) = rows
        # a sup over too few points is not a sup: the fine grid must find a
        # value at least as extreme as the coarse one.
        ok5 &= (kF <= kC + 1e-12) and (vF <= vC + 1e-12) and kF > 0 and vF > 0
        print(f"    {name:<28} {dF:9.4f} {vF:9.4f} {kF:10.4f} {tF:9.4f}")
    print(f"\n  P5  fine grid finds constants at least as extreme as coarse, all "
          f"strictly positive : {'PASS' if ok5 else 'FAIL'}")

    print("\n  READING")
    print("    Non-degeneracy over the window is not an extra hypothesis: by (V) it")
    print("    is exactly 'the design effect is bounded away from 0', which rho_I >= 0")
    print("    gives for free. Continuity (P4) plus compactness of the window then")
    print("    converts the pointwise statements into the uniform sigma^2_- and")
    print("    kappa(eta) above. The two cases that break it -- P2 and P3 -- are the")
    print("    Frechet lower bound and the tied endpoint, both already excluded.")


if __name__ == "__main__":
    main()
