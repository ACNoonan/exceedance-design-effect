"""SW-12: a second, purely combinatorial exact route to E[C], sharing no code path with
prop1_exact.py — and a reformulation of what the open rigour half actually requires.

    python experiments/2026-07-26-sw02-exchangeability-audit/prop1_combinatorial.py

WHY THIS EXISTS
prop1_exact.py removed the sampling error from Proposition 1's evidence by evaluating
E[C] = int_0^1 P(N(t) <= k-1) dt deterministically: cluster pmf, FFT convolution, Gauss-Legendre
quadrature. That settled the numerical half. Two things it does NOT settle:

  (a) whether the exact computation is itself right. Its controls (q=0 recovers k/(n+1) to 1e-14,
      quadrature refinement moves nothing) are strong, but they exercise the same pipeline that
      produces the answer. An error in the shared machinery would pass both.
  (b) anything about the analytic remainder. It is exact-but-continuum; it evaluates the integral,
      it does not expand it.

This script addresses (a) outright and changes the shape of (b).

THE IDENTITY. Under the atom mixture a cluster is, with probability q, an "atom" whose m members
all share ONE uniform draw; otherwise its m members are i.i.d. uniform. Condition on i, the number
of atom clusters (i ~ Binomial(b, q)). The pooled calibration multiset is then

    M = i + m(b - i)   DISTINCT i.i.d. uniform draws,

i of them carrying multiplicity m and m(b-i) carrying multiplicity 1. Sort them. The values are
i.i.d. and the atom/single label is a property of the CLUSTER, so in sorted order the label pattern
is a uniformly random arrangement of i atoms among M positions, independent of the values.

The pooled k-th order statistic is therefore the L-th smallest distinct draw, where

    L    = min{ l : (cumulative weight through position l) >= k },
    cum  = l + (m-1) R_l,     R_l = #atoms among the first l positions ~ Hypergeom(M, i, l).

R_l is independent of the order statistics, so E[U_(L)] = E[L]/(M+1) EXACTLY, and
E[L] = sum_{l=0}^{M} P(L > l) = sum_{l=0}^{M} P(l + (m-1) R_l <= k-1). Hence

    E[C] = sum_i C(b,i) q^i (1-q)^{b-i} * E[L_i] / (M_i + 1).                          (*)

Every step is an identity. There is no normal approximation, no continuity correction, no Edgeworth
term, no lattice correction and no quadrature anywhere in (*) — it is a finite sum of
hypergeometric CDFs.

THE REFORMULATION. Writing pi_1 < ... < pi_i for the atom positions (pi_0 := 0, pi_{i+1} := M+1),
R_l = r exactly for l in [pi_r, pi_{r+1} - 1], so with c_r := k-1-(m-1)r,

    E[L] = sum_{r=0}^{i} E[ ( min(c_r, pi_{r+1} - 1) - pi_r + 1 )^+ ].                 (**)

This matters for what remains open. integrity.md scopes SW-12's residual as: bound the remainder of
an Edgeworth expansion for a LATTICE sum, uniformly enough in the continuous level t to survive
integration over t. In (**) there is no t. The remaining analytic object is an expectation of
truncated gaps between discrete uniform ORDER STATISTICS, whose exact law is negative-hypergeometric
and whose asymptotics carry classical Berry-Esseen rates. That is a standard problem rather than a
bespoke one. It is not a proof, and this script does not claim one; it relocates the difficulty.

SCOPE, STATED PLAINLY. (*) and (**) are specific to the atom mixture, the model for which
rho_I(t) == q at every level and therefore rho_I' = 0. They test the second term of Proposition 1
alone and say nothing about the derivative term behind Corollary 3's sign claim, for which the
one-factor Gaussian in prop1_exact.py remains the only evidence.
"""

from __future__ import annotations

import itertools
from math import comb

import numpy as np
from scipy.stats import binom, hypergeom

M_CLUSTER = 4
Q_ATOM = 0.30
WEIGHT_FLOOR = 1e-18  # drop atom-count strata below this binomial mass, then renormalise


# --------------------------------------------------------------------------- the identity (*)

def exact_EC_combinatorial(b: int, m: int, q: float, k: int) -> float:
    """E[C] by identity (*). No quadrature, no convolution, no approximation."""
    i_all = np.arange(b + 1)
    w_all = binom.pmf(i_all, b, q)
    keep = w_all > WEIGHT_FLOOR
    i_kept, w_kept = i_all[keep], w_all[keep]

    total = 0.0
    for i, w in zip(i_kept, w_kept):
        i = int(i)
        M = i + m * (b - i)
        ell = np.arange(M + 1)
        # P(l + (m-1) R_l <= k-1) = P(R_l <= (k-1-l)/(m-1))
        EL = float(np.sum(hypergeom.cdf(np.floor((k - 1 - ell) / (m - 1)), M, i, ell)))
        total += w * EL / (M + 1)
    return total / float(np.sum(w_kept))


def predicted_drift_atom(n: int, m: int, p: float, q: float) -> float:
    """Proposition 1 for the atom mixture. rho_I(t) == q at every level, so rho_I' = 0
    and the prediction collapses to the second term: -(m-1)(2p-1)q / (2n)."""
    return -(m - 1) * (2 * p - 1) * q / (2 * n)


# ------------------------------------------------------- the reformulation (**), three ways

def EL_hypergeom(M: int, i: int, m: int, k: int) -> float:
    ell = np.arange(M + 1)
    return float(np.sum(hypergeom.cdf(np.floor((k - 1 - ell) / (m - 1)), M, i, ell)))


def EL_gaps(M: int, i: int, m: int, k: int) -> float:
    """Right-hand side of (**), summed over the exact joint law of (pi_r, pi_{r+1})."""
    total, denom = 0.0, comb(M, i)
    for r in range(i + 1):
        c_r = k - 1 - (m - 1) * r
        for lo in ([0] if r == 0 else range(1, M + 1)):
            for hi in ([M + 1] if r == i else range(lo + 1, M + 1)):
                if r == 0 and i == 0:
                    w = 1
                elif r == 0:
                    w = comb(M - hi, i - 1)
                elif r == i:
                    w = comb(lo - 1, i - 1)
                else:
                    w = comb(lo - 1, r - 1) * comb(M - hi, i - r - 1)
                if w:
                    total += (w / denom) * max(min(c_r, hi - 1) - lo + 1, 0)
    return total


def EL_bruteforce(M: int, i: int, m: int, k: int) -> float:
    """Enumerate every arrangement of i atoms among M positions and average L directly."""
    tot = cnt = 0
    for atoms in itertools.combinations(range(1, M + 1), i):
        aset, cum, L = set(atoms), 0, M
        for pos in range(1, M + 1):
            cum += m if pos in aset else 1
            if cum >= k:
                L = pos
                break
        tot += L
        cnt += 1
    return tot / cnt


# ------------------------------------------------------------------------------------ report

def preconditions() -> bool:
    ok = True
    print("[0] PRECONDITION — at q=0 there are no atoms, so (*) must return k/(n+1) EXACTLY.")
    print("    Not 'to 1e-14': (*) is an identity, so the only error is floating point.")
    for b, m in ((50, 4), (120, 5), (400, 2)):
        n = b * m
        k = int(round(0.9 * (n + 1)))
        err = exact_EC_combinatorial(b, m, 0.0, k) - k / (n + 1)
        flag = "PASS" if abs(err) < 1e-12 else "FAIL"
        ok &= flag == "PASS"
        print(f"    b={b:>4} m={m}   E[C] - k/(n+1) = {err:+.3e}   {flag}")

    print()
    print("[0b] OPPOSITE ENDPOINT — at q=1 every cluster is an atom, so the sample is b distinct")
    print("     draws of multiplicity m each and coverage is the exact Beta mean ceil(k/m)/(b+1).")
    print("     This endpoint is not reachable by prop1_exact.py's controls.")
    for b in (25, 50, 100):
        m = M_CLUSTER
        n = b * m
        k = int(round(0.9 * (n + 1)))
        err = exact_EC_combinatorial(b, m, 1.0, k) - int(np.ceil(k / m)) / (b + 1)
        flag = "PASS" if abs(err) < 1e-12 else "FAIL"
        ok &= flag == "PASS"
        print(f"    b={b:>4} m={m} k={k:>5}   E[C] - ceil(k/m)/(b+1) = {err:+.3e}   {flag}")
    return ok


def reformulation() -> bool:
    print("[3] THE REFORMULATION (**) — hypergeometric form vs gap form vs brute-force")
    print("    enumeration of every arrangement. Small cases, including both degenerate")
    print("    endpoints i=0 (no atoms) and i=M (all atoms).")
    print(f"{'M':>7}{'i':>4}{'m':>4}{'k':>5}{'hypergeom':>15}{'gaps':>15}"
          f"{'brute force':>15}{'max diff':>12}")
    ok = True
    for M, i, m, k in [(8, 3, 4, 12), (10, 4, 3, 9), (12, 5, 2, 11), (14, 6, 4, 25),
                       (9, 0, 4, 5), (9, 9, 4, 20), (11, 2, 5, 14), (13, 7, 3, 20)]:
        a, bb, c = EL_hypergeom(M, i, m, k), EL_gaps(M, i, m, k), EL_bruteforce(M, i, m, k)
        d = max(abs(a - bb), abs(bb - c))
        ok &= d < 1e-9
        print(f"{M:>7}{i:>4}{m:>4}{k:>5}{a:>15.8f}{bb:>15.8f}{c:>15.8f}{d:>12.2e}")
    return ok


def main() -> int:
    print("SW-12 / combinatorial identity for E[C] under the atom mixture, "
          f"m={M_CLUSTER}, q={Q_ATOM}\n")
    ok = preconditions()
    print()

    print("[1] THE DRIFT BY IDENTITY (*) — this column must reproduce prop1_exact.py's")
    print("    MODEL A, which reaches the same numbers through an FFT convolution and")
    print("    Gauss-Legendre quadrature. No code is shared between the two routes.")
    print(f"{'b':>6}{'n':>7}{'p':>10}{'exact drift':>16}{'predicted':>15}"
          f"{'ratio':>9}{'residual':>13}{'n^2*resid':>12}")
    rows = []
    for b in (25, 50, 100, 200, 400, 800):
        n = b * M_CLUSTER
        k = int(round(0.9 * (n + 1)))
        p = k / (n + 1)
        drift = exact_EC_combinatorial(b, M_CLUSTER, Q_ATOM, k) - p
        pred = predicted_drift_atom(n, M_CLUSTER, p, Q_ATOM)
        resid = drift - pred
        rows.append((n, drift, pred, resid))
        print(f"{b:>6}{n:>7}{p:>10.5f}{drift:>16.3e}{pred:>15.3e}"
              f"{drift / pred:>9.4f}{resid:>13.3e}{n * n * resid:>12.4f}")
    print()

    ns = np.array([r[0] for r in rows], float)
    rs = np.abs(np.array([r[3] for r in rows], float))
    slope = np.polyfit(np.log(ns), np.log(rs), 1)[0]
    print(f"[2] REMAINDER SCALING: |residual| ~ n^({slope:.2f})   "
          f"[Proposition 1 claims O(n^-2)]")
    print(f"    n^2 * residual at n={int(ns[-1])}: {ns[-1] ** 2 * rows[-1][3]:.4f}")
    print("    prop1_exact.py reports n^(-1.98) and -0.8269 at the same n.")
    print()

    ok &= reformulation()
    print()
    print("ALL CHECKS PASS" if ok else "SOME CHECKS FAILED")
    print()
    print("WHAT THIS DOES NOT DO: it does not bound the remainder. It confirms the exact")
    print("computation independently, and it shows the remaining analytic problem can be")
    print("posed without the continuous level t, which is the part integrity.md flags as")
    print("the crux. The derivative term behind Corollary 3 is untouched by either route.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
