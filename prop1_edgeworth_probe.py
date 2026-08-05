"""SW-12: is the Edgeworth step in Proposition 1's proof load-bearing, or only inert?

    python experiments/2026-07-26-sw02-exchangeability-audit/prop1_edgeworth_probe.py

WHY THIS EXISTS
Proposition 1's proof sketch takes a normal approximation with continuity correction and then
asserts that the Edgeworth skewness correction "integrates to zero at this order because
int phi(z)(z^2-1) dz = 0". integrity.md scopes SW-12's residual as bounding the remainder of that
Edgeworth expansion for a LATTICE sum, uniformly enough in the continuous level t to survive
integration -- and notes that plain Berry-Esseen is not enough, since it bounds the pointwise CDF
error at O(b^-1/2), far larger than the O(1/n) drift.

That framing quietly assumes the Edgeworth term is part of the derivation. It is worth checking
whether it is, because if the skewness correction only has to NOT CONTRIBUTE rather than to be
expanded with a bounded remainder, the analytic obligation is very different and much weaker.

`prop1_combinatorial.py` makes the check possible. For the atom mixture it gives an exact identity
E[C|i] = E[L]/(M+1) with E[L] = sum_{l=0}^{M} P(A_l <= k-1), A_l = l + (m-1) R_l and R_l
hypergeometric. There is no t in it, so the normal approximation can be swapped in at exactly one
place and its cost measured directly, with nothing else changing.

TWO MEASUREMENTS
  [1] At fixed atom count, replace the exact hypergeometric CDF by a continuity-corrected normal
      and measure the error in E[L]. Since E[C|i] = E[L]/(M+1), an error of c/M in E[L] is c/M^2 in
      E[C] -- exactly Proposition 1's claimed remainder order. So the diagnostic is whether the
      error is Theta(M^-1) or worse.
  [2] Carry the same substitution through the full binomial mixture over atom counts and compare
      the resulting drift against both the exact identity and Proposition 1.

WHAT A PASS WOULD MEAN. That Proposition 1's O(1/n) coefficient is reachable from the plain CLT
with continuity correction, and the Edgeworth term is inert rather than load-bearing. The remaining
analytic obligation would then be a SUMMED Berry-Esseen statement,
    sum_l [ P(A_l <= k-1) - Phi(z_l) ] = O(M^-1),
for hypergeometric CDFs along a linear boundary. Pointwise Berry-Esseen for sampling without
replacement is classical (Hoeglund 1978); the summed refinement is the work. That is a different
and more standard obligation than bounding an Edgeworth expansion uniformly in t.

SCOPE. Atom mixture only -- the model with rho_I(t) == q, hence rho_I' = 0. This exercises the
second term of Proposition 1 alone and says nothing about the derivative term behind Corollary 3.
"""

from __future__ import annotations

import numpy as np
from scipy.special import ndtr
from scipy.stats import binom, hypergeom

M_CLUSTER, Q_ATOM, WEIGHT_FLOOR = 4, 0.30, 1e-18


def EL_exact(M: int, i: int, m: int, k: int) -> float:
    """E[L] from the identity: exact hypergeometric CDFs, no approximation."""
    ell = np.arange(M + 1)
    return float(np.sum(hypergeom.cdf(np.floor((k - 1 - ell) / (m - 1)), M, i, ell)))


def EL_normal(M: int, i: int, m: int, k: int) -> float:
    """The same sum with the hypergeometric CDF replaced by a continuity-corrected normal.
    No skewness term, no Edgeworth correction of any kind."""
    ell = np.arange(M + 1, dtype=float)
    theta = i / M
    mean_A = ell * (1.0 + (m - 1) * theta)
    var_R = (ell * theta * (1 - theta) * (M - ell) / (M - 1)) if M > 1 else np.zeros_like(ell)
    sd_A = (m - 1) * np.sqrt(np.maximum(var_R, 0.0))
    z = np.divide(k - 1 + 0.5 - mean_A, sd_A, out=np.zeros_like(ell), where=sd_A > 0)
    z = np.where(sd_A > 0, z, np.where(mean_A <= k - 1, np.inf, -np.inf))
    return float(np.sum(ndtr(z)))


def EC(b: int, m: int, q: float, k: int, el_fn) -> float:
    i_all = np.arange(b + 1)
    w_all = binom.pmf(i_all, b, q)
    keep = w_all > WEIGHT_FLOOR
    tot = 0.0
    for i, w in zip(i_all[keep], w_all[keep]):
        i = int(i)
        M = i + m * (b - i)
        tot += w * el_fn(M, i, m, k) / (M + 1)
    return tot / float(np.sum(w_all[keep]))


def part1() -> bool:
    print("[1] COST OF THE NORMAL SUBSTITUTION IN E[L], at fixed atom count i = round(q*b).")
    print("    E[C|i] = E[L]/(M+1), so an error of c/M in E[L] is c/M^2 in E[C] -- inside")
    print("    Proposition 1's O(n^-2) remainder. 'err x M' bounded is therefore the pass.")
    print(f"{'b':>6}{'n':>7}{'M':>7}{'E[L] exact':>16}{'E[L] normal':>16}"
          f"{'err':>12}{'err x M':>11}")
    rows = []
    for b in (25, 50, 100, 200, 400, 800, 1600):
        m, n = M_CLUSTER, b * M_CLUSTER
        k = int(round(0.9 * (n + 1)))
        i = int(round(Q_ATOM * b))
        M = i + m * (b - i)
        ex, no = EL_exact(M, i, m, k), EL_normal(M, i, m, k)
        rows.append((M, no - ex))
        print(f"{b:>6}{n:>7}{M:>7}{ex:>16.6f}{no:>16.6f}{no - ex:>12.3e}{(no - ex) * M:>11.3f}")
    Ms = np.array([r[0] for r in rows], float)
    es = np.abs(np.array([r[1] for r in rows], float))
    slope = np.polyfit(np.log(Ms), np.log(es), 1)[0]
    ok = slope < -0.9
    print(f"\n    error scales as M^({slope:.2f}); need M^-1 or steeper   "
          f"{'PASS' if ok else 'FAIL'}")
    print(f"    err x M converges to ~{rows[-1][1] * rows[-1][0]:.3f}, a definite constant")
    return ok


def part2() -> bool:
    print("\n[2] THE DRIFT, carried through the full binomial mixture over atom counts.")
    print("    If the normal route reaches Proposition 1 with its own error inside the")
    print("    remainder, the Edgeworth term is inert rather than load-bearing.")
    print(f"{'b':>6}{'n':>7}{'drift exact':>15}{'drift normal':>15}{'predicted':>14}"
          f"{'ratio nrm':>11}{'exact-nrm':>12}{'x n^2':>10}")
    ns, diffs = [], []
    for b in (25, 50, 100, 200, 400, 800):
        m, n = M_CLUSTER, b * M_CLUSTER
        k = int(round(0.9 * (n + 1)))
        p = k / (n + 1)
        d_ex = EC(b, m, Q_ATOM, k, EL_exact) - p
        d_no = EC(b, m, Q_ATOM, k, EL_normal) - p
        pred = -(m - 1) * (2 * p - 1) * Q_ATOM / (2 * n)
        ns.append(n)
        diffs.append(d_ex - d_no)
        print(f"{b:>6}{n:>7}{d_ex:>15.6e}{d_no:>15.6e}{pred:>14.6e}"
              f"{d_no / pred:>11.4f}{d_ex - d_no:>12.3e}{(d_ex - d_no) * n * n:>10.4f}")
    slope = np.polyfit(np.log(np.array(ns, float)),
                       np.log(np.abs(np.array(diffs, float))), 1)[0]
    ok = slope < -1.9
    print(f"\n    exact-minus-normal scales as n^({slope:.2f}); Proposition 1 claims O(n^-2)   "
          f"{'PASS' if ok else 'FAIL'}")
    return ok


def main() -> int:
    print("SW-12 / is Proposition 1's Edgeworth step load-bearing or inert?  "
          f"atom mixture, m={M_CLUSTER}, q={Q_ATOM}\n")
    ok = part1()
    ok &= part2()
    print()
    if ok:
        print("VERDICT: INERT. The plain continuity-corrected normal reaches Proposition 1's")
        print("coefficient, and its own error lands inside the claimed O(n^-2) remainder. The")
        print("skewness term therefore only has to NOT CONTRIBUTE at O(1/n) -- which is what")
        print("the sketch's int phi(z)(z^2-1) dz = 0 says -- rather than to be expanded with a")
        print("bounded remainder. The remaining obligation is a SUMMED Berry-Esseen bound,")
        print("sum_l [P(A_l <= k-1) - Phi(z_l)] = O(M^-1), for hypergeometric CDFs along a")
        print("linear boundary. Pointwise is classical (Hoeglund 1978); summed is the work.")
    else:
        print("VERDICT: the normal route does NOT suffice; the Edgeworth term is load-bearing.")
    print()
    print("STILL NOT A PROOF, and still atom-mixture only: rho_I' = 0 here, so the derivative")
    print("term behind Corollary 3's sign claim is untouched. SW-12 stays open.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
