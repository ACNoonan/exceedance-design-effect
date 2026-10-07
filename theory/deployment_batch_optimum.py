#!/usr/bin/env python3
"""Optimal deployment batch size from Kish's own cost model — an IMPORT, not a new result.

WHAT THIS IS. Kish (1965) §8.3B derives the most economical subsample size per primary
cluster under the linear cost model C = nc + a*C_a, where a is the number of primary
clusters, c the cost per element and C_a the cost per cluster:

    optimum b = sqrt( (C_a/c) * (1 - roh) / roh )                      Kish (1965) eq. 8.3.7

with `roh` his term for the intraclass correlation. The variance it minimises is his
two-stage decomposition (eq. 5.6.8), whose components are ADDITIVE across stages —
a first-stage term over the number of clusters plus a second-stage term over the total:

    Var(ybar) = S_a^2 / a  +  (1 - b/B) S_b^2 / (ab)                   Kish (1965) eq. 5.6.8

and equivalently Var(ybar) = (S^2/n)[1 + roh(b-1)] = (S^2/n)[(1-roh) + roh*b], eq. 5.4.1,
which is where `deff` and "effective n" are defined in the first place.

WHY IT IS HERE. §8's items 1-12 price the CALIBRATION side. A practitioner who deploys a
threshold on a whole cluster of test points at once — one question's entire beam — averages
a clustered proportion, and that average carries its own variance component. Kish's formula
answers "how many test points per question is it worth collecting" in closed form. Nothing
in this script is new; the contribution is noticing that the deployment side has the same
shape as the calibration side and that the answer was published in 1965.

THE CHECK THAT COULD HAVE FAILED, AND DID NOT. The formula is implemented here and used to
reproduce EIGHT published cells from two independent secondary sources that both attribute
it to Kish §8.3.b — Kalton, Brick & Le (2005) ch. VI para. 71 (C*=16, rho=0.05 -> 17.4) and
UN ch. II Table II.2 (seven cost-ratio x rho cells). If the implementation had the ratio
inverted, the square root misplaced, or roh and 1-roh swapped, not one of the eight would
land. A direction check is also run: b_opt must INCREASE as roh falls, since weaker
clustering makes deep subsampling worthwhile. Both are printed below as PASS/FAIL.

    python3 deployment_batch_optimum.py > deployment_batch_optimum_RESULTS.txt
"""
from __future__ import annotations

import math

# CA-14 / CA-15 — the released PRM calibration set, already in the claims ledger.
RHO_I_RELEASED = 0.495
M_TILDE_RELEASED = 61.29


def b_opt(cost_ratio: float, roh: float) -> float:
    """Kish (1965) eq. 8.3.7. cost_ratio = C_a/c, the cost of a cluster over an element."""
    if not 0.0 < roh < 1.0:
        raise ValueError(f"roh must lie strictly in (0,1); got {roh}")
    return math.sqrt(cost_ratio * (1.0 - roh) / roh)


def main() -> None:
    print("=" * 78)
    print("OPTIMAL DEPLOYMENT BATCH SIZE — Kish (1965) eq. 8.3.7, applied to the test side")
    print("=" * 78)

    print("\n--- PRECONDITION 1: reproduce Kalton, Brick & Le (2005) ch.VI para.71 ---")
    print("    They publish: C* = 16, rho = 0.05  ->  b_opt = 17.4")
    got = b_opt(16, 0.05)
    ok1 = abs(got - 17.4) < 0.05
    print(f"    computed {got:.4f}   {'PASS' if ok1 else 'FAIL'}")
    print("    WOULD HAVE FAILED IF: the cost ratio were inverted (b_opt would be 1.09),")
    print("    or roh and 1-roh swapped (b_opt would be 0.92).")
    print(f"    inverted-ratio value  = {b_opt(1 / 16, 0.05):.4f}  (does NOT match 17.4)")
    print(f"    swapped-roh    value  = {math.sqrt(16 * 0.05 / (1 - 0.05)):.4f}  (does NOT match 17.4)")

    print("\n--- PRECONDITION 2: reproduce UN ch.II Table II.2, seven published cells ---")
    cells = [(4, 0.01, 20), (25, 0.01, 50), (16, 0.02, 28),
             (4, 0.05, 9), (9, 0.05, 13), (16, 0.05, 17), (25, 0.05, 22)]
    ok2 = True
    print(f"    {'C*':>5} {'rho':>6} {'computed':>9} {'published':>10}  result")
    for cs, r, pub in cells:
        v = b_opt(cs, r)
        hit = abs(v - pub) <= 0.6          # published values are rounded to integers
        ok2 &= hit
        print(f"    {cs:5d} {r:6.2f} {v:9.2f} {pub:10d}  {'PASS' if hit else 'FAIL'}")
    print(f"    all seven: {'PASS' if ok2 else 'FAIL'}")

    print("\n--- PRECONDITION 3: direction. b_opt must RISE as roh falls ---")
    prev, ok3 = None, True
    for r in (0.9, 0.5, 0.1, 0.01, 0.001):
        v = b_opt(16, r)
        mono = prev is None or v > prev
        ok3 &= mono
        print(f"    roh={r:<7} b_opt={v:8.2f}  increasing={mono}")
        prev = v
    print(f"    monotone: {'PASS' if ok3 else 'FAIL'}")

    print("\n" + "=" * 78)
    print("ILLUSTRATION — equal cluster sizes, using rho_I = 0.495 (CA-14)")
    print("=" * 78)
    factor = math.sqrt((1 - RHO_I_RELEASED) / RHO_I_RELEASED)
    print(f"\n    sqrt((1-roh)/roh) = {factor:.4f}, so optimum M = {factor:.2f} * sqrt(C*)")
    print(f"\n    {'cost ratio C*':>14} {'optimum M':>12}")
    for cs in (1, 4, 16, 64, 256, 1024):
        print(f"    {cs:14d} {b_opt(cs, RHO_I_RELEASED):12.2f}")

    justify = M_TILDE_RELEASED ** 2 * RHO_I_RELEASED / (1 - RHO_I_RELEASED)
    print(f"\n    The released size-biased mean is {M_TILDE_RELEASED}; the ordinary mean is 50.06.")
    print(f"    Illustrative equal-size cost ratio at M = {M_TILDE_RELEASED}: C* = {justify:.0f}")
    print(f"    This does not establish an optimum for the observed ragged allocation.")

    print("\n--- HEADLINE ---")
    print(f"    optimum deployment batch = {factor:.2f} * sqrt(C*)")
    print(f"    Equal-size illustration at M = {M_TILDE_RELEASED}: C* = {justify:.0f}")
    print(f"    at C* = 16, optimum M = {b_opt(16, RHO_I_RELEASED):.2f}")

    allok = ok1 and ok2 and ok3
    print(f"\n=== PRECONDITIONS 3/3 {'PASS' if allok else 'FAIL'} ===")
    if not allok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
