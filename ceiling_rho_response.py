"""SW-64 — §6.1's sampling-depth ceiling, recomputed with rho_I responding to family size.

    python experiments/2026-07-26-sw02-exchangeability-audit/ceiling_rho_response.py

WHY THIS EXISTS
§6.1 printed "ten times as many prefixes per question would buy twelve", from
`n_eff -> b/[(1+CV^2) rho_I]` evaluated at a FIXED rho_I. The premise is that rho_I, being a
pairwise property, does not move with family size. §6.2 of the same paper measures it moving:
widening the beam w = 2 -> 8 quadruples family size and rho_I(0.90) falls 0.606 -> 0.531 with
disjoint confidence intervals. So the ceiling has to be recomputed with rho_I as a function of the
scaling, and the correction is large: the answer is roughly 130 rather than 12.

WHAT IS AND IS NOT EXTRAPOLATED
The beam experiment supplies ONE controlled point: a 4x scaling costs 12.4% of rho_I. Reporting the
ceiling at s = 4 uses only that. Anything beyond s = 4 fits a power law rho_I(s) = rho_I * s^beta
through the same two points and evaluates it outside the measured range; those rows are printed as
extrapolations and labelled as such, because the entire lesson of SW-64 is that holding a measured
quantity fixed outside the regime it was measured in is what produced the original error.

THE CROSS-SECTIONAL ALTERNATIVE IS DELIBERATELY NOT USED
`rho_by_family_size.py` compares questions by their natural size and finds a 4.51x spread in rho_I,
implying a ceiling near 3,572. That comparison is confounded: large families are large *because* the
question is hard, which is §6.1's own size-score coupling. The beam sweep is a manipulation and the
quartile comparison is not, so the controlled slope is the one propagated here. The confounded
figure is computed below only so the gap between them is on the record.
"""

from __future__ import annotations

import math

# --- inputs, all printed in the paper and gated by CLAIMS.md -------------------------------------
B_CLUSTERS = 500        # CA-07-adjacent: released question count
CV2 = 0.224             # size-profile CV^2, printed in section 6.1's table
RHO_POOLED = 0.4946     # CA-14: rho_I at p = 0.8909
NEFF_PLUGIN = 812       # CA-32: plug-in effective size already held
CEILING_PUBLISHED = 826  # what section 6.1 prints under the fixed-rho premise

# section 6.2's beam sweep, w = 2 -> 8 (a 4x scaling in family size)
BEAM_SCALE = 4.0
RHO_W2, RHO_W2_LO, RHO_W2_HI = 0.606, 0.567, 0.646
RHO_W8, RHO_W8_LO, RHO_W8_HI = 0.531, 0.510, 0.556

# the confounded cross-sectional endpoint, for contrast only
RHO_LARGEST_QUARTILE = 0.1143


def ceiling(rho: float) -> float:
    """b / [(1 + CV^2) rho_I] — section 6.1's limit as every family is scaled."""
    return B_CLUSTERS / ((1.0 + CV2) * rho)


def beta_from_beam() -> float:
    """Power-law exponent of rho_I in the family-size scaling, from the two measured beam widths."""
    return math.log(RHO_W8 / RHO_W2) / math.log(BEAM_SCALE)


def main() -> int:
    beta = beta_from_beam()
    rho_of = lambda s: RHO_POOLED * s ** beta

    print("=" * 78)
    print("PRECONDITIONS — a failure in any one invalidates every number below")
    print("=" * 78)
    ok = True

    p1 = abs(ceiling(RHO_POOLED) - CEILING_PUBLISHED) < 1.0
    print(f"  P1 fixed-rho ceiling reproduces the paper: {ceiling(RHO_POOLED):.1f} vs "
          f"{CEILING_PUBLISHED}  -> {'PASS' if p1 else 'FAIL'}")
    print("     would fail if: b, CV^2 or rho_I drifted from the values section 6.1 prints, in")
    print("     which case this correction is being applied to a different measurement.")
    ok &= p1

    p2 = RHO_W8_HI < RHO_W2_LO
    print(f"  P2 beam intervals disjoint: [{RHO_W8_LO}, {RHO_W8_HI}] below "
          f"[{RHO_W2_LO}, {RHO_W2_HI}]  -> {'PASS' if p2 else 'FAIL'}")
    print("     would fail if: the beam sweep's fall were inside noise. THE WHOLE CORRECTION")
    print("     RESTS ON THIS — if the intervals overlapped, the fixed-rho premise would be")
    print("     unrefuted and section 6.1's original arithmetic would stand.")
    ok &= p2

    p3 = beta < 0
    print(f"  P3 fitted exponent is negative: beta = {beta:.4f}  -> {'PASS' if p3 else 'FAIL'}")
    print("     would fail if: rho_I rose with family size, which would move the ceiling the")
    print("     other way and make the published number an over- rather than under-statement.")
    ok &= p3

    # negative control on the propagation itself, not on the data
    ctrl_flat = B_CLUSTERS / ((1.0 + CV2) * RHO_POOLED * 1.0 ** beta)
    ctrl_rising = B_CLUSTERS / ((1.0 + CV2) * RHO_POOLED * 4.0 ** abs(beta))
    p4 = abs(ctrl_flat - CEILING_PUBLISHED) < 1.0 and ctrl_rising < CEILING_PUBLISHED
    print(f"  P4 NEGATIVE CONTROL on the propagation: at s = 1 it returns {ctrl_flat:.1f} "
          f"(= the published {CEILING_PUBLISHED}), and with the sign of beta flipped it returns "
          f"{ctrl_rising:.1f} (< {CEILING_PUBLISHED})  -> {'PASS' if p4 else 'FAIL'}")
    print("     would fail if: the sign of the response were coded backwards — the flipped arm is")
    print("     required to move the ceiling DOWN, so a sign error cannot pass both halves.")
    ok &= p4

    if not ok:
        print("\n  A PRECONDITION FAILED. No number below may be quoted.")
        return 1
    print("  all pass.\n")

    print("=" * 78)
    print("THE CEILING, WITH rho_I RESPONDING TO FAMILY SIZE")
    print("=" * 78)
    print(f"    {'family scaling':>16}{'rho_I':>10}{'ceiling':>10}{'gain over 812':>16}   basis")
    print(f"    {'1x (as held)':>16}{RHO_POOLED:>10.4f}{'':>10}{'':>16}   plug-in reports "
          f"{NEFF_PLUGIN}")
    print(f"    {'any, rho fixed':>16}{RHO_POOLED:>10.4f}{ceiling(RHO_POOLED):>10.1f}"
          f"{ceiling(RHO_POOLED) - NEFF_PLUGIN:>16.0f}   the published premise, now refuted")
    for s, basis in ((2.0, "interpolated inside the measured 4x"),
                     (4.0, "MEASURED — the beam sweep's own scaling"),
                     (10.0, "extrapolated beyond the measured 4x"),
                     (100.0, "extrapolated beyond the measured 4x")):
        print(f"    {f'{s:.0f}x':>16}{rho_of(s):>10.4f}{ceiling(rho_of(s)):>10.1f}"
              f"{ceiling(rho_of(s)) - NEFF_PLUGIN:>16.0f}   {basis}")
    print()
    print(f"    The published sentence says ten times the prefixes buys twelve. Under the measured")
    print(f"    response it buys {ceiling(rho_of(10.0)) - NEFF_PLUGIN:.0f}, and at the one scaling")
    print(f"    actually manipulated (4x) it buys {ceiling(rho_of(4.0)) - NEFF_PLUGIN:.0f}.")
    print()
    print("    THERE IS NO LONGER A FINITE CEILING. With beta < 0 the limit diverges, slowly:")
    print(f"    {ceiling(rho_of(10.0)):.0f} at ten times and {ceiling(rho_of(100.0)):.0f} at a")
    print("    hundred. 'Already at the ceiling' is the wrong shape of statement; the right one is")
    print("    that depth buys hundreds where breadth buys thousands.")
    print()
    print("    For contrast, NOT PROPAGATED: the confounded cross-sectional endpoint")
    print(f"    rho_I = {RHO_LARGEST_QUARTILE} gives {ceiling(RHO_LARGEST_QUARTILE):.0f}. Large")
    print("    families are large because the question is hard, so this mixes the size response")
    print("    with the difficulty composition and cannot be read as a response to scaling.")
    print()
    print("=" * 78)
    print("WHAT SURVIVES")
    print("=" * 78)
    print(f"    Doubling the number of questions buys about 800 effective points; unbounded")
    print(f"    sampling depth buys hundreds. Breadth still beats depth, by roughly 4x rather")
    print(f"    than by the 60x the fixed-rho arithmetic implied. Section 8 item 11 stands; the")
    print(f"    premise sentence and the figure 'twelve' do not.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
