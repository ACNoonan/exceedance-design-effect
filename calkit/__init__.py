"""calkit — a calibration toolbox, grown one earned function per lesson.

Nothing here is a black box you imported. Every function was typed by hand in a
lesson, after building the intuition by simulation and watching it break.

    EXCEPTIONS, recorded so the sentence above stays true:
      · metrics.py (L1) — written out by Claude Code 2026-07-25 at Adam's request while
        moving fast on the research lanes. Verified against L1's pre-registered
        falsification case, but read rather than derived. See its PROVENANCE block.
      · conformal.split_conformal (L2) — written out by Claude Code 2026-07-26 at Adam's
        request, to unblock regeneration of the SW-02 paper's tables. This is the
        guarantee-bearing line the README singles out as one to type by hand, so the
        exception is the most expensive one on this list. Reversible: retype it and
        experiments/_conformal.py::check_agrees_with_calkit() proves the two identical.
      · _scaffold.py — provided by design; standard statistics, not calibration concepts.

    Keep this list short. If it grows, the package has stopped being what it claims.

Modules fill in over the course:
    metrics.py     L1   brier, ece, reliability_table
    distributional L1b  pit, crps
    conformal.py   L2-4 split_conformal, cqr, mondrian
    adaptive.py    L5   aci
    selective.py   L6-7 selective, llm_gate
    risk.py        L8   risk_control
"""

__version__ = "0.0.0"
