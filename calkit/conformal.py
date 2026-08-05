"""Distribution-free prediction — Lessons 2–4.

Contract shared with the notebooks:
    scores  : array-like of floats — nonconformity scores, higher = weirder
    alpha   : float in (0, 1)      — target miscoverage, so coverage is 1 - alpha

Pre-registration / lesson: lessons/02-split-conformal.ipynb
"""

from __future__ import annotations

import numpy as np


def split_conformal(cal_scores, alpha: float) -> float:
    """The threshold above which a new point counts as a violation.

        q = the ⌈(n + 1)(1 - alpha)⌉-th smallest of the n calibration scores

    Return that value. Any test point whose score is ≤ q is "covered".

    WHY THE +1, AND WHY A RANK AT ALL — this is the whole lesson
    -------------------------------------------------------------
    You have n calibration points and 1 test point: n + 1 in total. **If all n + 1 are
    exchangeable, the test point's score is equally likely to hold any rank among them**
    — it cannot prefer a rank, because nothing distinguishes it from the others.

    So P(test score lands above the k-th smallest) = (n + 1 - k) / (n + 1). Choosing
    k = ⌈(n + 1)(1 - alpha)⌉ makes that ≤ alpha, which is the guarantee. No distribution
    is assumed anywhere. No model is assumed anywhere. The only input is *the new point
    is not special*.

    That is also the entire failure mode: everything that breaks conformal prediction
    breaks it by making the new point special.

    Practical notes
    ---------------
    - If ⌈(n + 1)(1 - alpha)⌉ > n, the data cannot support that alpha at all — n is too
      small for the requested coverage. Return +inf (cover everything) rather than
      silently clipping to the max, and say so. This is the honest version of "you
      don't have enough calibration data", and it is the same impossibility Chow (1970)
      describes from the other direction.
    - Use `np.sort` and index, not `np.quantile` with a default interpolation. The
      guarantee is about an *order statistic*; interpolating between two calibration
      scores invents a value no data point had and quietly breaks the rank argument.

    PROVENANCE — read this before trusting the package's claim about itself
    ----------------------------------------------------------------------
    This function was **written out by Claude Code on 2026-07-26 at Adam's request**, to
    unblock regeneration of the SW-02 paper's tables. It was NOT hand-typed in Lesson 2.
    It is recorded in the exceptions list in `calkit/__init__.py`.

    The house rule it bypasses exists for a reason, so the bypass is reversible by design:
    retype this body yourself and `experiments/_conformal.py::check_agrees_with_calkit()`
    will prove your version identical to this one on 200 random inputs. Until then, the
    SW-02 numbers regenerate from an AI-written line, which satisfies reproducibility but
    not the discipline the rule was protecting.
    """
    s = np.sort(np.asarray(cal_scores, dtype=float))
    n = s.size
    if n == 0:
        raise ValueError("empty calibration set")
    if not 0.0 < alpha < 1.0:
        raise ValueError(f"alpha must be in (0, 1); got {alpha}")
    k = int(np.ceil((n + 1) * (1.0 - alpha)))
    return float("inf") if k > n else float(s[k - 1])


def coverage(test_scores, threshold: float) -> float:
    """Fraction of test points at or below the threshold. Scaffolding — provided.

    This is the empirical check that split_conformal did what it claimed. Compare it
    against 1 - alpha; if it drifts below, either alpha was too ambitious for your n or
    exchangeability is broken.
    """
    s = np.asarray(test_scores, dtype=float)
    if s.size == 0:
        raise ValueError("empty test set")
    return float(np.mean(s <= threshold))
