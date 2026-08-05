"""Research-side conformal primitives. NOT the earned library.

Why this exists as a duplicate rather than an import
-----------------------------------------------------
`calkit.conformal.split_conformal` is a Lesson-2 exercise Adam types himself; it is deliberately
left as a stub. Research work cannot block on a lesson, and a lesson cannot be pre-empted by
research needing its answer. So the two live separately, exactly as STRUCTURE.md prescribes:

    "If both need the same helper, it belongs in calkit — and if it isn't earned enough to live
     there, duplicate it rather than reaching across."

This is the research copy. It is written out, it is not an earned function, and it must never be
imported by anything under `lessons/`.

**Consistency check:** once L2 lands, `check_agrees_with_calkit()` asserts the two implementations
return identical thresholds on random inputs. If they ever disagree, one of them is wrong and every
number in the SW-02 draft is suspect.
"""

from __future__ import annotations

import numpy as np


def split_conformal(cal_scores, alpha: float) -> float:
    """The ceil((n+1)(1-alpha))-th smallest calibration score.

    Sorted order statistic, not an interpolated quantile: the guarantee is a statement about
    ranks, and interpolating between two calibration scores invents a value no data point had.

    Returns +inf when ceil((n+1)(1-alpha)) > n, i.e. when n is too small to support the requested
    coverage at all. Covering everything is the honest response; clipping to the maximum silently
    reports a threshold whose coverage is unknown.
    """
    s = np.sort(np.asarray(cal_scores, dtype=float))
    n = s.size
    if n == 0:
        raise ValueError("empty calibration set")
    if not 0.0 < alpha < 1.0:
        raise ValueError(f"alpha must be in (0,1); got {alpha}")
    k = int(np.ceil((n + 1) * (1.0 - alpha)))
    return float("inf") if k > n else float(s[k - 1])


def nominal_rank_coverage(n: int, alpha: float) -> float:
    """k/(n+1) — the coverage the discrete rank actually targets, which is not 1-alpha.

    Separating this from 1-alpha matters when measuring drift: part of any observed gap is pure
    ceiling discreteness and is present even under perfect exchangeability.
    """
    k = int(np.ceil((n + 1) * (1.0 - alpha)))
    return k / (n + 1)


def check_agrees_with_calkit(n_trials: int = 200, seed: int = 0) -> bool:
    """Assert the research copy and the earned copy agree. Run after L2 lands."""
    from calkit.conformal import split_conformal as earned

    rng = np.random.default_rng(seed)
    for _ in range(n_trials):
        n = int(rng.integers(3, 300))
        alpha = float(rng.uniform(0.01, 0.5))
        s = rng.normal(size=n)
        a, b = split_conformal(s, alpha), earned(s, alpha)
        if not (a == b or (np.isinf(a) and np.isinf(b))):
            raise AssertionError(f"MISMATCH n={n} alpha={alpha:.4f}: research={a} earned={b}")
    return True
