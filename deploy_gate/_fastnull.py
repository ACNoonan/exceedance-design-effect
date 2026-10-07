"""Vectorised one-way ICC for a BINARY indicator, for permutation nulls only.

Why this exists, and why it is not a second estimator
----------------------------------------------------
`experiments/_icc.py` is the spec: it is pinned by `test_icc_golden.py` and every published number
comes from it. But its `ssw` is a Python loop over clusters, and a permutation null at 9,400 clusters
× 1,000 draws × 5 levels × 5 prefix lengths is ~25,000 calls — hours, not minutes.

For a **binary** y the ANOVA sums have a closed form in the per-cluster counts, so the whole thing is
two `bincount` calls:

    sum_i y_ij^2 = c_j          (because y in {0,1})
    ssw_j        = c_j - c_j^2 / n_j
    ssb          = sum_j n_j (c_j/n_j - ybar)^2

`assert_matches_spec` is called before any null is computed and compares this path against
`_icc.py::icc_oneway` on the *observed* data. If they ever disagree the run stops. That is the
difference between an optimisation and a second, silently-diverging implementation of the same
quantity — which is the exact failure `_icc.py`'s own docstring was written about.
"""
from __future__ import annotations

import numpy as np


class Fast:
    """Precomputed cluster geometry for one fixed size profile."""

    def __init__(self, codes: np.ndarray, n_groups: int | None = None):
        self.codes = np.asarray(codes)
        self.b = int(self.codes.max()) + 1 if n_groups is None else int(n_groups)
        self.sizes = np.bincount(self.codes, minlength=self.b).astype(float)
        keep = self.sizes > 0
        self.k = int(keep.sum())
        self.n = float(self.sizes.sum())
        self.sizes_safe = np.where(keep, self.sizes, 1.0)   # avoid 0-division on empty codes
        self.keep = keep
        sum_sq = float((self.sizes**2).sum())
        self.m_tilde = sum_sq / self.n
        self.m0 = (self.n - sum_sq / self.n) / (self.k - 1)

    def rho(self, y: np.ndarray) -> float:
        # General form: ssw_j = sum(y^2)_j - (sum y_j)^2 / n_j. For a 0/1 indicator this reduces to
        # c_j - c_j^2/n_j, but it is written generally on purpose — `deploygate/T-06` feeds
        # answerability-residualised values, which are NOT binary, and the binary shortcut would
        # have been silently wrong for them. (`assert_matches_spec` would have caught it as a crash;
        # correctness is better than a crash.)
        c = np.bincount(self.codes, weights=y, minlength=self.b)
        cc = np.bincount(self.codes, weights=y * y, minlength=self.b)
        ybar = float(y.sum() / self.n)
        means = np.where(self.keep, c / self.sizes_safe, 0.0)
        ssb = float((self.sizes * (means - ybar) ** 2).sum())
        ssw = float((np.where(self.keep, cc - c**2 / self.sizes_safe, 0.0)).sum())
        msb = ssb / (self.k - 1)
        msw = ssw / (self.n - self.k)
        denom = msb + (self.m0 - 1) * msw
        return float("nan") if denom == 0 else (msb - msw) / denom

    def null(self, y: np.ndarray, n_perm: int, rng: np.random.Generator) -> dict:
        """Permute the indicator, holding the size profile and the marginal exactly fixed.

        Reports the 95th percentile as well as the mean: a permuted mean of +0.0002 once hid a
        +0.06 fluke in this program, so the bar a measurement clears is the tail, not the centre.
        """
        out = np.empty(n_perm)
        yp = y.copy()
        for i in range(n_perm):
            rng.shuffle(yp)
            out[i] = self.rho(yp)
        return {
            "mean": float(np.nanmean(out)),
            "p95": float(np.nanpercentile(out, 95)),
            "max": float(np.nanmax(out)),
        }


def assert_matches_spec(y: np.ndarray, codes: np.ndarray, spec_rho: float, tol: float = 1e-9) -> Fast:
    """Build a `Fast` and prove it reproduces `_icc.py` on this exact input, or raise."""
    f = Fast(codes)
    got = f.rho(np.asarray(y, dtype=float))
    if not (abs(got - spec_rho) <= tol or (np.isnan(got) and np.isnan(spec_rho))):
        raise AssertionError(
            f"fast binary ICC {got!r} != spec icc_oneway {spec_rho!r} (tol {tol}). "
            "The null path and the measurement path have diverged; refusing to report a null."
        )
    return f
