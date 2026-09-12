"""Mode 2 — effective sample size from a published pass@k spectrum alone.

With K trials per item, `accuracy` (= pass@1) and pass@2..pass@K determine the full
per-item success-count distribution f_0..f_K exactly: six equations, six unknowns at
K = 5. From f the between-item variance, the balanced one-way ICC, DEFF and n_eff all
follow — no per-trial data, no API key, no maintainer cooperation.

Lifted from `calibrating-benchmarks/lanes/2026-08-02-benchmark-saturation/tb21_reconstruct.py`
(validated end to end against 32,778 real per-trial outcomes, worst |Δ ICC| 0.00042) with
three deliberate changes:

- K is an argument, not a module constant;
- everything is on the FRACTION scale (the TB 2.1 lane worked in percent);
- degenerate ICC denominators return NaN, matching `_icc.icc_oneway`'s contract, where the
  lane returned 0.0. NaN is the honest answer: a zero-variance board has no estimable ICC.

Identifiability: the linear system is square only when the full spectrum pass@1..pass@K is
supplied. With fewer rows `recover_counts` still returns the least-squares solution on the
simplex, but it is not unique; check `well_determined` before quoting the result.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb, sqrt

import numpy as np
from scipy.optimize import lsq_linear

from ._icc import IccResult

__all__ = [
    "PassKResult",
    "pass_at_k_row",
    "recover_counts",
    "passk_icc",
    "published_se",
    "task_se",
    "analyze_passk_spectrum",
]


def pass_at_k_row(K: int, k: int) -> np.ndarray:
    """P(a random k-subset of the K trials contains >= 1 success | item has c successes),
    for c = 0..K. That is 1 - C(K-c, k)/C(K, k); 1.0 whenever K - c < k."""
    return np.array(
        [1.0 - (comb(K - c, k) / comb(K, k) if K - c >= k else 0.0) for c in range(K + 1)]
    )


def recover_counts(pass_at: dict[int, float], K: int) -> tuple[np.ndarray, float, bool]:
    """Solve for f_0..f_K from a pass@k spectrum, constrained to the simplex.

    `pass_at` maps k -> pass@k as a FRACTION in [0, 1]. pass@1 is the accuracy.
    Returns (f, residual_cost, well_determined). `well_determined` is True iff all of
    pass@1..pass@K were supplied, which makes the system square (rank K + simplex row).
    """
    ks = sorted(pass_at)
    if not ks or ks[0] < 1 or ks[-1] > K:
        raise ValueError(f"pass_at keys must lie in 1..K={K}, got {ks}")
    A = np.vstack([pass_at_k_row(K, k) for k in ks] + [np.ones(K + 1)])
    b = np.array([float(pass_at[k]) for k in ks] + [1.0])
    r = lsq_linear(A, b, bounds=(0.0, 1.0))
    f = np.clip(r.x, 0.0, None)
    return f / f.sum(), float(r.cost), len(ks) == K


def passk_icc(f: np.ndarray, K: int, n_items: int) -> IccResult:
    """Balanced one-way ANOVA ICC on the binary trial outcomes, computed purely from f.

    Balanced design: every item has exactly K trials, so m0 = m_tilde = m_bar = K and
    DEFF = 1 + (K - 1) * rho exactly.
    """
    f = np.asarray(f, dtype=float)
    p = np.arange(K + 1) / K
    counts = f * n_items
    pbar = float((f * p).sum())
    ssb = K * float((counts * (p - pbar) ** 2).sum())
    msb = ssb / (n_items - 1) if n_items > 1 else float("nan")
    ssw = float((counts * K * p * (1 - p)).sum())
    msw = ssw / (n_items * (K - 1)) if K > 1 else float("nan")
    denom = msb + (K - 1) * msw
    rho = (msb - msw) / denom if denom and np.isfinite(denom) else float("nan")
    return IccResult(
        rho=rho,
        m0=float(K),
        m_tilde=float(K),
        m_bar=float(K),
        k=int(n_items),
        n=int(n_items * K),
        n_singleton=0,
        msb=msb,
        msw=msw,
        clipped=False,
    )


def published_se(f: np.ndarray, K: int, n_items: int) -> float:
    """The within-item-only SE formula boards like TB 2.1 publish (fraction scale).

    Carries NO between-item variance and shrinks to 0 as trials grow; reproduced here so a
    recovered f can be checked against a board's own stderr before anything else is quoted.
    """
    f = np.asarray(f, dtype=float)
    p = np.arange(K + 1) / K
    counts = f * n_items
    var = float((counts * p * (1 - p) / (K - 1)).sum()) / (n_items**2)
    return sqrt(var)


def task_se(f: np.ndarray, K: int, n_items: int) -> float:
    """SE of the mean per-item rate when ITEMS are resampled (fraction scale)."""
    f = np.asarray(f, dtype=float)
    p = np.arange(K + 1) / K
    mean = float((f * p).sum())
    var_between = float((f * (p - mean) ** 2).sum())
    return sqrt(var_between / n_items)


@dataclass(frozen=True)
class PassKResult:
    """Everything mode 2 can say about a board from its published spectrum."""

    f: np.ndarray            # recovered success-count distribution, f_0..f_K
    icc: IccResult           # balanced ICC; .deff() and .n_eff() follow
    residual: float          # lsq residual of the inversion
    well_determined: bool    # full spectrum supplied?
    published_se: float      # the board's own (within-item) SE, rebuilt from f
    task_se: float           # the item-resampled SE
    dead_fraction: float     # f_0 + f_K: items contributing zero variance


def analyze_passk_spectrum(pass_at: dict[int, float], K: int, n_items: int) -> PassKResult:
    """One call from a published spectrum to the full mode-2 readout."""
    f, cost, ok = recover_counts(pass_at, K)
    res = passk_icc(f, K, n_items)
    return PassKResult(
        f=f,
        icc=res,
        residual=cost,
        well_determined=ok,
        published_se=published_se(f, K, n_items),
        task_se=task_se(f, K, n_items),
        dead_fraction=float(f[0] + f[K]),
    )
