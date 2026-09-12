"""The reporting layer — one call per input mode, one line out.

The line is the artifact: a string a paper or a leaderboard README can carry verbatim,
naming the resampled unit, the cluster count, the size-biased mean size, the dependence
at the statistic reported, and the count the data is actually worth.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

import numpy as np

from ._icc import IccResult, icc_oneway, rho_indicator
from .passk import PassKResult, analyze_passk_spectrum

__all__ = ["Report", "analyze_outcomes", "analyze_scores", "analyze_passk"]


@dataclass(frozen=True)
class Report:
    mode: str                 # "outcomes" | "scores" | "passk"
    unit: str                 # the resampled unit the clusters represent ("repo", "session", ...)
    res: IccResult
    level: Optional[float] = None      # operating level p, scores mode only
    extras: dict = field(default_factory=dict)

    @property
    def deff(self) -> float:
        return self.res.deff()

    @property
    def n_eff(self) -> float:
        return self.res.n_eff()

    def line(self) -> str:
        r = self.res
        rho_label = f"rho_I(p={self.level:g})" if self.level is not None else "rho"
        parts = [
            f"n={r.n}",
            f"clusters({self.unit})={r.k}",
            f"m_tilde={r.m_tilde:.1f}",
            f"{rho_label}={r.rho:.4f}",
            f"DEFF={self.deff:.2f}",
            f"n_eff={self.n_eff:.0f}",
        ]
        if r.n_singleton:
            parts.append(f"singletons={r.n_singleton}")
        if not self.extras.get("well_determined", True):
            parts.append("UNDERDETERMINED")
        return ", ".join(parts)

    def to_dict(self) -> dict:
        r = self.res
        d = {
            "mode": self.mode,
            "unit": self.unit,
            "n": r.n,
            "clusters": r.k,
            "m_bar": r.m_bar,
            "m_tilde": r.m_tilde,
            "rho": r.rho,
            "deff": self.deff,
            "n_eff": self.n_eff,
            "n_singleton": r.n_singleton,
            "level": self.level,
        }
        d.update({k: v for k, v in self.extras.items() if not isinstance(v, np.ndarray)})
        return d


def analyze_outcomes(outcomes, cluster_ids, *, unit: str = "cluster") -> Report:
    """Mode 1 — per-observation outcomes with cluster ids (mean target)."""
    res = icc_oneway(np.asarray(outcomes, dtype=float), cluster_ids)
    return Report(mode="outcomes", unit=unit, res=res)


def analyze_scores(
    scores, cluster_ids, *, level: float, threshold: Optional[float] = None,
    unit: str = "cluster",
) -> Report:
    """Mode 3 — scores with cluster ids at an operating level (threshold target).

    The dependence that governs a threshold is the ICC of the exceedance indicators at the
    level, not the score correlation. Pass `threshold` when calibration and deployment pools
    are separate; otherwise the threshold is the pooled empirical quantile at `level`.
    """
    res = rho_indicator(np.asarray(scores, dtype=float), cluster_ids, p=level, threshold=threshold)
    return Report(mode="scores", unit=unit, res=res, level=level)


def analyze_passk(pass_at: dict[int, float], K: int, n_items: int, *, unit: str = "item") -> Report:
    """Mode 2 — a board's published accuracy + pass@k spectrum, nothing else."""
    pk: PassKResult = analyze_passk_spectrum(pass_at, K, n_items)
    return Report(
        mode="passk",
        unit=unit,
        res=pk.icc,
        extras={
            "well_determined": pk.well_determined,
            "residual": pk.residual,
            "published_se": pk.published_se,
            "task_se": pk.task_se,
            "dead_fraction": pk.dead_fraction,
        },
    )
