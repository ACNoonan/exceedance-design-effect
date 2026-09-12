"""neff — how many independent observations does your evaluation have?

Three input modes, one readout (rho, m_tilde, DEFF, n_eff, and a reporting line):

- `analyze_outcomes(outcomes, cluster_ids)` — per-observation outcomes with cluster ids.
- `analyze_passk(pass_at, K, n_items)` — a leaderboard's published accuracy + pass@k
  spectrum, nothing else.
- `analyze_scores(scores, cluster_ids, level=...)` — scores with cluster ids at an
  operating level: the exceedance-indicator ICC that governs a threshold.

Core estimators live in `neff._icc` (vendored canonical; see `.vocab-pin`), the pass@k
inversion in `neff.passk`. Theory and provenance: doi.org/10.5281/zenodo.21595640.
"""

from ._icc import (
    IccResult,
    copula_diagonal_gaussian,
    deff,
    icc_oneway,
    n_eff,
    rho_indicator,
    rho_indicator_gaussian,
    rho_indicator_pairs,
    rho_indicator_strata,
)
from .passk import (
    PassKResult,
    analyze_passk_spectrum,
    pass_at_k_row,
    passk_icc,
    published_se,
    recover_counts,
    task_se,
)
from .report import Report, analyze_outcomes, analyze_passk, analyze_scores

__version__ = "0.1.0"

__all__ = [
    "IccResult",
    "PassKResult",
    "Report",
    "analyze_outcomes",
    "analyze_passk",
    "analyze_passk_spectrum",
    "analyze_scores",
    "copula_diagonal_gaussian",
    "deff",
    "icc_oneway",
    "n_eff",
    "pass_at_k_row",
    "passk_icc",
    "published_se",
    "recover_counts",
    "rho_indicator",
    "rho_indicator_gaussian",
    "rho_indicator_pairs",
    "rho_indicator_strata",
    "task_se",
]
