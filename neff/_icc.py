"""Intra-cluster correlation of the exceedance indicator, and the design effect it drives.

Research-side shared module, sibling to `_conformal.py` and governed by the same rule in
STRUCTURE.md: `experiments/` may import from here, `lessons/` never may.

Why this exists
---------------
As of 2026-07-27 the same quantity was hand-written **eight times** across five lanes, in three
mutually incompatible forms wearing one name. Consolidating is not tidying — the copies disagree,
and the disagreements had already reached published-adjacent numbers:

1. **Edge-case policy diverged silently.** `2026-07-26-conformal-context-pruning/icc_link.py`
   DROPS every cluster of size 1; `2026-07-26-layer-drop-calibration/rho_i_audit.py` CLIPS negative
   estimates to zero; three others do neither. All five are defensible and none announced itself, so
   a rho from one lane and a rho from another were never comparable. This matters most where it is
   least visible: AD-07's entire result is about singletons, and CP's estimator cannot see them.

2. **The design-effect multiplier diverged, and one side is wrong.** SW-02 Theorem 1 is
   `n_eff = n / (1 + (m_tilde - 1) * rho_I(p))` with `m_tilde = sum(m^2)/sum(m)`, the SIZE-BIASED
   mean. AD-08 uses m_tilde; LD's `rho_i_audit.json` used `m0`, the ANOVA size correction, which is
   a different and generally smaller number. On LD's 57 MMLU subjects m0 = 34.46 against
   m_tilde = 70.15, so its reported n_eff of 483.9 should read 267.6 — optimistic by 1.81x.
   `test_icc_golden.py::test_ld_multiplier_divergence` pins both, so the correction cannot be lost.

3. **The analytic and empirical forms shared a name and swapped argument order.** `rho_I(p, r)`
   (model-based, Gaussian copula) and `rho_I(fams, p)` (sample ANOVA) were both spelled `rho_I`.
   `rho_I(0.9, 0.3)` was a valid call in two files meaning two unrelated things. They are
   `rho_indicator_gaussian` and `rho_indicator` here and can no longer be confused.

4. **A third form was never a duplicate at all.** `k3_prm800k.rho_I(G_cond, f_z)` is the
   design-based population ICC over known stratum marginals — no MSW subtraction, no m0 correction.
   It estimates the same population quantity by a different route and carries an upward finite-
   stratum bias the ANOVA form corrects. On K3's own substrate that bias is MEASURED at +1.6e-5 at
   p=0.80 and +2.0e-5 at p=0.99 — negligible, because the five strata hold ~73k selected samples
   each — so no K3 number moves. But K3.md's claim that both lanes "measure it with the same
   estimator" is not what the code does, and the bias stops being negligible the moment the strata
   are small. It is `rho_indicator_strata` here.

What is deliberately NOT changed
--------------------------------
`2026-07-26-sw02-exchangeability-audit/` is FROZEN. Its scripts shipped in the v4 Zenodo code
archive against DOI 10.5281/zenodo.21629688; editing them post-publication would mean the archive
no longer matches the published record. SW-02's numbers are the SPEC for this module, not debt to be
repaid — they are pinned as tests. Only AD, K3, CP and LD migrate.

Provenance
----------
Written out 2026-07-27, not hand-typed in a lesson. It is research-side by construction and must
never be promoted into `calkit/` without going on that package's provenance exceptions list.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Literal, Sequence

import numpy as np
from scipy.stats import multivariate_normal, norm

__all__ = [
    "IccResult",
    "icc_oneway",
    "rho_indicator",
    "rho_indicator_gaussian",
    "rho_indicator_pairs",
    "copula_diagonal_gaussian",
    "rho_indicator_strata",
    "deff",
    "n_eff",
]

Singletons = Literal["keep", "drop", "error"]


# --------------------------------------------------------------------------------------------
# result container
# --------------------------------------------------------------------------------------------


@dataclass(frozen=True)
class IccResult:
    """Everything a caller needs to interpret an ICC, including what it would rather not see.

    `n_singleton` is returned unconditionally and on purpose. The most expensive disagreement
    between the historical implementations was invisible precisely because nobody had to ask how
    many clusters of size 1 were in play.
    """

    rho: float
    m0: float          # ANOVA size correction, (N - sum(m^2)/N) / (k - 1). NOT the design-effect multiplier.
    m_tilde: float     # size-biased mean, sum(m^2)/sum(m). THIS is what enters deff / n_eff.
    m_bar: float       # plain mean cluster size, for reporting only
    k: int             # clusters used
    n: int             # observations used
    n_singleton: int   # clusters of size 1 in the INPUT (before any `singletons` policy applied)
    msb: float
    msw: float
    clipped: bool      # True iff a negative estimate was floored to 0 by `clip=True`

    def deff(self) -> float:
        """Design effect at this cluster structure, using m_tilde per SW-02 Theorem 1."""
        return deff(self.rho, self.m_tilde)

    def n_eff(self) -> float:
        """Effective sample size, using m_tilde per SW-02 Theorem 1."""
        return n_eff(self.n, self.m_tilde, self.rho)


# --------------------------------------------------------------------------------------------
# grouping
# --------------------------------------------------------------------------------------------


def _as_groups(values, cluster_ids=None) -> list[np.ndarray]:
    """Accept either (flat values, cluster ids) or a ragged sequence of per-cluster arrays.

    Both call signatures existed in the wild — `anova_icc(fams)` in AD-08 and prm_measurement,
    `anova_icc(vals, fam_ids)` in AD-05b — so both are supported rather than forcing a rewrite of
    every call site. Grouping is order-independent: `np.unique` sorts ids, and the ANOVA statistics
    below are symmetric in cluster order, so the two paths give bit-identical results.
    """
    if cluster_ids is None:
        return [np.asarray(g, dtype=float).ravel() for g in values]
    v = np.asarray(values, dtype=float).ravel()
    c = np.asarray(cluster_ids).ravel()
    if v.shape != c.shape:
        raise ValueError(f"values {v.shape} and cluster_ids {c.shape} must have the same length")
    order = np.argsort(c, kind="stable")
    v, c = v[order], c[order]
    bounds = np.flatnonzero(c[1:] != c[:-1]) + 1
    return list(np.split(v, bounds))


# --------------------------------------------------------------------------------------------
# the empirical estimator
# --------------------------------------------------------------------------------------------


def icc_oneway(
    values,
    cluster_ids=None,
    *,
    singletons: Singletons = "keep",
    clip: bool = False,
) -> IccResult:
    """One-way random-effects ICC with unequal cluster sizes (Donner & Eliasziw).

        rho = (MSB - MSW) / (MSB + (m0 - 1) * MSW),   m0 = (N - sum(m^2)/N) / (k - 1)

    This is the estimator SW-02 §8 settled on. The naive pair ratio
    `sum C(c_j,2) / sum C(m_j,2)` against a point-weighted p_hat is INCONSISTENT under unequal
    sizes — it weights families by m_j(m_j-1) while p_hat weights by m_j, so where larger families
    have higher rates the ratio can exceed 1. That was observed on PRM800K before it was fixed.

    Parameters
    ----------
    values, cluster_ids
        Either `(flat_values, flat_cluster_ids)` or a single ragged sequence of per-cluster arrays.
    singletons
        What to do with clusters of size 1. **There is no silent default policy** — `n_singleton`
        is always reported so the choice is auditable after the fact.

        - ``"keep"`` (default): singletons contribute to N, to the grand mean, and to SSB. They add
          nothing to SSW and nothing to its df (one observation, one fitted mean, zero residual df),
          so MSW is unaffected — keeping them is statistically clean, not a compromise. Matches
          prm_measurement, AD-08 and AD-05b.
        - ``"drop"``: exclude them entirely. This CHANGES THE ESTIMAND to clusters observed at least
          twice, which is a real and sometimes correct choice — but it is a different quantity, and
          it is the one thing AD-07 shows you cannot afford to do silently. Matches CP's `icc_link`.
        - ``"error"``: raise if any are present.
    clip
        Floor a negative estimate at 0. **Default False, and that is deliberate.** A negative
        design effect is not meaningful, so clipping is reasonable when *using* rho — but it is a
        decision about use, not about estimation. Clipped, "no detectable clustering" and "the
        estimate is too noisy to sign" become the same number, and the second is a power warning
        you want to see. Let `deff()` do the flooring, where it is visible. Matches LD when True.

    Returns
    -------
    IccResult — `rho` is NaN when fewer than two usable clusters remain, or when the denominator
    vanishes, rather than raising. A degenerate stratum is a normal occurrence in a sweep.
    """
    groups = _as_groups(values, cluster_ids)
    n_singleton = sum(1 for g in groups if g.size == 1)

    if singletons == "error" and n_singleton:
        raise ValueError(f"{n_singleton} singleton cluster(s) present and singletons='error'")
    if singletons == "drop":
        groups = [g for g in groups if g.size >= 2]
    elif singletons not in ("keep", "error"):
        raise ValueError(f"singletons must be 'keep', 'drop' or 'error'; got {singletons!r}")

    groups = [g for g in groups if g.size > 0]
    sizes = np.array([g.size for g in groups], dtype=float)
    k, n = len(groups), float(sizes.sum())

    nan = float("nan")
    if k < 2 or n <= k:
        return IccResult(nan, nan, nan, nan, k, int(n), n_singleton, nan, nan, False)

    flat = np.concatenate(groups)
    grand = float(flat.mean())
    means = np.array([float(g.mean()) for g in groups])

    ssb = float((sizes * (means - grand) ** 2).sum())
    ssw = float(sum(float(((g - g.mean()) ** 2).sum()) for g in groups))
    msb, msw = ssb / (k - 1), ssw / (n - k)

    sum_sq = float((sizes ** 2).sum())
    m0 = (n - sum_sq / n) / (k - 1)
    m_tilde = sum_sq / n
    m_bar = n / k

    denom = msb + (m0 - 1) * msw
    rho = nan if denom == 0 else (msb - msw) / denom

    clipped = False
    if clip and np.isfinite(rho) and rho < 0:
        rho, clipped = 0.0, True

    return IccResult(
        rho=float(rho), m0=float(m0), m_tilde=float(m_tilde), m_bar=float(m_bar),
        k=k, n=int(n), n_singleton=n_singleton,
        msb=float(msb), msw=float(msw), clipped=clipped,
    )


def rho_indicator(
    scores,
    cluster_ids=None,
    p: float = 0.9,
    *,
    threshold: float | None = None,
    singletons: Singletons = "keep",
    clip: bool = False,
) -> IccResult:
    """Indicator ICC at coverage level `p`: the ICC of `1{score <= t}`, `t` the pooled p-quantile.

    This is the rho_I of SW-02 Theorem 1 — the quantity that actually drives the design effect. It
    is NOT the ICC of the raw score, which is a DIFFERENT number.

    **It is not reliably a SMALLER one, and this docstring said otherwise until 2026-07-30.** The
    old wording — "a different and generally larger number; the whole point of the theorem is that
    the score correlation overstates the damage" — is false as a general claim, and the counter-
    example is on real data:

        SW-02 Sec 6.1, PRM calibration set   score ICC 0.599  vs  rho_I 0.495   (score LARGER)
        deploygate/D-01, SQuAD 2.0 dev       score ICC 0.0352 vs  rho_I 0.0426  (score SMALLER)
          (same substrate, paragraph level)  score ICC -0.0026 vs rho_I 0.0640  (score ~ZERO)

    The last row is the paper's own Sec 3 counterexample appearing in released data: a raw-score
    correlation indistinguishable from zero alongside an indicator ICC that clears its permutation
    null and carries DEFF 1.60. So the defensible statement is that the two quantities differ and
    **neither bounds the other** — measure rho_I, never infer it from the score ICC in either
    direction. Attenuation into the tail (Sec 5) is a statement about rho_I(p) as p varies, not a
    ranking of rho_I against the score ICC.

    Pass `threshold` to score against a fixed, externally calibrated t instead of the pooled
    empirical quantile — the correct move when calibration and test sets are separate.

    The indicator convention is `score <= t` (low score = conforming), matching every historical
    call site. Flip the sign of `scores` if yours runs the other way.
    """
    groups = _as_groups(scores, cluster_ids)
    flat = np.concatenate(groups) if groups else np.array([])
    if flat.size == 0:
        nan = float("nan")
        return IccResult(nan, nan, nan, nan, 0, 0, 0, nan, nan, False)
    t = float(np.quantile(flat, p)) if threshold is None else float(threshold)
    ind = [(g <= t).astype(float) for g in groups]
    return icc_oneway(ind, singletons=singletons, clip=clip)


# --------------------------------------------------------------------------------------------
# the analytic form — model-based, NOT interchangeable with the above
# --------------------------------------------------------------------------------------------


def copula_diagonal_gaussian(p: float, r: float) -> float:
    """delta(p) = P(both siblings <= the p-quantile) under an equicorrelated Gaussian copula.

    Exposed because it is a primitive in its own right, not only an intermediate: SW-02
    Theorem 1 is stated in terms of the copula diagonal, and the AD lane consumes delta
    directly when it needs the joint rather than the ICC. Keeping it private forced callers
    to re-derive it, which is how the duplication started.

    Both Frechet bounds are closed-form: r=+1 gives the comonotone copula M with diagonal p,
    r=-1 the countermonotone copula W with diagonal max(2p-1, 0) — the value a family of size
    2 hits exactly under full within-family centering.
    """
    if not 0.0 < p < 1.0:
        raise ValueError(f"p must be in (0, 1); got {p}")
    if not -1.0 <= r <= 1.0:
        raise ValueError(f"r must be in [-1, 1]; got {r}")
    if r >= 1.0 - 1e-12:
        return float(p)
    if r <= -1.0 + 1e-12:
        return float(max(2.0 * p - 1.0, 0.0))
    if r == 0.0:
        return float(p * p)
    z = norm.ppf(p)
    return float(multivariate_normal(mean=[0.0, 0.0], cov=[[1.0, r], [r, 1.0]]).cdf([z, z]))


def rho_indicator_pairs(values, *, p: float = 0.9, threshold: float | None = None) -> float:
    """Pair-estimator indicator ICC for BALANCED families. Raises on ragged input.

        delta_hat = sum_j C(c_j, 2) / sum_j C(m_j, 2),   rho_I = (delta - p^2) / (p(1-p))

    This is a legitimate estimator and the one closest to SW-02's theory, which is written in
    terms of the copula diagonal — but ONLY when every family is the same size. Under unequal
    sizes it is inconsistent: delta_hat weights families by m_j(m_j-1) while p_hat weights by
    m_j, so where larger families have higher rates the ratio can exceed 1. That is not
    hypothetical — it returned an impossible rho_I > 1 on the real PRM calibration set before
    the ANOVA form replaced it.

    So the balance requirement is ENFORCED rather than documented. Use `icc_oneway` /
    `rho_indicator` for anything ragged.

    `values` is a 2-D array-like of shape (families, m).
    """
    y = np.asarray(values, dtype=float)
    if y.ndim != 2:
        raise ValueError(
            f"rho_indicator_pairs needs a (families, m) 2-D array; got shape {y.shape}. "
            "Ragged families have no balanced pair estimator — use rho_indicator().")
    b, m = y.shape
    if m < 2:
        raise ValueError("pair estimator needs at least 2 members per family")
    t = float(np.quantile(y, p)) if threshold is None else float(threshold)
    ind = (y <= t).astype(float)
    c = ind.sum(axis=1)
    delta = float((c * (c - 1.0)).sum() / (b * m * (m - 1.0)))
    p_hat = float(ind.mean())
    if not 0.0 < p_hat < 1.0:
        return float("nan")
    return (delta - p_hat * p_hat) / (p_hat * (1.0 - p_hat))


def rho_indicator_gaussian(p: float, r: float) -> float:
    """Indicator ICC at level `p` under an equicorrelated Gaussian copula with correlation `r`.

        rho_I(p) = (delta(p) - p^2) / (p * (1 - p)),  delta(p) = P(both siblings <= the p-quantile)

    Model-based: `r` is the LATENT score correlation, not a measured indicator ICC. Deliberately
    named apart from `rho_indicator` because the two took swapped arguments under one name and
    `rho_I(0.9, 0.3)` was a valid call in two files meaning two unrelated things.

    **`r` may be NEGATIVE, and that is not an edge case here.** This function originally
    short-circuited every `r <= 0` to 0.0, which is right only at exactly r=0. Attempting to
    migrate the AD lane onto it in 2026-07-27 surfaced the bug: within-family centering is the
    whole subject of that lane, and centering DRIVES sibling correlation negative — at m=2 under
    full centering, Y_i2 = -Y_i1 exactly. The migration would have silently returned 0 for the
    arm the experiment exists to measure.

    Both Frechet bounds are closed-form rather than passed to a bivariate-normal CDF that would
    be singular there: r=+1 is the comonotone copula M with diagonal p, and r=-1 is the
    countermonotone copula W with diagonal max(2p-1, 0). At r=0 siblings are independent, so
    delta = p^2 and rho_I = 0 exactly.
    """
    if not 0.0 < p < 1.0:
        raise ValueError(f"p must be in (0, 1); got {p}")
    if not -1.0 <= r <= 1.0:
        raise ValueError(f"r must be in [-1, 1]; got {r}")
    # The perfect-correlation and independence endpoints return exact constants rather than
    # being computed from the diagonal. Routing r=1 through (delta - p^2)/(p(1-p)) gives
    # 0.9999999999999997 at p=0.8 and 1.000000000000001 at p=0.99 — a value ABOVE 1 for a
    # correlation, which downstream code is entitled to reject. Caught by
    # test_analytic_endpoints_are_exact when this function was refactored onto the shared
    # copula, which is what that test is for.
    if r >= 1.0 - 1e-12:
        return 1.0
    if r == 0.0:
        return 0.0
    delta = copula_diagonal_gaussian(p, r)
    return (delta - p * p) / (p * (1.0 - p))


def rho_indicator_strata(
    g_cond: Sequence[float],
    f_z: Sequence[float],
    *,
    sizes: Sequence[float] | None = None,
) -> float:
    """Design-based indicator ICC from per-stratum exceedance rates and a KNOWN stratum marginal.

        rho = Var_z(G(z)) / (p_bar * (1 - p_bar)),   p_bar = sum_z f(z) G(z)

    This is K3's form, and it is a genuinely different estimator from `icc_oneway` — same
    population quantity, different route. It requires `f_z` to be known (in K3, by construction
    from the unselected population) and it has NO finite-stratum bias correction: sampling noise in
    each `G(z)` inflates the between-stratum variance and biases rho upward.

    Pass `sizes` (observations per stratum) for a first-order correction subtracting the estimated
    sampling variance of each G(z). Off by default so K3's published numbers reproduce exactly. On
    K3's substrate the correction is measured at -1.6e-5 (p=0.80) to -2.0e-5 (p=0.99); it is
    first-order only, treating p_bar as known, which is fine when the strata are large and is the
    regime where the correction matters least anyway.
    """
    g = np.asarray(g_cond, dtype=float)
    f = np.asarray(f_z, dtype=float)
    if g.shape != f.shape:
        raise ValueError(f"g_cond {g.shape} and f_z {f.shape} must have the same length")
    p_bar = float((g * f).sum())
    var_between = float((f * (g - p_bar) ** 2).sum())
    if sizes is not None:
        nz = np.asarray(sizes, dtype=float)
        if nz.shape != g.shape:
            raise ValueError(f"sizes {nz.shape} must match g_cond {g.shape}")
        var_between -= float((f * g * (1.0 - g) / np.maximum(nz, 1.0)).sum())
    return var_between / max(p_bar * (1.0 - p_bar), 1e-12)


# --------------------------------------------------------------------------------------------
# design effect
# --------------------------------------------------------------------------------------------


def deff(rho_i: float, m_tilde: float, *, floor_at_one: bool = True) -> float:
    """Design effect: `1 + (m_tilde - 1) * rho_i`.

    **`m_tilde` is the SIZE-BIASED mean `sum(m^2) / sum(m)`, not `m0` and not `m_bar`.** This is the
    multiplier in SW-02 Theorem 1 and the one place a wrong cluster statistic silently rescales an
    effective sample size. LD's `rho_i_audit.json` passed `m0` here and reported an n_eff 1.81x too
    optimistic; that is why the argument is named rather than positional-by-convention.

    `floor_at_one` clips a below-1 design effect. This is where clipping belongs — visible, at the
    point of use, rather than buried in the estimator (see `icc_oneway(clip=...)`). A design effect
    below 1 means the estimate went negative, which is a power warning about the ICC, not a licence
    to claim you have MORE information than n independent points.
    """
    d = 1.0 + (m_tilde - 1.0) * rho_i
    if floor_at_one and np.isfinite(d):
        return max(d, 1.0)
    return float(d)


def n_eff(n: int | float, m_tilde: float, rho_i: float, *, floor_at_one: bool = True) -> float:
    """Effective sample size `n / deff`, per SW-02 Theorem 1. See `deff` on `m_tilde`."""
    d = deff(rho_i, m_tilde, floor_at_one=floor_at_one)
    return float(n) / d if d else float("nan")
