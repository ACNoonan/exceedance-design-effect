"""Golden-number tests for `_icc.py` — the refactor's safety net.

    .venv/bin/python -m pytest experiments/test_icc_golden.py -q
    .venv/bin/python experiments/test_icc_golden.py          # same, without pytest

The rule this file enforces
---------------------------
Every number below was produced by a DIFFERENT hand-written implementation before `_icc.py`
existed. If a change to `_icc.py` moves one of them, that is a FINDING — a published or
published-adjacent number just changed — and it must be resolved as a finding, not patched by
editing the expected value here.

Three of these were never a test of anything until now:

  * `test_ad08_ad05b_cross_implementation` — AD-05b and AD-08 attacked the same open item in
    parallel, unseen, and agreed to five decimals. RESULTS-AD05b.md calls that "a real control on
    both — the kind that could have failed and did not." It was an ACCIDENT. Here it is a test, and
    it now runs both call signatures (ragged list vs flat+ids) through one estimator.

  * `test_sw02_published_table` — SW-02's scripts are frozen inside a published Zenodo code archive
    and may not be edited. That makes their output the specification. If this fails, `_icc.py` is
    wrong; the paper is not.

  * `test_ld_multiplier_divergence` — pins the m0-vs-m_tilde error found on 2026-07-27 so the
    correction cannot quietly evaporate. It asserts the WRONG number as wrong and the right one as
    right, together, on purpose.

Substrates are the caches already on disk. Tests needing a cache skip cleanly if it is absent, so
this file is runnable on a fresh clone; the analytic and synthetic tests always run.
"""

from __future__ import annotations

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from neff._icc import (  # noqa: E402
    deff,
    icc_oneway,
    n_eff,
    rho_indicator,
    rho_indicator_gaussian,
    rho_indicator_strata,
)

HERE = os.path.dirname(os.path.abspath(__file__))
AD = os.path.join(HERE, "2026-07-27-ancestry-decorrelating-scores")
SEL = os.path.join(HERE, "2026-07-27-selection-identification")

# Floating-point summation order differs between the ragged-list and flat+ids paths, so bitwise
# equality is not the right bar. 1e-12 relative is ~4 orders tighter than any decision any lane
# makes on these numbers, and still catches a genuine estimator change.
RTOL = 1e-12


def _load(path, *keys):
    if not os.path.exists(path):
        pytest.skip(f"cache absent: {os.path.basename(path)}")
    d = np.load(path)
    return tuple(d[k] for k in keys)


# ==============================================================================================
# 1. the analytic form, against SW-02's frozen published output
# ==============================================================================================


def test_sw02_published_table():
    """`assumption_stress_RESULTS.txt` [1], p = 0.90012, b=200 clusters of m=4.

    Published rho_I column: 0.1850 / 0.1469 / 0.1356 / 0.1331 / 0.1290 against conditional
    correlations 0.40, 1/3, 0.3125, 0.3077, 0.30. The table prints r rounded to 4dp, so row 2's
    r is exactly 1/3 (0.3333 rounds rho_I to 0.1468 — a display artifact, not a discrepancy).
    """
    p = 0.90012
    for r, expected in [(0.40, 0.1850), (1 / 3, 0.1469), (0.3125, 0.1356),
                        (0.3077, 0.1331), (0.30, 0.1290)]:
        assert round(rho_indicator_gaussian(p, r), 4) == expected, f"r={r}"


def test_sw02_published_n_eff():
    """Same table, n_eff column: 514.5 at n=800, m=4, r=0.40. Uses m_tilde (= m for equal sizes)."""
    rho = rho_indicator_gaussian(0.90012, 0.40)
    assert round(n_eff(800, 4, rho), 1) == 514.5


def test_analytic_endpoints_are_exact():
    """r=0 -> independent siblings -> delta = p^2 -> rho_I = 0. r=1 -> identical -> rho_I = 1.

    Returned exactly rather than through the numerical CDF, which would leave ~1e-9 dust and make
    a zero-clustering check look like weak clustering.
    """
    for p in (0.5, 0.8, 0.90012, 0.99):
        assert rho_indicator_gaussian(p, 0.0) == 0.0
        assert rho_indicator_gaussian(p, 1.0) == 1.0


def test_analytic_handles_negative_correlation():
    """Centering drives sibling correlation NEGATIVE — the AD lane's entire subject.

    `rho_indicator_gaussian` originally returned 0.0 for every `r <= 0`, correct only at
    exactly 0. Migrating AD-01 onto it would have silently zeroed the arm the experiment
    measures. Pinned so the short-circuit cannot come back.

    At r = -1 (countermonotone copula W) the diagonal is max(2p-1, 0), so at p <= 0.5 the
    two siblings can never both fall below the quantile and rho_I hits its floor of
    -p/(1-p); at p = 0.9 it is (0.8 - 0.81)/0.09.
    """
    assert rho_indicator_gaussian(0.9, 0.0) == 0.0
    assert rho_indicator_gaussian(0.9, -1.0) == pytest.approx((0.8 - 0.81) / 0.09)
    assert rho_indicator_gaussian(0.5, -1.0) == pytest.approx(-1.0)

    for p in (0.5, 0.8, 0.9):
        vals = [rho_indicator_gaussian(p, r) for r in (-0.9, -0.5, -0.2, 0.0, 0.2, 0.5, 0.9)]
        assert all(v < 0 for v in vals[:3]), vals          # negative r => negative rho_I
        assert all(b > a for a, b in zip(vals, vals[1:])), vals   # monotone throughout

    with pytest.raises(ValueError):
        rho_indicator_gaussian(0.9, -1.5)


def test_analytic_is_monotone_and_level_dependent():
    """rho_I rises in r at fixed p, and FALLS in p at fixed r in the upper tail.

    The second half is SW-02's level-dependence result, and it is the reason a single rho quoted
    without its level is meaningless. Asserted here so the module cannot silently lose it.
    """
    p = 0.9
    vals = [rho_indicator_gaussian(p, r) for r in (0.1, 0.3, 0.5, 0.7, 0.9)]
    assert all(b > a for a, b in zip(vals, vals[1:])), vals

    r = 0.5
    tail = [rho_indicator_gaussian(q, r) for q in (0.80, 0.90, 0.95, 0.99)]
    assert all(b < a for a, b in zip(tail, tail[1:])), tail


# ==============================================================================================
# 2. the empirical form, against AD-08 and AD-05b on real PRM800K
# ==============================================================================================

# result_ad08.json, partA, lambda = 0.0. Substrate: 815,632 solutions over 500 MATH problems,
# families = problems, nonconformity s = -prm_score.
AD08_RHO_I = {0.80: 0.30482415843865013,
              0.90: 0.20285364896720962,
              0.95: 0.13411880738713170,
              0.99: 0.04659113783291548}
AD08_M_TILDE = 1720.9829089589423
AD08_N = 815632


def _ad08_families():
    qid, prm = _load(os.path.join(AD, "prm800k_families.npz"), "qid", "prm")
    return np.split(-prm, np.flatnonzero(np.diff(qid)) + 1)


def test_ad08_real_score():
    """AD-08's raw rho_I at four coverage levels, plus the cluster structure it reported."""
    fams = _ad08_families()
    for p, expected in AD08_RHO_I.items():
        res = rho_indicator(fams, p=p)
        assert res.rho == pytest.approx(expected, rel=RTOL), f"p={p}"
        assert res.k == 500
        assert res.n == AD08_N
        assert res.n_singleton == 0
        assert res.m_tilde == pytest.approx(AD08_M_TILDE, rel=RTOL)


def test_ad08_deff_and_n_eff():
    """result_ad08.json partA at lambda=0: deff 525.29 / n_eff 1552.72 at p=0.80."""
    res = rho_indicator(_ad08_families(), p=0.80)
    assert res.deff() == pytest.approx(525.292342752271, rel=1e-10)
    assert res.n_eff() == pytest.approx(1552.7201400395318, rel=1e-10)


def test_ad08_ad05b_cross_implementation():
    """The accidental control, made deliberate.

    AD-08 built ragged family arrays from `qid` boundaries and used `s = -prm`. AD-05b built a
    flat array plus `fam` ids from a separately written extraction, on a bounded score that is a
    monotone equivalent. RESULTS-AD05b.md records raw rho_I(0.80) = 0.30482 from that second path.

    Both call signatures now run through one estimator, and the two caches are independent files.
    Agreement here means the extraction, the grouping and the ANOVA all match.
    """
    prm, fam = _load(os.path.join(AD, "ad05b_cache.npz"), "prm", "fam")
    flat = rho_indicator(-prm, fam, p=0.80)
    ragged = rho_indicator(_ad08_families(), p=0.80)

    assert flat.rho == pytest.approx(ragged.rho, rel=RTOL)
    assert flat.rho == pytest.approx(AD08_RHO_I[0.80], rel=RTOL)
    assert flat.k == ragged.k == 500


def test_indicator_icc_is_below_score_icc():
    """SW-02's headline in one assertion: the SCORE correlation overstates the damage.

    AD-08 reports rho_hat = 0.6122 for the raw score against rho_I(0.80) = 0.3048. Any future
    change that lets the indicator ICC drift up toward the score ICC has broken the thing the
    theorem is for.
    """
    fams = _ad08_families()
    score_icc = icc_oneway(fams)
    assert score_icc.rho == pytest.approx(0.6121536723070096, rel=1e-9)
    assert rho_indicator(fams, p=0.80).rho < score_icc.rho


# ==============================================================================================
# 3. the design-based form, against K3's published sensitivity curve
# ==============================================================================================

# K3.md: "rho_I(Z) falls 20x from 0.1035 at p=0.80 to 0.0054 at p=0.99".
K3_RHO_I = {0.80: 0.1035381613212218,
            0.90: 0.05870318271326575,
            0.95: 0.03010780082627702,
            0.99: 0.00540347420476825}
K3_SELECTED = 366508


def _k3_selection():
    """Replicate k3_prm800k.py's imposed selection exactly: seed 20260727, GAMMA_TRUE = 1.8."""
    s, z = _load(os.path.join(SEL, "k3_prm800k_cache.npz"), "s", "z")
    levels = np.arange(1, 6)
    f_z = np.array([(z == lv).mean() for lv in levels])
    pi_z = np.array([1.0, 0.85, 0.65, 0.45, 0.30])
    r = np.exp(np.log(1.8) * (1 - s))
    r /= r.max()
    keep = np.random.default_rng(20260727).random(s.size) < (pi_z[z - 1] * r)
    return s[keep], z[keep], f_z, levels, int(keep.sum())


def test_k3_published_rho_i():
    """K3's rho_I(Z) curve, and the selection count it was computed on."""
    s_sel, z_sel, f_z, levels, n_sel = _k3_selection()
    assert n_sel == K3_SELECTED

    for p, expected in K3_RHO_I.items():
        tau = float(np.quantile(s_sel, p))
        g_cond = np.array([(s_sel[z_sel == lv] <= tau).mean() for lv in levels])
        assert rho_indicator_strata(g_cond, f_z) == pytest.approx(expected, rel=1e-12), f"p={p}"


def test_k3_uses_population_not_selected_marginal():
    """K3.md's central warning, as a test: 'Reading g as f would be a large error.'

    f(z) is the UNSELECTED population marginal; g(z) is what the selected sample shows. On
    PRM800K, f = (0.096, 0.199, 0.220, 0.252, 0.233) against g = (0.184, 0.308, 0.233, 0.176,
    0.099). Substituting g for f at p=0.90 gives an f-weighted mean exceedance of 0.8634 against a
    g-weighted 0.9000 — K3.md: "that 3.7-point gap is the whole failure."

    NOTE, because it cost a test failure to find: K3.md ALSO quotes
    g = (0.357, 0.270, 0.188, 0.116, 0.068). That belongs to a separate illustration with uniform
    strata, f = (0.2, 0.2, 0.2, 0.2, 0.2), and is NOT this run. Two worked examples share one
    document and one symbol. Pin numbers to the artifact that produced them, never to the prose.
    """
    s_sel, z_sel, f_z, levels, _ = _k3_selection()
    g_z = np.array([(z_sel == lv).mean() for lv in levels])

    assert np.round(f_z, 3).tolist() == [0.096, 0.199, 0.220, 0.252, 0.233]
    assert np.round(g_z, 3).tolist() == [0.184, 0.308, 0.233, 0.176, 0.099]

    tau = float(np.quantile(s_sel, 0.90))
    g_cond = np.array([(s_sel[z_sel == lv] <= tau).mean() for lv in levels])
    assert float((g_cond * f_z).sum()) == pytest.approx(0.8634, abs=5e-5)
    assert float((g_cond * g_z).sum()) == pytest.approx(0.9000, abs=5e-5)


def test_k3_finite_stratum_bias_is_small_here_but_real():
    """The correction K3's plug-in omits: present, signed downward, and negligible on this data.

    Pinned so that if the substrate ever gets smaller strata, the size of what is being ignored is
    already on the record rather than rediscovered.
    """
    s_sel, z_sel, f_z, levels, _ = _k3_selection()
    for p, expected_bias in ((0.80, 1.6e-5), (0.99, 2.0e-5)):
        tau = float(np.quantile(s_sel, p))
        g_cond = np.array([(s_sel[z_sel == lv] <= tau).mean() for lv in levels])
        sizes = np.array([(z_sel == lv).sum() for lv in levels], dtype=float)
        raw = rho_indicator_strata(g_cond, f_z)
        corrected = rho_indicator_strata(g_cond, f_z, sizes=sizes)
        assert corrected < raw
        assert raw - corrected == pytest.approx(expected_bias, rel=0.2), f"p={p}"


# ==============================================================================================
# 4. the LD multiplier error — asserted as an error, so it cannot be lost
# ==============================================================================================

# rho_i_audit.json, config "full", exceedance of the confidence score, p = 0.80.
LD_RHO_I = 0.09363042660603062
LD_M0 = 34.461535714285716
LD_K, LD_N = 57, 2000
LD_RECORDED_DEFF = 4.133017863821501       # what the file says — computed with m0
LD_RECORDED_N_EFF = 483.907901174844       # ditto


def test_ld_multiplier_divergence():
    """LD passed m0 where SW-02 Theorem 1 calls for m_tilde. Both numbers pinned, together.

    m_tilde is recovered from the recorded m0 by inverting the ANOVA correction:
        m0 = (N - sum(m^2)/N) / (k - 1)   =>   m_tilde = sum(m^2)/N = N - m0 * (k - 1)
    On 57 MMLU subjects that gives m_tilde = 70.154 against m0 = 34.462 — the subjects are very
    unequal in size, so the size-biased mean is about twice the plain one.

    Consequence: LD's reported effective sample size is 1.81x too optimistic. rho_I itself is
    unaffected; only deff and n_eff are wrong.
    """
    m_tilde = LD_N - LD_M0 * (LD_K - 1)
    assert m_tilde == pytest.approx(70.154, abs=5e-4)

    # what LD recorded BEFORE the 2026-07-27 correction — reproduced exactly, so the error is
    # identified rather than merely alleged. `rho_i_audit.py` now emits the m_tilde form and keeps
    # these under `superseded_2026_07_27`; this assertion is what makes that history checkable.
    assert deff(LD_RHO_I, LD_M0) == pytest.approx(LD_RECORDED_DEFF, rel=1e-12)
    assert n_eff(LD_N, LD_M0, LD_RHO_I) == pytest.approx(LD_RECORDED_N_EFF, rel=1e-12)

    # what the theorem gives
    assert deff(LD_RHO_I, m_tilde) == pytest.approx(7.4749, abs=5e-4)
    assert n_eff(LD_N, m_tilde, LD_RHO_I) == pytest.approx(267.56, abs=5e-2)

    # the whole point
    assert LD_RECORDED_N_EFF / n_eff(LD_N, m_tilde, LD_RHO_I) == pytest.approx(1.81, abs=5e-3)


# ==============================================================================================
# 5. the edge-case policies that used to diverge silently
# ==============================================================================================


def _ragged_with_singletons():
    """Fixture with real raggedness AND singletons — the case the five implementations split on."""
    rng = np.random.default_rng(20260727)
    groups = []
    for m in [1, 1, 1, 2, 3, 5, 8, 13, 21, 1, 4, 7]:
        groups.append(rng.normal(loc=rng.normal(scale=0.8), size=m))
    return groups


def test_singleton_policies_are_distinct_and_explicit():
    """`keep` and `drop` give DIFFERENT answers. That is the finding, not a bug.

    CP's `icc_link.icc_oneway` dropped size-1 clusters with no announcement, so its rho was never
    comparable to AD's on any ragged substrate. Both behaviours remain available; neither is
    reachable without typing it.
    """
    groups = _ragged_with_singletons()

    kept = icc_oneway(groups, singletons="keep")
    dropped = icc_oneway(groups, singletons="drop")

    assert kept.n_singleton == 4
    assert dropped.n_singleton == 4          # reported from the INPUT, not post-policy
    assert kept.k == 12 and dropped.k == 8
    assert kept.n == 67 and dropped.n == 63
    assert kept.rho != dropped.rho

    with pytest.raises(ValueError):
        icc_oneway(groups, singletons="error")


def test_singletons_do_not_disturb_msw():
    """Why `keep` is the default: a singleton adds 1 to N and 1 to k, so 0 to the within df, and
    contributes 0 to SSW. MSW is therefore identical with and without them — keeping singletons is
    statistically clean rather than a compromise, and only SSB / m0 / m_tilde change."""
    groups = _ragged_with_singletons()
    kept = icc_oneway(groups, singletons="keep")
    dropped = icc_oneway(groups, singletons="drop")
    assert kept.msw == pytest.approx(dropped.msw, rel=1e-12)
    assert kept.msb != pytest.approx(dropped.msb, rel=1e-6)


def test_negative_estimate_is_returned_not_hidden():
    """LD clipped negatives to 0 inside the estimator. Here clipping is opt-in and flagged.

    Anti-correlated clusters give a genuinely negative ANOVA estimate. Unclipped it reads as
    "the estimate is negative", which is a power warning; clipped it is indistinguishable from
    "no clustering detected", and those are different situations.
    """
    rng = np.random.default_rng(7)
    base = rng.normal(size=40)
    groups = [np.array([b, -b]) + 1e-9 * rng.normal(size=2) for b in base]

    raw = icc_oneway(groups)
    assert raw.rho < 0
    assert raw.clipped is False

    clipped = icc_oneway(groups, clip=True)
    assert clipped.rho == 0.0
    assert clipped.clipped is True


def test_deff_floors_at_one_where_it_is_visible():
    """A design effect below 1 would claim MORE information than n independent points. Floored at
    the point of use, where the caller can see it, rather than inside the estimator."""
    assert deff(-0.05, 10.0) == 1.0
    assert deff(-0.05, 10.0, floor_at_one=False) < 1.0
    assert n_eff(1000, 10.0, -0.05) == 1000.0


def test_degenerate_inputs_return_nan_rather_than_raising():
    """Sweeps hit degenerate strata routinely; a NaN row is information, a traceback is a lost run."""
    assert np.isnan(icc_oneway([np.array([1.0, 2.0])]).rho)          # k < 2
    assert np.isnan(icc_oneway([np.array([1.0]), np.array([2.0])]).rho)  # n <= k
    assert np.isnan(rho_indicator([], p=0.9).rho)


def test_both_call_signatures_agree_on_the_same_data():
    """Ragged-list and flat+ids paths are one estimator. Grouping order must not matter either."""
    groups = _ragged_with_singletons()
    flat = np.concatenate(groups)
    ids = np.concatenate([np.full(len(g), i) for i, g in enumerate(groups)])

    a = icc_oneway(groups)
    b = icc_oneway(flat, ids)
    assert b.rho == pytest.approx(a.rho, rel=RTOL)
    assert b.m_tilde == pytest.approx(a.m_tilde, rel=RTOL)

    perm = np.random.default_rng(1).permutation(len(flat))
    c = icc_oneway(flat[perm], ids[perm])
    assert c.rho == pytest.approx(a.rho, rel=RTOL)


def test_m0_and_m_tilde_are_reported_separately():
    """They coincide only for equal cluster sizes. Conflating them is the LD error; the module
    returns both under distinct names so a caller passing the wrong one does so visibly."""
    equal = [np.arange(4.0) + i for i in range(10)]
    r = icc_oneway(equal)
    assert r.m0 == pytest.approx(4.0) and r.m_tilde == pytest.approx(4.0)

    r2 = icc_oneway(_ragged_with_singletons())
    assert r2.m0 != pytest.approx(r2.m_tilde, rel=1e-3)
    assert r2.m_tilde > r2.m_bar > r2.m0      # size-biased > plain > ANOVA-corrected, when ragged


def test_rho_indicator_accepts_an_external_threshold():
    """Calibrate-on-one-split, measure-on-another is the correct move when the sets are separate;
    the pooled empirical quantile silently uses the test data to set its own threshold."""
    groups = _ragged_with_singletons()
    flat = np.concatenate(groups)
    t = float(np.quantile(flat, 0.9))
    assert rho_indicator(groups, p=0.9).rho == pytest.approx(
        rho_indicator(groups, threshold=t).rho, rel=RTOL)
    assert rho_indicator(groups, threshold=t + 1.0).rho != rho_indicator(groups, threshold=t).rho


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-q"]))
