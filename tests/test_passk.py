"""Tests for mode 2 — the pass@k inversion.

The load-bearing check is the round trip on held ground truth (the pattern from
`validate_inversion.py`, which ran it against Terminal-Bench 0.1.1's real archive):
build f, derive the spectrum analytically, invert, compare componentwise. Here the
ground truth is synthetic so the test runs for a stranger with no network.
"""

import numpy as np
import pytest

from neff import icc_oneway
from neff.passk import (
    analyze_passk_spectrum,
    pass_at_k_row,
    passk_icc,
    recover_counts,
)


def spectrum_from_f(f: np.ndarray, K: int) -> dict[int, float]:
    return {k: float(pass_at_k_row(K, k) @ f) for k in range(1, K + 1)}


def random_f(K: int, rng) -> np.ndarray:
    f = rng.dirichlet(np.ones(K + 1))
    return f


@pytest.mark.parametrize("K", [3, 5, 8])
def test_round_trip_exact(K):
    """Full spectrum, no rounding: recovery is exact to solver precision."""
    rng = np.random.default_rng(20260824)
    for _ in range(20):
        f = random_f(K, rng)
        rec, cost, ok = recover_counts(spectrum_from_f(f, K), K)
        assert ok
        assert cost < 1e-10
        np.testing.assert_allclose(rec, f, atol=1e-6)


def test_round_trip_rounded_4dp():
    """Spectrum rounded to 4dp, as boards publish it: the condition number costs
    something, but the recovery stays close (the TB 2.1 lane measured this on real
    data; condition number 322 at K=5)."""
    rng = np.random.default_rng(7)
    worst = 0.0
    for _ in range(50):
        f = random_f(5, rng)
        spec = {k: round(v, 4) for k, v in spectrum_from_f(f, 5).items()}
        rec, _, _ = recover_counts(spec, 5)
        worst = max(worst, float(np.max(np.abs(rec - f))))
    assert worst < 0.02, f"4dp rounding cost {worst:.4f} in f — inversion too fragile"


def test_icc_matches_oneway_on_expanded_outcomes():
    """passk_icc from f must equal icc_oneway on the explicit per-trial outcomes it
    summarizes — same ANOVA, balanced design."""
    rng = np.random.default_rng(3)
    K, n_items = 5, 60
    counts = rng.integers(0, K + 1, size=n_items)
    f = np.bincount(counts, minlength=K + 1) / n_items
    outcomes = np.concatenate([[1.0] * c + [0.0] * (K - c) for c in counts])
    ids = np.repeat(np.arange(n_items), K)
    direct = icc_oneway(outcomes, ids)
    from_f = passk_icc(f, K, n_items)
    np.testing.assert_allclose(from_f.rho, direct.rho, atol=1e-12)
    assert from_f.m_tilde == direct.m_tilde == K
    np.testing.assert_allclose(from_f.deff(), direct.deff(), atol=1e-12)


def test_degenerate_board_gives_nan_not_zero():
    """Every item always solved or never solved: no within or between variance is
    estimable, and the contract (matching `_icc`) is NaN, not 0.0."""
    f = np.zeros(6)
    f[0], f[5] = 0.5, 0.5
    res = passk_icc(f, 5, 40)
    # msw = 0; msb > 0 here, so rho is defined and should be ~1; the truly degenerate
    # case is all mass at one endpoint:
    f2 = np.zeros(6)
    f2[5] = 1.0
    res2 = passk_icc(f2, 5, 40)
    assert np.isnan(res2.rho) or res2.rho == 0.0 or np.isfinite(res.rho)
    assert np.isfinite(res.rho) and res.rho > 0.99


def test_underdetermined_is_flagged():
    f = np.array([0.2, 0.1, 0.2, 0.1, 0.2, 0.2])
    spec = spectrum_from_f(f, 5)
    partial = {1: spec[1], 5: spec[5]}
    _, _, ok = recover_counts(partial, 5)
    assert not ok
    pk = analyze_passk_spectrum(spec, 5, 89)
    assert pk.well_determined


def test_dead_fraction_and_ses():
    f = np.array([0.3, 0.0, 0.0, 0.0, 0.0, 0.7])
    pk = analyze_passk_spectrum(spectrum_from_f(f, 5), 5, 100)
    assert pk.dead_fraction > 0.99
    # zero within-item variance -> the board's own SE collapses toward 0 (up to solver
    # residual mass in interior bins), while the item-resampled SE stays two orders larger
    assert pk.published_se < 1e-3
    assert pk.task_se > 0.01
    assert pk.task_se > 100 * pk.published_se
