"""SW-02 §6.1 — MEASURING the coverage dispersion on the released PRM set, not plugging it in.

    python experiments/2026-07-26-sw02-exchangeability-audit/prm_dispersion.py

WHY THIS EXISTS (SW-24, SW-27; opened 2026-07-27)
`prm_measurement.py` computes m_tilde, rho_I and hence DEFF = 30.8, n_eff = 812 on the released
set. §6.1 then reported "coverage dispersion is 5.6x wider than the exchangeable assumption
implies, a 5th-95th range of [0.873, 0.909] against the [0.888, 0.894] that n = 25,028 would
give." **That 5.6 is sqrt(DEFF) — our own formula evaluated at our own estimate. It was never
measured**, in a section introduced with "we can say by how much rather than argue that they do."

This script measures it end to end: resample the released questions, run split conformal, and
watch the coverage distribution. Two things come out, and both change §6.1.

  RAW SCORE.        success_prob has 9 distinct values with 67.4% of mass at exactly 0.0, so
                    assumption (A2) (F continuous, f(q_p) > 0) fails outright and coverage can
                    only take the 9 values F attains at its atoms. The realised design effect on
                    coverage sd is ~1.1x, not 5.6x, and the quoted i.i.d. reference sd of 0.0020
                    is unattainable — atom-flipping alone gives an exchangeable sample ~0.0118.
  TIE-BROKEN.       Random tie-breaking (jitter below the atom spacing) is the standard conformal
                    repair for a discrete score and restores (A2) without changing the procedure.
                    The design effect is then real and large — but ~4.3x, not 5.6x.

WHY THE 28% GAP IS NOT A BUG IN THIS SCRIPT
Three candidates could produce it — the law, the rho_I estimator, or this bootstrap harness — and
precondition P3 eliminates all three at once. A synthetic arm is built on the EXACT released size
profile with a one-factor Gaussian copula tuned to a KNOWN true rho_I, and the law, the ANOVA
plug-in and this harness are required to agree there. They do. The gap therefore belongs to the
real data, and the size-band sweep at the end localises it: as the size-score coupling is removed
by restricting to a narrow size band, plug-in/measured goes 1.28 -> 1.10 -> 1.01.

The reading: **Proposition 2's m -> m_tilde substitution over-corrects when cluster sizes are
informative.** §3.4 validated m_tilde to 1.6% across four size profiles, but those sizes were
drawn independently of the scores. The released set has Spearman(size, score) = -0.44. §3.5
already says informative sizes break the MEAN at first order; they break the DISPERSION
correction too, by 28%, in the direction that flatters us.

HONEST SCOPE — read before quoting any number
- `prm_measurement.py`'s caveats all still apply and are not repeated: clusters are QUESTIONS
  (a lower bound on family correlation), and success_prob is the calibrated TARGET rather than
  their unreleased nonconformity score.
- Because the score is a proxy, the tie-broken 4.3x is what the design effect looks like on THIS
  variable made continuous. It is not a claim about their actual pipeline's score, whose rho_I
  would differ. That is exactly why it must be reported as measured-on-the-release rather than as
  a property of their system.
- Random tie-breaking treats two same-question rows with identical scores as independent draws.
  Where those ties are genuine shared-ancestry duplication, jitter DISCARDS real dependence, so
  4.3x is plausibly a lower bound on the tie-broken quantity. Both readings are reported; neither
  is 5.6.
- The cluster bootstrap treats the 500 observed questions as the population. Resampled n varies
  across replicates, which inflates every arm equally — P2 is what shows that does not confound
  the ratio.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from scipy.optimize import brentq
from scipy.stats import multivariate_normal, norm, spearmanr

sys.path.insert(0, str(Path(__file__).resolve().parent))
from prm_measurement import anova_icc, load, size_profile  # noqa: E402  (same estimator as §6.1)

SEED = 20260727
B_REPS = 4000
ATOM_SPACING = 0.125          # success_prob is k/8
JITTER = 0.124                # < spacing: preserves the ordering ACROSS atoms
N_SYNTH = 3                   # synthetic ground-truth realisations (P4 is noisy at 1)

# The operating level is NOT a round number and must not be hard-coded. §6.1 enumerates the
# ACHIEVABLE thresholds and takes the one whose achieved coverage is nearest 0.90 — threshold
# 0.750, giving p = 0.8909. Asking np.quantile for 0.891 instead overshoots it by 1e-4 and lands
# on the next atom (0.875, p = 0.9145, rho_I = 0.4274), which is a different row of §6.1's table.
# That is precisely the discreteness this script exists to document, and it broke P1 on the first
# run. The level is therefore derived from the data below.
TARGET = 0.90


# ----------------------------------------------------------------- bootstrap machinery

def _flatten(fams):
    sizes = np.array([len(f) for f in fams])
    return np.concatenate(fams), sizes, np.concatenate([[0], np.cumsum(sizes)])


def coverage_dist(scores, starts, sizes, level, arm, rng, reps=B_REPS):
    """Distribution of C = F_pop(q_hat) over resampled calibration sets.

    F_pop is the pooled empirical CDF of the full released set — the PER-PREFIX test marginal
    (SW-23's reading (a)), under which the size channel contributes exactly zero, so what this
    measures is dispersion alone and not the size bias.
    """
    b, n_all = len(sizes), len(scores)
    order = np.argsort(scores)
    srt = scores[order]
    out = np.empty(reps)
    for r in range(reps):
        if arm == "CLUSTER":
            pick = rng.integers(0, b, b)
            samp = np.concatenate([scores[starts[j]:starts[j + 1]] for j in pick])
        elif arm == "PERMUTED":                       # same sizes, membership randomised
            perm = scores[rng.permutation(n_all)]
            blocks = np.split(perm, np.cumsum(sizes)[:-1])
            pick = rng.integers(0, b, b)
            samp = np.concatenate([blocks[j] for j in pick])
        elif arm == "IID":
            n = int(sizes[rng.integers(0, b, b)].sum())
            samp = scores[rng.integers(0, n_all, n)]
        else:
            raise ValueError(arm)
        k = min(int(np.ceil((len(samp) + 1) * level)), len(samp))
        qhat = np.partition(samp, k - 1)[k - 1]
        out[r] = np.searchsorted(srt, qhat, side="right") / n_all
    return out


def ratio(scores, starts, sizes, level, rng):
    c = coverage_dist(scores, starts, sizes, level, "CLUSTER", rng)
    p = coverage_dist(scores, starts, sizes, level, "PERMUTED", rng)
    i = coverage_dist(scores, starts, sizes, level, "IID", rng)
    return c, p, i


def operating_level(scores, target=TARGET):
    """§6.1's rule: among ACHIEVABLE thresholds, the one whose achieved coverage is nearest
    `target`. Returns (threshold, achieved p). For a continuous score this is just the
    empirical quantile; for the 9-atom released score it is a genuine choice among 9 levels."""
    u = np.unique(scores)
    F = np.array([(scores <= t).mean() for t in u])
    j = int(np.argmin(np.abs(F - target)))
    return float(u[j]), float(F[j])


def plugin_ratio(scores, starts, sizes, level=None, thresh=None):
    """sqrt(DEFF) from the paper's own formula. Pass `thresh` to pin the threshold exactly
    (required on the atomic score, where a level lookup can straddle an atom boundary)."""
    m_til = float((sizes.astype(float) ** 2).sum() / sizes.sum())
    q = thresh if thresh is not None else np.quantile(scores, level, method="inverted_cdf")
    fams = [(scores[starts[j]:starts[j + 1]] <= q).astype(float) for j in range(len(sizes))]
    rho = anova_icc(fams)
    return float(np.sqrt(1 + (m_til - 1) * rho)), rho, m_til, float((scores <= q).mean())


# ----------------------------------------------------------------- preconditions

def preconditions(fams, scores, starts, sizes, t_star, level, rng):
    """Every check here COULD come out wrong, and names what a failure would look like."""
    print("=" * 78)
    print("PRECONDITIONS — a failure in any one of these invalidates everything below")
    print("=" * 78)
    ok = True

    # P1 — do we still reproduce the published §6.1 inputs? Would fail if the cache changed,
    #      the estimator drifted, or we are reading a different release.
    _, m_bar, m_til = size_profile(fams)
    pr, rho, _, p_ach = plugin_ratio(scores, starts, sizes, thresh=t_star)
    p1 = (abs(m_bar - 50.06) < 0.01 and abs(m_til - 61.29) < 0.01
          and abs(rho - 0.4946) < 0.002 and abs(p_ach - 0.8909) < 0.001
          and abs(1 + (m_til - 1) * rho - 30.8) < 0.1)
    print(f"  P1 published inputs reproduce: m_bar {m_bar:.2f} (50.06), m_tilde {m_til:.2f} "
          f"(61.29), rho_I {rho:.4f} (0.4946),")
    print(f"     DEFF {1 + (m_til - 1) * rho:.1f} (30.8) at threshold {t_star:.3f}, achieved p "
          f"{p_ach:.4f} (0.8909)  -> {'PASS' if p1 else 'FAIL'}")
    print("     would fail if: the cached release changed, or the ANOVA estimator drifted from")
    print("     the one that produced the published DEFF=30.8.")
    ok &= p1

    # P2 — jitter must not reorder across atoms. Would fail if JITTER >= ATOM_SPACING.
    p2 = JITTER < ATOM_SPACING
    print(f"  P2 jitter {JITTER} < atom spacing {ATOM_SPACING}: ranks across atoms preserved "
          f"-> {'PASS' if p2 else 'FAIL'}")
    print("     would fail if: jitter could move a score past the next atom, which would change")
    print("     the empirical CDF rather than merely break ties inside it.")
    ok &= p2

    # P3 — the harness must reproduce i.i.d. sampling when clusters carry no dependence.
    #      Would fail if the resampler, the varying n, or the coverage map introduced spread.
    c_r, p_r, i_r = ratio(scores, starts, sizes, level, rng)
    r_pi = p_r.std(ddof=1) / max(i_r.std(ddof=1), 1e-12)
    p3 = 0.95 < r_pi < 1.05
    print(f"  P3 permuted/iid sd ratio = {r_pi:.3f} (must be ~1)  -> {'PASS' if p3 else 'FAIL'}")
    print("     would fail if: the cluster resampler, the varying resampled n, or the coverage")
    print("     map were themselves generating dispersion. Permuting membership IS i.i.d.")
    print("     sampling with extra steps, so any gap here is the harness, not the data.")
    ok &= p3

    # P4 — GROUND TRUTH. Same size profile, known rho_I, no size-score coupling.
    #      Would fail if Theorem 1, the ANOVA estimator, or this harness were wrong in general.
    #      Averaged over N_SYNTH realisations: at one draw the ratio moves by ~5% between seeds,
    #      which is the same order as the effect being tested and would make P4 unfalsifiable.
    true_rho = 0.4941
    r_g = brentq(lambda r: _rho_gauss(level, r) - true_rho, 1e-4, 0.9999)
    law_true = float(np.sqrt(1 + (m_til - 1) * true_rho))
    plugs, meass, rhos = [], [], []
    for _ in range(N_SYNTH):
        s_sc, s_sz, s_st = _flatten(_synth(sizes, r_g, rng))
        s_plug, s_rho, _, _ = plugin_ratio(s_sc, s_st, s_sz, level=level)
        sc, _, si = ratio(s_sc, s_st, s_sz, level, rng)
        plugs.append(s_plug); rhos.append(s_rho)
        meass.append(sc.std(ddof=1) / si.std(ddof=1))
    s_plug, s_meas, s_rho = float(np.mean(plugs)), float(np.mean(meass)), float(np.mean(rhos))
    p4 = abs(s_plug / s_meas - 1) < 0.10
    print(f"  P4 synthetic ground truth, {N_SYNTH} realisations on the RELEASED size profile,")
    print(f"     TRUE rho_I={true_rho}, sizes drawn independently of scores:")
    print(f"     ANOVA rho_I {s_rho:.4f}  plug-in {s_plug:.2f}  measured {s_meas:.2f}  "
          f"ratio {s_plug / s_meas:.3f}   -> {'PASS' if p4 else 'FAIL'}")
    print(f"     (law at the TRUE rho_I would be {law_true:.2f}; ANOVA runs ~"
          f"{100 * (1 - s_rho / true_rho):.0f}% low on ragged sizes and the two partly cancel —")
    print("      reported because it matters for how the real-data gap is attributed.)")
    print("     would fail if: the law, the estimator or the harness were wrong. This is the")
    print("     check that makes the REAL-DATA gap attributable to the data.")
    ok &= p4

    if not ok:
        print("\n  A PRECONDITION FAILED. No number below may be quoted.")
        raise SystemExit(1)
    print("  all pass.\n")


def _rho_gauss(p, r):
    z = norm.ppf(p)
    d = multivariate_normal.cdf([z, z], mean=[0, 0], cov=[[1, r], [r, 1]])
    return (d - p * p) / (p * (1 - p))


def _synth(sizes, r, rng):
    """One-factor Gaussian clusters on the released size profile, sizes independent of scores."""
    Z = rng.standard_normal(len(sizes))
    return [norm.cdf(np.sqrt(r) * Z[j] + np.sqrt(1 - r) * rng.standard_normal(int(sizes[j])))
            for j in range(len(sizes))]


# ----------------------------------------------------------------- main

def main():
    rng = np.random.default_rng(SEED)
    fams = load()
    scores, sizes, starts = _flatten(fams)
    n = len(scores)
    t_star, level = operating_level(scores)
    print(f"operating point (§6.1's rule: achievable threshold nearest {TARGET}): "
          f"t = {t_star:.3f}, achieved p = {level:.4f}\n")

    preconditions(fams, scores, starts, sizes, t_star, level, rng)

    print("=" * 78)
    print("[1] THE MARGINAL IS ATOMIC — why (A2) fails on the released score (SW-27)")
    print("=" * 78)
    u, ct = np.unique(scores, return_counts=True)
    print(f"    distinct values: {len(u)}   largest atom: {100 * ct.max() / n:.1f}% at "
          f"{u[ct.argmax()]:.3f}")
    print(f"    attainable coverage values F(atom): {np.round(np.cumsum(ct) / n, 4)}")
    print("    (A2) requires F continuous with f(q_p) > 0. It is neither, so Theorem 1's")
    print("    Bahadur step and density cancellation have no purchase on this variable.")

    jit = scores + rng.random(n) * JITTER
    print()
    print("=" * 78)
    print("[2] MEASURED DISPERSION — raw versus tie-broken, against the plug-in")
    print("=" * 78)
    print(f"    {'arm':<12}{'cluster sd':>12}{'iid sd':>10}{'MEASURED':>10}{'plug-in':>10}")
    results = {}
    for lbl, sc in (("raw", scores), ("tie-broken", jit)):
        c, p, i = ratio(sc, starts, sizes, level, rng)
        plug, rho, m_til, p_ach = plugin_ratio(
            sc, starts, sizes, level=level, thresh=(t_star if lbl == "raw" else None))
        meas = c.std(ddof=1) / max(i.std(ddof=1), 1e-12)
        results[lbl] = (c, i, meas, plug, rho)
        print(f"    {lbl:<12}{c.std(ddof=1):>12.5f}{i.std(ddof=1):>10.5f}"
              f"{meas:>10.2f}{plug:>10.2f}")
        print(f"    {'':<12}rho_I {rho:.4f} at achieved p {p_ach:.4f}; "
              f"5-95 cluster [{np.percentile(c, 5):.4f}, {np.percentile(c, 95):.4f}], "
              f"iid [{np.percentile(i, 5):.4f}, {np.percentile(i, 95):.4f}]")
    print()
    print(f"    PAPER PRINTS 5.6x and [0.873, 0.909] vs [0.888, 0.894].")
    print(f"    Raw score        : {results['raw'][2]:.2f}x — the effect is invisible; "
          f"discreteness dominates.")
    print(f"    Tie-broken       : {results['tie-broken'][2]:.2f}x — real, large, and NOT 5.6.")
    print(f"    Mean coverage, tie-broken cluster arm: {results['tie-broken'][0].mean():.4f} "
          f"(nominal {level:.4f})")

    print()
    print("=" * 78)
    print("[3] LOCALISING THE 28% GAP — it tracks the size-score coupling (SW-24)")
    print("=" * 78)
    print(f"    {'subset':<16}{'b':>5}{'CV^2':>8}{'spearman':>10}{'plug-in':>9}"
          f"{'measured':>10}{'ratio':>8}")
    for lo, hi, lbl in ((0, 10**9, "all 500"), (35, 70, "sizes 35-70"), (40, 60, "sizes 40-60")):
        keep = np.where((sizes >= lo) & (sizes <= hi))[0]
        sub = [jit[starts[j]:starts[j + 1]] for j in keep]
        s_sc, s_sz, s_st = _flatten(sub)
        cv2 = float((s_sz.astype(float) ** 2).sum() / s_sz.sum()) / s_sz.mean() - 1
        means = np.array([s_sc[s_st[j]:s_st[j + 1]].mean() for j in range(len(s_sz))])
        rho_sz = spearmanr(s_sz, means).statistic
        plug, _, _, _ = plugin_ratio(s_sc, s_st, s_sz, level=level)
        c, _, i = ratio(s_sc, s_st, s_sz, level, rng)
        meas = c.std(ddof=1) / max(i.std(ddof=1), 1e-12)
        print(f"    {lbl:<16}{len(s_sz):>5}{cv2:>8.3f}{rho_sz:>10.3f}{plug:>9.2f}"
              f"{meas:>10.2f}{plug / meas:>8.2f}")
    print()
    print("    As the coupling is removed the plug-in converges on the measurement. P4 shows")
    print("    the same size profile WITHOUT coupling has no gap, so the driver is")
    print("    informativeness, not size dispersion. Proposition 2 needs that scope condition.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
