"""Selection-on-score: the dose-response curve, in simulation, before the real run.

    python experiments/2026-07-26-sw02-exchangeability-audit/selection_dose_response.py

WHAT THIS TESTS
SW-02 §3.5, general form: if membership in the calibration set depends on the score being
calibrated, the calibration marginal is not the test marginal and the threshold moves at first
order, with the sign of the shift given by the sign of the dependence.

FT-17's demonstration measured two points on that curve with a real substrate: label errors that
are score-CORRELATED make a selective-answering certificate permissive (realised false-answer rate
2.46x nominal), while errors at the SAME RATE chosen at random make it conservative (0.08x). The
natural next run interpolates. This script runs the theory arm of that interpolation on synthetic
data, so the empirical curve has something to be compared against.

PRE-REGISTERED PREDICTION (written before running; see the assessment that accompanied it)
  P1. The realised false-answer rate is MONOTONE in the error-score correlation.
  P2. It crosses nominal alpha EXACTLY ONCE.
  P3. The crossing sits at no natural value -- in particular not at correlation 0 -- so a
      model-anchored certificate is only accidentally valid.
A non-monotone curve, or more than one crossing, falsifies the selection-on-score account as
stated. That is the point of running it.

SETUP (an abstraction of the FT-17 gate, not a replica of its substrate)
  - item score s ~ N(0,1); higher = more confident.
  - true correctness c ~ Bernoulli(sigmoid(a + b s)), so errors concentrate at low scores.
  - the certifier calibrates on INCORRECT items and sets tau at their (1-alpha) order statistic,
    so that at most alpha of incorrect items score above tau.
  - the gate answers when s >= tau. FALSE ANSWER = incorrect item that is answered.
  - a LABELER supplies the correctness labels used for calibration. It errs on a fixed fraction
    `err_rate` of items. WHICH items it errs on is the dial:
        rho_e = 0 -> errors drawn uniformly from OUTSIDE the self-referential disagreement set
        rho_e = 1 -> errors are exactly that set                (FT-17 arm M, self-referential)
    Error RATE is held constant across the sweep; only the composition changes. That is the
    comparison FT-17 made, and it is what isolates correlation from rate.

CAUTION ON THE rho_e = 0 ENDPOINT (integrity.md SW-17)
It is NOT the uniformly-random labeler and it is NOT FT-17's arm N, though earlier versions of
this docstring said both. Drawing the flip set from the COMPLEMENT of the self-referential
disagreement set anti-selects on the score, so this endpoint carries a POSITIVE error-score
correlation by construction: +0.042, +0.068, +0.136 at err_rate = 0.105, 0.211, 0.350, against a
genuinely uniform control at 0.000 +/- 0.017 (up to 8 sigma; measured in `sw15_epsilon_matched.py`,
which also carries the uniform control). The bias grows with err_rate because the excluded set does.

The consequence that matters: the sweep's correlation axis runs from +offset to -max, not from 0
to -max. A crossing expressed as a FRACTION of attainable correlation is therefore NOT comparable
to one measured on an implementation whose zero endpoint really is zero -- which both empirical
arms are. Correcting the origin moves this file's crossing from 75% to 81%.

What is unaffected: monotonicity, convexity, the single crossing, and the direction of the two
endpoints (rho_e=0 conservative, rho_e=1 permissive). The offset slides the crossing along a
rescaled axis rather than bending the curve, so every claim the paper draws from this script
stands. If anything a true uniform arm would make the conservative endpoint less extreme.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from _conformal import split_conformal  # noqa: E402

N_CAL, N_TEST, ALPHA, REPS, SEED = 4000, 20000, 0.10, 400, 0
ERR_RATE = 0.21          # matches FT-17's arm N / arm M error rate
A, B = 1.3, 1.6          # correctness ~ sigmoid(A + B s); ~21% base error rate


def sigmoid(x):
    return 1.0 / (1.0 + np.exp(-x))


def draw(rng, n):
    s = rng.normal(size=n)
    c = (rng.random(n) < sigmoid(A + B * s)).astype(bool)   # True = correct
    return s, c


def self_referential_labels(s, c, err_rate):
    """The rho_e=1 labeler: it IS a threshold on the score being certified.

    This is CommCP's actual practice -- ground truth defined as "the single option with the
    highest LLM confidence". Its label is c_hat = (s >= t*), with t* chosen so that its
    disagreement rate with the truth equals err_rate, holding the rate comparable to the
    random-error arm. Returns the boolean disagreement mask.
    """
    grid = np.quantile(s, np.linspace(0.01, 0.99, 199))
    rates = np.array([np.mean((s >= t) != c) for t in grid])
    t_star = grid[int(np.argmin(np.abs(rates - err_rate)))]
    return ((s >= t_star) != c)


def corrupt(rng, s, c, rho_e, err_rate):
    """Flip `err_rate` of labels; rho_e controls WHICH ones, holding the RATE fixed.

    rho_e = 0 -> the flipped set is uniform over the COMPLEMENT of the
                 self-referential disagreement set -- NOT uniform over all
                 items, and NOT FT-17 arm N. See the module docstring's
                 caution and integrity.md SW-17: this endpoint sits at a
                 positive error-score correlation, not at zero.
    rho_e = 1 -> the flipped set is exactly the self-referential
                 labeler's disagreement set                             (FT-17 arm M)
    in between -> a rho_e FRACTION of the fixed error budget is drawn from the
                  self-referential disagreement set and the rest uniformly from elsewhere.
                  "Elsewhere" is what makes rho_e=0 a biased rather than neutral endpoint.

    NOTE ON THE DIAL. An earlier version mixed a propensity score,
    prop = rho_e*disagree + (1-rho_e)*uniform, and took the top k. That SATURATES: for any
    rho_e >= 0.5 every disagreement item outranks every other item, so the flip set stops
    changing and the curve is exactly flat from 0.5 to 1.0. The allocation form below has no
    such artifact -- the error rate is still identical at every rho_e, but the composition
    moves linearly across the whole range.
    """
    n = s.size
    k = int(round(err_rate * n))
    if k == 0:
        return c.copy()
    dis_mask = self_referential_labels(s, c, err_rate)
    dis_idx = np.flatnonzero(dis_mask)
    oth_idx = np.flatnonzero(~dis_mask)
    n_dis = min(int(round(rho_e * k)), dis_idx.size)
    n_oth = min(k - n_dis, oth_idx.size)
    flip = np.concatenate([
        rng.choice(dis_idx, size=n_dis, replace=False),
        rng.choice(oth_idx, size=n_oth, replace=False),
    ])
    out = c.copy()
    out[flip] = ~out[flip]
    return out


def one_rep(rng, rho_e, err_rate=None):
    err_rate = ERR_RATE if err_rate is None else err_rate
    s, c = draw(rng, N_CAL)
    c_hat = corrupt(rng, s, c, rho_e, err_rate)
    # MEASURED error-score correlation (point-biserial): the x-axis the empirical run uses.
    # rho_e is an allocation knob, NOT a correlation -- the two are not on the same scale and
    # crossings quoted on one axis cannot be compared to crossings on the other.
    errs = (c_hat != c).astype(float)
    meas_corr = (float(np.corrcoef(errs, s)[0, 1])
                 if 0 < errs.sum() < errs.size else float("nan"))
    wrong = s[~c_hat]                                       # calibrate on labelled-incorrect
    if wrong.size < 5:
        return np.nan, np.nan
    # tau = ceil((n+1)(1-alpha))-th smallest of the incorrect-item scores, so that at most
    # alpha of incorrect items score above it. Higher score = more confident = answered.
    tau = split_conformal(wrong, ALPHA)
    st, ct = draw(rng, N_TEST)                              # test uses TRUE labels
    answered = st >= tau
    false_answer = float(np.mean(answered & ~ct) / max(np.mean(~ct), 1e-12))
    over_refusal = float(np.mean(~answered & ct) / max(np.mean(ct), 1e-12))
    return false_answer, over_refusal, meas_corr


def precondition() -> bool:
    """Truth-anchored control: with NO label errors the gate must deliver alpha.

    Asserted before anything else, because a dose-response curve whose baseline is wrong is
    just a shape. (Lesson borrowed from FT-17's first run, where matching rates hid a broken
    denominator: check the control, not only the contrast.)
    """
    rng = np.random.default_rng(SEED)
    res = np.array([one_rep(rng, 0.0, err_rate=0.0) for _ in range(200)])
    fa = float(np.nanmean(res[:, 0]))
    ok = abs(fa - ALPHA) < 0.01
    print(f"[0] PRECONDITION — truth-anchored (err_rate=0): FA={fa:.4f} vs alpha={ALPHA} "
          f"({fa/ALPHA:.2f}x)  {'PASS' if ok else 'FAIL'}")
    return ok


def robustness() -> None:
    """Does the cliff survive changes to error rate and to how discriminative the score is?"""
    print("\n[2] ROBUSTNESS — FA/alpha at each rho_e, across settings")
    print(f"{'err':>5} {'B':>5} " + " ".join(f"{r:>6.1f}" for r in np.linspace(0, 1, 6)))
    global A, B, ERR_RATE
    A0, B0, E0 = A, B, ERR_RATE
    for err in (0.10, 0.21, 0.35):
        for b in (0.8, 1.6, 3.0):
            B, ERR_RATE = b, err
            row = []
            for rho_e in np.linspace(0, 1, 6):
                rng = np.random.default_rng(SEED)
                res = np.array([one_rep(rng, rho_e) for _ in range(120)])
                row.append(float(np.nanmean(res[:, 0])) / ALPHA)
            print(f"{err:>5.2f} {b:>5.1f} " + " ".join(f"{v:>6.2f}" for v in row))
    A, B, ERR_RATE = A0, B0, E0


def main() -> int:
    if not precondition():
        print("    precondition failed — the curve below is not interpretable")
    rhos = np.linspace(0.0, 1.0, 11)
    print(f"\nselection-on-score dose response — error rate fixed at {ERR_RATE:.0%}, "
          f"alpha={ALPHA}, {REPS} reps")
    print(f"{'rho_e':>6} {'meas.corr':>10} {'FA rate':>9} {'vs alpha':>9} {'over-refusal':>13} {'verdict':>13}")
    fa_curve, corr_curve = [], []
    for rho_e in rhos:
        rng = np.random.default_rng(SEED)
        res = np.array([one_rep(rng, rho_e) for _ in range(REPS)])
        m = float(np.nanmean(res[:, 0]))
        orf = float(np.nanmean(res[:, 1]))
        mc = float(np.nanmean(res[:, 2]))
        fa_curve.append(m)
        corr_curve.append(mc)
        verdict = "conservative" if m < ALPHA * 0.9 else (
            "PERMISSIVE" if m > ALPHA * 1.1 else "~nominal")
        print(f"{rho_e:>6.2f} {mc:>10.3f} {m:>9.4f} {m/ALPHA:>8.2f}x {orf:>13.4f} {verdict:>13}")

    fa_curve = np.array(fa_curve)
    corr_curve = np.array(corr_curve)
    # Monotone in EITHER direction: the sign of the measured correlation depends on whether the
    # score is a confidence (higher = better, as here) or a nonconformity score (higher = weirder,
    # as in the empirical run). Only the magnitude and the ordering are comparable across the two.
    dx = np.diff(corr_curve)
    mono_x = bool(np.all(dx >= -1e-3) or np.all(dx <= 1e-3))
    print(f"\n  SWEEP-VARIABLE CHECK — measured corr monotone in the knob? "
          f"{'YES' if mono_x else 'NO  <-- unaccounted variance in the labeler draw'}")
    print(f"     range |corr| {abs(corr_curve[0]):.3f} -> {abs(corr_curve[-1]):.3f}")
    d = np.diff(fa_curve)
    monotone = bool(np.all(d >= -1e-4) or np.all(d <= 1e-4))
    crossings = int(np.sum(np.diff(np.sign(fa_curve - ALPHA)) != 0))
    print(f"\n  P1 monotone in rho_e?        {'YES' if monotone else 'NO  <-- FALSIFIED'}")
    print(f"  P2 exactly one crossing of a? {'YES' if crossings == 1 else f'NO ({crossings}) <-- FALSIFIED'}")
    if crossings == 1:
        i = int(np.where(np.diff(np.sign(fa_curve - ALPHA)) != 0)[0][0])
        lo, hi = fa_curve[i], fa_curve[i + 1]
        x = rhos[i] + (ALPHA - lo) / (hi - lo) * (rhos[i + 1] - rhos[i])
        cx = corr_curve[i] + (ALPHA - lo) / (hi - lo) * (corr_curve[i + 1] - corr_curve[i])
        print(f"  P3 crossing at rho_e =        {x:.3f} (allocation knob)")
        print(f"     crossing at MEASURED corr = {cx:.3f}  <- the axis comparable to the "
              f"empirical run")
    robustness()
    print("\n  Direction check against FT-17: rho_e=0 should be conservative, rho_e=1 permissive.")
    print(f"    rho_e=0.0 -> {fa_curve[0]/ALPHA:.2f}x   rho_e=1.0 -> {fa_curve[-1]/ALPHA:.2f}x")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
