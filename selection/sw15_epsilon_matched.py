"""SW-15: is the crossing-as-fraction-of-attainable-correlation stable, or just epsilon-dependent?

    python experiments/2026-07-26-sw02-exchangeability-audit/sw15_epsilon_matched.py

THE ISSUE (paper/integrity.md SW-15)
Section 10 reports the crossing expressed as a fraction of the maximum attainable error-score
correlation as "64-79% across three settings": 79% and 64% from two empirical arms at
eps = 0.105 and 0.211, and 75% from the synthetic replication in selection_dose_response.py.
Three numbers in a 15-point band was floated, in an intermediate draft, as a stable invariant.
It is not established as one. The two empirical values come from ONE substrate at two error
rates and differ by 14.7 points -- a spread as large as the gap to the synthetic value -- so
the apparent cross-implementation agreement is not distinguishable from the fraction simply
varying with eps.

WHAT THIS RUN ADDS
The synthetic already sits at eps = 0.21 (selection_dose_response.ERR_RATE, whose comment says
it matches the empirical arm), so a matched-eps comparison at 0.21 is 75% synthetic vs 64%
empirical. One matched point cannot separate the two explanations. What separates them is the
SLOPE: sweep eps in the synthetic across the empirical range and ask whether the fraction moves
with eps the way the empirical pair does.

PRE-REGISTERED PREDICTIONS (written before running)
  H-A "substrate-stable, eps-dependent": the fraction is a function of eps that both substrates
      roughly share. Signature: synthetic fraction RISES as eps falls, by something near the
      empirical +14.7 points from eps 0.211 -> 0.105. Under H-A the 64-79% band is a coincidence
      of the eps values sampled, not an invariant, and the honest object is a curve in
      (eps, fraction).
  H-B "eps-independent, substrate-dependent": the synthetic fraction is FLAT in eps. The
      empirical 79->64 movement is then a property of that substrate, and the 11-point
      synthetic-vs-empirical gap at matched eps = 0.21 is the real signal.
  H-C "no structure": the fraction moves non-monotonically or with error bars wide enough to
      cover the whole 64-79 band, in which case the band is not measuring anything.

  DISCRIMINATOR, fixed in advance: fit the synthetic fraction against eps over
  [0.105, 0.211]. Call it H-A if the change has the same SIGN as the empirical (-) and a
  magnitude within a factor of 2 of the empirical 14.7 points (so 7.4 to 29.4 points of RISE as
  eps falls). Call it H-B if |change| < 5 points. Anything else is H-C.

  Under every one of the three, "64-79% is a stable invariant" stays dead. This run decides
  what replaces it in the text, not whether the correction was needed.

FOUND DURING THE RUN, NOT PRE-REGISTERED (flagged as post hoc, because it is)
The sweep-variable check fired at every eps, which turned out to be two separate things.
(i) My check tested |corr| for monotonicity; the correlation passes through zero mid-sweep, so
    |corr| necessarily dips and the check reports a false alarm. Fixed to test signed corr,
    which is monotone at every eps.
(ii) Chasing (i) surfaced a real defect: the rho_e=0 endpoint is NOT at correlation zero. It
     sits at +0.04 to +0.14, growing with eps, because `corrupt` draws the rho_e=0 flip set
     from the complement of the self-referential disagreement set rather than uniformly. Both
     empirical arms start at exactly 0.00, so |cross|/|max| is measured from a different origin
     in the two implementations. Convention B below corrects for it. The [A] block is the
     evidence; it is a construction artifact, not sampling noise, at up to 8 sigma.
This means the published 75% and the empirical 64%/79% were never the same quantity.

PRECONDITION
The published synthetic number must be reproduced by THIS script's crossing estimator before any
sweep value is read. The estimator here is not the one in selection_dose_response.py -- that one
interpolates the crossing linearly on a curve it separately proves is convex, which biases the
crossing low. This script interpolates log(FA), which is near-linear for this curve. If the two
disagree materially the published 75% is an artifact of the estimator and that, not the sweep,
is the finding.

ERROR BARS
The published 75% is a single seed with no stated uncertainty -- quoting a crossing without its
spread is the P4 failure SW-15 is itself an instance of. Every fraction below is reported as
mean +/- sd over N_SEEDS independent labeler draws.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[1]))

import selection_dose_response as sdr  # noqa: E402

ALPHA = sdr.ALPHA
RHO_GRID = np.linspace(0.0, 1.0, 26)
EPSILONS = [0.105, 0.15, 0.211, 0.28, 0.35]
N_SEEDS = 8
REPS = 150

# The two empirical arms. Fixed constants, not measured here.
#
# These are the RECORDED fractions from integrity.md, not values re-derived from Section 10's
# table. The table displays the eps=0.105 arm's maximum attainable correlation rounded to 0.29;
# the unrounded value is 0.2852, so 0.225/0.29 gives 77.6% where the real figure is 78.9%. Deriving
# from the rounded table also understates the empirical movement as 13.5 points instead of 14.7 --
# which is the number Section 10 itself quotes, and the discrepancy is how the rounding was caught.
EMP_FRAC = {0.105: 0.789, 0.211: 0.642}              # eps -> crossing as fraction of attainable


def curve(seed: int, eps: float):
    """FA and measured-correlation curves over RHO_GRID at a fixed error rate."""
    fa, corr = [], []
    for rho_e in RHO_GRID:
        rng = np.random.default_rng(seed)
        res = np.array([sdr.one_rep(rng, rho_e, err_rate=eps) for _ in range(REPS)])
        fa.append(float(np.nanmean(res[:, 0])))
        corr.append(float(np.nanmean(res[:, 2])))
    return np.array(fa), np.array(corr)


def crossing(fa, corr):
    """Correlation at which FA crosses ALPHA, interpolating log(FA) against rho.

    Returns (corr_at_crossing, n_crossings). log-space because the FA curve rises by more than
    an order of magnitude across the sweep and is convex throughout; linear interpolation on a
    convex curve places the crossing systematically low.
    """
    sign = np.sign(fa - ALPHA)
    idx = np.flatnonzero(np.diff(sign) != 0)
    if idx.size != 1:
        return float("nan"), int(idx.size)
    i = int(idx[0])
    lo, hi = fa[i], fa[i + 1]
    if lo <= 0 or hi <= 0:
        return float("nan"), 1
    w = (np.log(ALPHA) - np.log(lo)) / (np.log(hi) - np.log(lo))
    return float(corr[i] + w * (corr[i + 1] - corr[i])), 1


def truly_uniform(rng, s, c, err_rate):
    """Control for the rho_e=0 arm: flip set drawn uniformly over ALL items.

    This is what selection_dose_response's docstring says rho_e=0 is ("errors chosen uniformly
    at random", FT-17 arm N). What `corrupt` actually does at rho_e=0 is draw from `oth_idx`,
    the COMPLEMENT of the self-referential disagreement set — which anti-selects on the score
    and so carries a positive error-score correlation by construction.
    """
    k = int(round(err_rate * s.size))
    flip = rng.choice(s.size, size=k, replace=False)
    out = c.copy()
    out[flip] = ~out[flip]
    return out


def origin_check() -> None:
    """Is the rho_e=0 endpoint at correlation zero, as the empirical arms are?

    This decides whether the fraction is even comparable across implementations. The empirical
    arms both run 0.00 -> max. If the synthetic runs offset -> max instead, then |cross|/|max|
    is measured from a different origin in the two, and the 64-79% band is not three
    measurements of one quantity.
    """
    print("\n[A] ORIGIN CHECK — is the rho_e=0 arm actually uncorrelated with the score?")
    print(f"{'eps':>6} {'as coded':>20} {'uniform control':>22} {'offset':>9}")
    for eps in EPSILONS:
        a, b = [], []
        rng = np.random.default_rng(sdr.SEED)
        for _ in range(300):
            s, c = sdr.draw(rng, sdr.N_CAL)
            e = (sdr.corrupt(rng, s, c, 0.0, eps) != c).astype(float)
            a.append(np.corrcoef(e, s)[0, 1])
            e2 = (truly_uniform(rng, s, c, eps) != c).astype(float)
            b.append(np.corrcoef(e2, s)[0, 1])
        sd = np.std(b)
        print(f"{eps:>6.3f} {np.mean(a):>+14.4f} ±{np.std(a):.4f} {np.mean(b):>+16.4f} ±{sd:.4f} "
              f"{abs(np.mean(a))/sd:>7.1f}σ")
    print("    -> the as-coded arm is NOT arm N. Fraction is therefore reported both ways below.")


def precondition() -> bool:
    """Reproduce the published 75% with this script's estimator, at the published settings."""
    print("[0] PRECONDITION — reproduce the published synthetic fraction (eps=0.21, seed=0)")
    fa, corr = curve(sdr.SEED, 0.21)
    cx, n = crossing(fa, corr)
    frac = abs(cx) / abs(corr[-1])
    print(f"    crossing corr {cx:+.3f}   max attainable {corr[-1]:+.3f}   "
          f"fraction {frac:.1%}   crossings={n}")
    print(f"    published: crossing -0.186, max -0.247, fraction 75.3%")
    ok = n == 1 and abs(frac - 0.753) < 0.05
    print(f"    within 5 points of published?  {'PASS' if ok else 'FAIL'}")
    if not ok:
        print("    -> the published 75% is estimator-dependent; report THAT, not the sweep")
    return ok


def main() -> int:
    ok = precondition()
    origin_check()

    print(f"\n[1] EPSILON SWEEP — fraction of attainable correlation at the crossing")
    print(f"    {N_SEEDS} seeds x {REPS} reps x {RHO_GRID.size} rho values per epsilon")
    print(f"    A = |cross|/|max|              — the published convention, origin assumed at 0")
    print(f"    B = (cross-start)/(max-start)  — origin at the sweep's actual rho_e=0 endpoint,")
    print(f"                                     which [A] shows is not 0. B is like-with-like.\n")
    print(f"{'eps':>6} {'start':>8} {'cross':>8} {'max':>8} {'A':>14} {'B':>14} "
          f"{'mono':>5} {'empirical':>10}")
    outA, outB = {}, {}
    for eps in EPSILONS:
        fa_, fb_, cx, mx, st, mono_ok = [], [], [], [], [], True
        for s in range(N_SEEDS):
            fa, corr = curve(s, eps)
            c, n = crossing(fa, corr)
            if n != 1 or not np.isfinite(c):
                continue
            # SWEEP-VARIABLE CHECK on the SIGNED correlation. Not |corr|: the correlation passes
            # through zero mid-sweep (see [A]), so |corr| necessarily dips and a check on it
            # reports a false alarm at every eps.
            d = np.diff(corr)
            if not (np.all(d >= -2e-3) or np.all(d <= 2e-3)):
                mono_ok = False
            fa_.append(abs(c) / abs(corr[-1]))
            fb_.append((c - corr[0]) / (corr[-1] - corr[0]))
            cx.append(c); mx.append(corr[-1]); st.append(corr[0])
        if not fa_:
            print(f"{eps:>6.3f}  no single crossing at any seed — curve does not cross alpha")
            continue
        fa_, fb_ = np.array(fa_), np.array(fb_)
        outA[eps], outB[eps] = fa_, fb_
        emp = f"{EMP_FRAC[eps]:.1%}" if eps in EMP_FRAC else "—"
        print(f"{eps:>6.3f} {np.mean(st):>+8.3f} {np.mean(cx):>+8.3f} {np.mean(mx):>+8.3f} "
              f"{np.mean(fa_):>9.1%} ±{np.std(fa_):.1%} {np.mean(fb_):>9.1%} ±{np.std(fb_):.1%} "
              f"{'YES' if mono_ok else 'NO':>5} {emp:>10}")

    print("\n[2] VERDICT — read off convention B")
    for tag, out in (("A (published)", outA), ("B (like-with-like)", outB)):
        if not (0.105 in out and 0.211 in out):
            continue
        lo, hi = out[0.105], out[0.211]
        change = (np.mean(lo) - np.mean(hi)) * 100          # points of RISE as eps falls
        se = np.hypot(np.std(lo), np.std(hi)) * 100 / np.sqrt(N_SEEDS)
        emp_change = (EMP_FRAC[0.105] - EMP_FRAC[0.211]) * 100
        span = (max(np.mean(v) for v in out.values())
                - min(np.mean(v) for v in out.values())) * 100
        if change > 0 and emp_change / 2 <= change <= emp_change * 2:
            v = "H-A  substrate-stable, eps-dependent"
        elif abs(change) < 5:
            v = "H-B  eps-independent — empirical movement is substrate-specific"
        else:
            v = "H-C  no shared structure"
        m = np.mean(out[0.211])
        gap = abs(m - EMP_FRAC[0.211]) * 100
        print(f"\n  convention {tag}")
        print(f"    eps 0.211 -> 0.105 : synthetic {change:+.1f} pts (se {se:.1f})   "
              f"empirical {emp_change:+.1f} pts")
        print(f"    span across all {len(out)} eps (a {max(EPSILONS)/min(EPSILONS):.1f}x range): "
              f"{span:.1f} points")
        print(f"    matched-eps at 0.211: synthetic {m:.1%} vs empirical "
              f"{EMP_FRAC[0.211]:.1%}  -> gap {gap:.1f} points")
        print(f"    -> {v}")
    if not ok:
        print("\n    NOTE: precondition failed — read [1] as an estimator finding, not a sweep.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
