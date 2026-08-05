"""SW-02 §6 — measuring the design effect on a REAL PRM calibration set.

    python experiments/2026-07-26-sw02-exchangeability-audit/prm_measurement.py

Converts the paper's live instance from an argument into a measurement.

THE ARTIFACT
Park, Greenewald, Alim, Wang & Azizan, "Know What You Don't Know: Uncertainty Calibration of
Process Reward Models" (NeurIPS 2025, arXiv:2506.09338) release their calibration sets at
https://huggingface.co/datasets/young-j-park/prm_calibration -- (question, reasoning_prefix,
success_prob) triplets. Their Theorem 2 invokes split-conformal exchangeability directly on this
set. Every row is a PREFIX of a reasoning trajectory, and rows from the same question share
prefixes by construction, so the exchangeability assumption is applied to data with explicit
family structure. The paper reports no test of it.

WHAT IS MEASURED HERE
1. The size profile, and hence m_tilde -- EXACT and assumption-free. This alone determines how
   much the naive average family size understates the design effect.
2. rho_I(p), the ICC of the exceedance indicator, at each achievable threshold, giving
   n_eff = n/(1 + (m_tilde - 1) rho_I(p)) -- on real data. Estimated by one-way ANOVA, NOT by
   the same-family-pair ratio: with sizes ranging 8 to 135, the pair estimator is inconsistent
   (it weights families by m_j(m_j-1) while p_hat weights by m_j) and returned rho_I > 1 here
   before this was corrected. The naive value is still computed and returned for comparison.
3. The score-level ICC of success_prob, for comparison, to show on a real artifact how far apart
   the two quantities are.

HONEST SCOPE -- read before quoting any number
- Clusters here are QUESTIONS. Question-level grouping is the correct level for their Theorem 2,
  which asserts exchangeability over the whole set.
  *** CORRECTED 2026-08-02 (SW-63). This paragraph used to end "the release carries no trajectory
  index, so same-trajectory and cross-trajectory pairs cannot be separated ... therefore a LOWER
  BOUND on the family correlation." That is FALSE and the paper says so: §6.1 reconstructs the
  chains by string-prefixing (reasoning_prefix is the literal text), finds 3,961 maximal chains,
  measures rho_I = 0.688 at the trajectory level against 0.495 at the question level, and concludes
  the trajectory DEFF is SMALLER (7.06 vs 30.8) because m_tilde falls 61.3 -> 9.8. So 30.8 is the
  COMPLETE number, not a lower bound. Independently reproduced by ../prefix_tree_structure.py at
  0.6856 / 0.4946. Do not reinstate the lower-bound language; it cost a day of rediscovery. ***
- success_prob is the calibrated TARGET, not their nonconformity score (a residual from a
  quantile-regression head not included in the release). rho_I of their actual score would
  differ. What is exact here is m_tilde and the family structure; rho_I is measured on the
  target variable and labelled as such.
- success_prob is a Monte Carlo estimate over 8 rollouts, so it takes only 9 distinct values with
  67% of mass at exactly 0. Thresholds are therefore coarse and only certain coverage levels are
  achievable. Reported as achieved, not interpolated.
"""

from __future__ import annotations

import collections
import json
import sys
import urllib.request
from pathlib import Path

import numpy as np

URL = ("https://huggingface.co/datasets/young-j-park/prm_calibration/"
       "resolve/main/math500/Llama-3.2-1B-Instruct/data.json")
CACHE = Path(__file__).resolve().parent / "prm_calibration_cache.json"


def load():
    if not CACHE.exists():
        print(f"downloading {URL}")
        urllib.request.urlretrieve(URL, CACHE)
    rows = json.loads(CACHE.read_text())
    fam = collections.defaultdict(list)
    for r in rows:
        fam[r["question"]].append(float(r["success_prob"]))
    return [np.asarray(v) for v in fam.values()]


def size_profile(fams):
    sizes = np.array([len(f) for f in fams], dtype=float)
    m_bar = sizes.mean()
    m_til = float((sizes ** 2).sum() / sizes.sum())
    return sizes, m_bar, m_til


def anova_icc(fams_binary):
    """One-way random-effects ICC. The correct estimator when cluster sizes are unequal.

    The naive pair estimator delta_hat = sum C(c_j,2) / sum C(m_j,2) paired with a
    point-weighted p_hat is INCONSISTENT under unequal sizes: delta_hat weights families by
    m_j(m_j-1) while p_hat weights by m_j, so if larger families have higher rates the ratio
    can exceed 1 -- impossible for a correlation, and observed here before this was fixed.
    """
    sizes = np.array([len(f) for f in fams_binary], dtype=float)
    k = len(fams_binary)
    n = sizes.sum()
    grand = np.concatenate(fams_binary).mean()
    means = np.array([f.mean() for f in fams_binary])
    ssb = float((sizes * (means - grand) ** 2).sum())
    ssw = float(sum(((f - f.mean()) ** 2).sum() for f in fams_binary))
    msb, msw = ssb / (k - 1), ssw / (n - k)
    m0 = (n - (sizes ** 2).sum() / n) / (k - 1)
    return float((msb - msw) / (msb + (m0 - 1) * msw))


def indicator_icc(fams, t):
    """rho_I at threshold t. Returns (p_hat, delta_pair_naive, rho_I_anova)."""
    below = [(f <= t).sum() for f in fams]
    sizes = [len(f) for f in fams]
    n = sum(sizes)
    p_hat = sum(below) / n
    pairs_both = sum(c * (c - 1) / 2 for c in below)
    pairs_tot = sum(m * (m - 1) / 2 for m in sizes)
    delta_naive = pairs_both / pairs_tot
    if not (0 < p_hat < 1):
        return p_hat, delta_naive, float("nan")
    return p_hat, delta_naive, anova_icc([(f <= t).astype(float) for f in fams])


def score_icc(fams):
    """One-way random-effects ICC of the raw score, for comparison."""
    return anova_icc(fams)


def main() -> int:
    fams = load()
    sizes, m_bar, m_til = size_profile(fams)
    n = int(sizes.sum())

    print(f"\n[1] FAMILY STRUCTURE  (clusters = questions)")
    print(f"    rows n            = {n}")
    print(f"    families b        = {len(fams)}")
    print(f"    sizes             = min {int(sizes.min())}, median {int(np.median(sizes))}, "
          f"max {int(sizes.max())}")
    print(f"    m_bar             = {m_bar:.2f}")
    print(f"    m_tilde           = {m_til:.2f}   <- size-biased mean, the one that matters")
    print(f"    CV^2              = {m_til/m_bar - 1:.3f}")
    print(f"    exact, assumption-free: using m_bar understates (m-1) by "
          f"{(m_til-1)/(m_bar-1) - 1:+.1%}")

    print(f"\n[2] SCORE-LEVEL ICC (for comparison, NOT the governing quantity)")
    print(f"    ICC(success_prob) = {score_icc(fams):.4f}")

    print(f"\n[3] INDICATOR ICC AND EFFECTIVE SAMPLE SIZE, BY ACHIEVABLE THRESHOLD")
    print(f"{'thresh':>7} {'coverage p':>11} {'rho_I':>7} {'DEFF':>7} "
          f"{'n_eff':>8} {'n_eff/n':>8}")
    for t in sorted(set(np.concatenate(fams)))[:-1]:
        p_hat, delta, ri = indicator_icc(fams, t)
        if not (0.30 < p_hat < 0.999) or np.isnan(ri):
            continue
        deff = 1 + (m_til - 1) * ri
        print(f"{t:>7.3f} {p_hat:>11.4f} {ri:>7.4f} {deff:>7.2f} "
              f"{n/deff:>8.1f} {1/deff:>8.3f}")

    print("\n[4] WHAT THIS MEANS FOR THEIR REPORTED GUARANTEE")
    cands = []
    for t in sorted(set(np.concatenate(fams)))[:-1]:
        p_hat, delta, ri = indicator_icc(fams, t)
        if 0.30 < p_hat < 0.999 and not np.isnan(ri):
            cands.append((abs(p_hat - 0.90), t, p_hat, ri))
    if cands:
        _, t, p_hat, ri = min(cands)
        deff = 1 + (m_til - 1) * ri
        n_eff = n / deff
        sd_nom = np.sqrt(p_hat * (1 - p_hat) / n)
        sd_true = np.sqrt(p_hat * (1 - p_hat) / n_eff)
        print(f"    nearest achievable level to 0.90: p = {p_hat:.4f} (threshold {t:.3f})")
        print(f"    rho_I = {ri:.4f}, DEFF = {deff:.1f}")
        print(f"    n = {n} calibration points carry n_eff = {n_eff:.0f} points of information")
        print(f"    coverage sd if exchangeable : {sd_nom:.4f}")
        print(f"    coverage sd as clustered    : {sd_true:.4f}   "
              f"({sd_true/sd_nom:.1f}x wider)")
        print(f"    5th-95th pct of achieved coverage: "
              f"[{p_hat - 1.645*sd_true:.3f}, {p_hat + 1.645*sd_true:.3f}] "
              f"vs [{p_hat - 1.645*sd_nom:.3f}, {p_hat + 1.645*sd_nom:.3f}] assumed")
    print("\n    Caveats in the module docstring are load-bearing. Read them before quoting.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
