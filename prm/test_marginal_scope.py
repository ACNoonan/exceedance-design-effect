"""SW-02 §3.5 / §6.1 — does the informative-size bias exist at all? It depends on the test marginal.

    python experiments/2026-07-26-sw02-exchangeability-audit/test_marginal_scope.py

THE DEFECT THIS SETTLES (integrity.md SW-23)
§3.5 and §6.1 asserted that the size-score coupling in the PRM artifact induces a first-order
coverage bias "larger than the design effect measured above". That assertion is not well posed
until the TEST MARGINAL is named, and neither this paper nor [park2025] named it. There are two
readings of the guarantee, and the size channel's bias is enormous under one and identically zero
under the other.

  (a) PER-PREFIX. The test unit is a fresh (question, prefix) pair drawn the way the calibration
      rows were -- pooled over prefixes, so question j carries weight m_j / n on BOTH sides.
      Calibration marginal = test marginal. The size channel contributes EXACTLY ZERO at first
      order; only §4's design effect and §3.6's drift survive.
      This is an identity, not a measurement, and is reported below as such.

  (b) PER-QUESTION. The test unit is a fresh question, weight 1/b each, while calibration still
      weights question j by m_j / n. The marginals differ whenever sizes vary, and the bias is
      first-order.

Under (b) the required likelihood ratio is w(x) proportional to 1/m_j -- a function of the
covariate alone, and OBSERVED rather than estimated, since the sizes are in the release. So
reading (b) is ordinary covariate shift and is repairable by weighted conformal prediction
([wieczorek2023]'s design-based form). That is the positive half §3.5 previously lacked.

WHAT IS MEASURED
At every achievable threshold, both marginals exactly:
    p_pool(t) = (1/n) sum over ALL ROWS       1{S <= t}          <- per-prefix
    p_perq(t) = (1/b) sum over QUESTIONS of   (within-question rate <= t)   <- per-question
The gap p_perq - p_pool is the first-order bias under reading (b), exact and assumption-free for
the released variable. It is compared against TWO baselines:
  - the Proposition 1 drift at the same level, which is the commensurable one (both are mean
    effects). §3.5 previously compared it against the DESIGN EFFECT, which is a dispersion result;
    those are not commensurable and the comparison was apples-to-oranges.
  - the coverage sd implied by n_eff, so the bias can also be read in standard deviations.

TWO CAVEATS, BOTH LOAD-BEARING

1. ORIENTATION. success_prob is treated as the score with coverage event {S <= t}, following
   `prm_measurement.py`. If [park2025]'s nonconformity score runs the other way -- high
   success_prob = conforming = low nonconformity, the natural construction -- the coverage event
   flips and so does the SIGN of every gap below. The MAGNITUDE is invariant (p -> 1-p on both
   marginals negates the gap and preserves |gap|). So this script fixes the size of the bias and
   does NOT fix its direction, which is exactly what §10 already says.

2. success_prob is the calibrated TARGET, not their nonconformity score (a residual from an
   unreleased quantile head). The reweighting gap is exact for success_prob; its magnitude for
   their score would differ. The family structure and the weights are exact regardless.

NOT A REPAIR VALIDATION. Re-weighting calibration by 1/m_j and taking the p-quantile reproduces
the per-question marginal BY CONSTRUCTION, so an in-sample "repair" is an identity that cannot
fail. It is not computed here, and would not be evidence if it were.
"""

from __future__ import annotations

import collections
import json
from pathlib import Path

import numpy as np
from scipy import stats

CACHE = Path(__file__).resolve().parent / "prm_calibration_cache.json"


def load():
    if not CACHE.exists():
        raise SystemExit(
            f"missing {CACHE.name} — run prm_measurement.py first; it downloads and caches it")
    rows = json.loads(CACHE.read_text())
    fam = collections.defaultdict(list)
    for r in rows:
        fam[r["question"]].append(float(r["success_prob"]))
    return [np.asarray(v) for v in fam.values()]


def anova_icc(fams_binary):
    """One-way random-effects ICC — the estimator `prm_measurement.py` settled on.

    Kept identical to that module rather than imported, so this script's numbers are checkable
    against §6.1's without the two files having to agree on an interface.
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


def main() -> int:
    fams = load()
    sizes = np.array([len(f) for f in fams], dtype=float)
    n, b = int(sizes.sum()), len(fams)
    m_bar = sizes.mean()
    m_til = float((sizes ** 2).sum() / sizes.sum())
    rho_s, p_s = stats.spearmanr(sizes, np.array([f.mean() for f in fams]))

    print("[0] PRECONDITION — reproduce §6.1's composition, not merely its rates")
    print(f"    rows n           = {n}          (§6.1: 25028)")
    print(f"    families b       = {b}            (§6.1: 500)")
    print(f"    m_bar / m_tilde  = {m_bar:.2f} / {m_til:.2f} (§6.1: 50.06 / 61.29)")
    print(f"    Spearman(size, family mean) = {rho_s:+.4f}, p = {p_s:.2e}"
          f"  (§6.1: -0.42, p ~ 3e-23)")
    assert n == 25028 and b == 500, "family structure does not match §6.1 — stop"

    print("\n[1] THE TWO TEST MARGINALS, AT EVERY ACHIEVABLE THRESHOLD")
    print("    p_pool = per-PREFIX (calibration's own weighting) | p_perq = per-QUESTION")
    print(f"\n{'thresh':>7} {'p_pool':>9} {'p_perq':>9} {'gap (pp)':>10}")
    pooled = np.concatenate(fams)
    rows_out = []
    for t in sorted(set(pooled))[:-1]:
        p_pool = float((pooled <= t).mean())
        p_perq = float(np.mean([(f <= t).mean() for f in fams]))
        if not (0.30 < p_pool < 0.999):
            continue
        rows_out.append((t, p_pool, p_perq))
        print(f"{t:>7.3f} {p_pool:>9.4f} {p_perq:>9.4f} {100 * (p_perq - p_pool):>+10.2f}")

    gaps = [100 * (r[2] - r[1]) for r in rows_out]
    print(f"\n    gap range across all achievable levels: "
          f"{min(gaps):+.2f} to {max(gaps):+.2f} pp — stable, not a tail artefact")

    print("\n[2] AT THE LEVEL §6.1 REPORTS (nearest achievable to 0.90)")
    t, p_pool, p_perq = min(rows_out, key=lambda r: abs(r[1] - 0.90))
    gap_pp = 100 * (p_perq - p_pool)
    print(f"    threshold t            = {t:.3f}")
    print(f"    per-prefix  (= nominal) = {p_pool:.4f}")
    print(f"    per-question            = {p_perq:.4f}")
    print(f"    FIRST-ORDER GAP         = {gap_pp:+.2f} percentage points")

    ordered = sorted(rows_out, key=lambda r: r[1])
    idx = next(i for i, r in enumerate(ordered) if r[0] == t)
    lo, hi = ordered[max(idx - 1, 0)], ordered[min(idx + 1, len(ordered) - 1)]

    def rho_at(tt):
        return anova_icc([(f <= tt).astype(float) for f in fams])

    rho_I = rho_at(t)
    rho_prime = (rho_at(hi[0]) - rho_at(lo[0])) / (hi[1] - lo[1])
    p = p_pool
    drift = (m_til - 1) / (2 * n) * (p * (1 - p) * rho_prime - (2 * p - 1) * rho_I)

    deff = 1 + (m_til - 1) * rho_I
    sd_eff = float(np.sqrt(p * (1 - p) / (n / deff)))

    print("\n[3] THE COMMENSURABLE COMPARISON (Proposition 1 drift — both are MEAN effects)")
    print(f"    rho_I({p:.3f})            = {rho_I:.4f}")
    print(f"    rho_I' (finite diff, {lo[1]:.3f}..{hi[1]:.3f}) = {rho_prime:+.3f}")
    print(f"    Prop-1 drift           = {100 * drift:+.3f} pp")
    print(f"    |gap| / |drift|        = {abs(gap_pp / (100 * drift)):.0f}x")
    print("\n    Secondary reading, against dispersion rather than mean:")
    print(f"    DEFF = {deff:.1f}, n_eff = {n / deff:.0f}, coverage sd = {100 * sd_eff:.2f} pp")
    print(f"    |gap| / sd             = {abs(gap_pp / (100 * sd_eff)):.1f} sd")

    print("\n[4] READING (a), PER-PREFIX — stated, not measured")
    print("    Calibration and test marginals coincide by construction, so the size channel")
    print("    contributes exactly 0.00 pp at first order. That is an identity and could not have")
    print("    come out otherwise; it is recorded as an argument, not as evidence.")
    print("\n[5] SIGN IS NOT FIXED BY THE RELEASE — see caveat 1 in the docstring.")
    print("    Every gap above negates under the opposite score orientation; magnitudes do not.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
