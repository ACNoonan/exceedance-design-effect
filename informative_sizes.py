"""SW-02 — informative cluster sizes: the assumption that actually fails hardest.

    python experiments/2026-07-26-sw02-exchangeability-audit/informative_sizes.py

Proposition 2 conditions on cluster sizes as FIXED. In every real ancestry-sharing pipeline the
sizes are determined by the same process that generates the scores, so they are informative.
This script establishes three things:

1. WHAT BREAKS. Informative sizes do not perturb the design effect. They break the common-marginal
   assumption (A1)-(A2): if larger families systematically score differently, the pooled
   calibration distribution is no longer the test distribution, and coverage acquires a
   FIRST-ORDER bias that dwarfs the O(1) dispersion inflation and the O(1/b) mean drift.

2. THE SIGN AND SIZE. With the size profile held identical and only the size/score PAIRING
   changed, coverage moves by roughly +6.5 pp when large families score high and -18 pp when
   they score low, against a design-effect contribution of well under 1 pp. Direction, not
   magnitude, is the transferable part: the coupling strength here is maximal (rank-matched) and
   real pipelines will be weaker.

3. IT IS PRESENT IN THE REAL ARTIFACT. On the released PRM calibration set the correlation
   between family size and family mean score is Spearman -0.42 (p ~ 1e-23) -- longer reasoning
   traces on harder questions. So this is a live violation in the paper's own live instance,
   not a hypothetical.

The honest limit: the direction of the coverage error in that artifact depends on how their
nonconformity score maps to success_prob, and the release does not contain the score. What the
data establish is that the coupling exists and is strong, hence that the assumption is violated
-- not which way the resulting bias points.
"""

from __future__ import annotations

import collections
import json
from pathlib import Path

import numpy as np
from scipy.stats import norm, pearsonr, spearmanr

ALPHA, B, REPS, R = 0.10, 60, 20_000, 0.6
SIZES = np.array([1] * 20 + [2] * 15 + [4] * 12 + [8] * 8 + [16] * 5)
CACHE = Path(__file__).resolve().parent / "prm_calibration_cache.json"


def simulate(mode: str, seed: int = 0) -> np.ndarray:
    """Coverage per replication. Size PROFILE is identical across modes; only pairing differs."""
    rng = np.random.default_rng(seed)
    cov = np.empty(REPS)
    for t in range(REPS):
        anc = rng.normal(size=B)
        if mode == "independent":
            sizes = rng.permutation(SIZES)
        elif mode == "big=high":
            sizes = np.sort(SIZES)[np.argsort(np.argsort(anc))]
        elif mode == "big=low":
            sizes = np.sort(SIZES)[np.argsort(np.argsort(-anc))]
        else:
            raise ValueError(mode)
        fams = [np.sqrt(R) * a + np.sqrt(1 - R) * rng.normal(size=int(m))
                for a, m in zip(anc, sizes)]
        alls = np.concatenate(fams)
        k = int(np.ceil((alls.size + 1) * (1 - ALPHA)))
        cov[t] = float(norm.cdf(np.sort(alls)[k - 1]))
    return cov


def part_1() -> None:
    n = int(SIZES.sum())
    nominal = int(np.ceil((n + 1) * (1 - ALPHA))) / (n + 1)
    print(f"\n[1] SIMULATION — same size profile, different size/score pairing")
    print(f"    n={n}, b={B}, within-family score correlation r={R}, nominal={nominal:.4f}\n")
    print(f"{'size-score coupling':>22} {'mean cov':>9} {'shift (pp)':>11} {'sd':>8} {'verdict':>10}")
    for mode, label in (("independent", "independent"),
                        ("big=high", "large fams score HIGH"),
                        ("big=low", "large fams score LOW")):
        c = simulate(mode)
        shift = 100 * (c.mean() - nominal)
        verdict = "ok" if abs(shift) < 1 else ("conservative" if shift > 0 else "UNSAFE")
        print(f"{label:>22} {c.mean():>9.4f} {shift:>+11.2f} {c.std(ddof=1):>8.4f} "
              f"{verdict:>10}")
    print("\n    For comparison, the entire design effect at this configuration moves the MEAN")
    print("    by under 1 pp. The marginal violation is first-order; the design effect is not.")


def part_2() -> None:
    if not CACHE.exists():
        print("\n[2] SKIPPED — run prm_measurement.py first to fetch the dataset cache.")
        return
    rows = json.loads(CACHE.read_text())
    fam = collections.defaultdict(list)
    for r in rows:
        fam[r["question"]].append(float(r["success_prob"]))
    sizes = np.array([len(v) for v in fam.values()], dtype=float)
    means = np.array([np.mean(v) for v in fam.values()])
    rs, ps = spearmanr(sizes, means)
    rp, pp = pearsonr(sizes, means)
    print(f"\n[2] IS THE COUPLING PRESENT IN THE REAL PRM CALIBRATION SET?")
    print(f"    families = {len(sizes)}")
    print(f"    Spearman(size, family mean score) = {rs:+.4f}   p = {ps:.2e}")
    print(f"    Pearson (size, family mean score) = {rp:+.4f}   p = {pp:.2e}")
    q = np.quantile(sizes, [0, .25, .5, .75, 1.0])
    print(f"\n{'size quartile':>16} {'families':>9} {'mean size':>10} {'mean score':>11}")
    for i in range(4):
        sel = (sizes >= q[i]) & (sizes <= q[i + 1]) if i == 3 else \
              (sizes >= q[i]) & (sizes < q[i + 1])
        print(f"{'Q' + str(i + 1):>16} {int(sel.sum()):>9} {sizes[sel].mean():>10.1f} "
              f"{means[sel].mean():>11.4f}")
    print("\n    Strong and highly significant: larger families score systematically lower")
    print("    (harder questions -> longer traces -> more prefixes). Assumption (A1)-(A2) is")
    print("    violated in the released data. Direction of the induced coverage error is NOT")
    print("    determined here -- their nonconformity score is not in the release.")


def main() -> int:
    part_1()
    part_2()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
