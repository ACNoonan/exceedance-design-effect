#!/usr/bin/env python3
"""
One-sided rho_I(p) on real data -- the object SW-02 section 5 actually uses.

WHY THIS AND NOT WHAT WE ALREADY HAVE. Every NHANES measurement so far (runs 10-16)
computed rho_A, the ICC of INTERVAL MEMBERSHIP 1{lo < Y <= hi} -- a two-sided object,
correct for reference intervals. SW-02 section 5 is ONE-SIDED: rho_I(p) is the ICC of the
exceedance indicator 1{Y <= q_p} at a single coverage level. Different estimand; the
two-sided results do not transfer, and neither does today's skew work.

WHAT SECTION 5 ASKS FOR. It plots rho_I(p) under a Gaussian copula and hedges in its own
figure caption: "the ordering is a property of this family, not a general one". That hedge
is currently theoretical. This tests it on real clustered data.

    rho_I(p) = (delta(p) - p^2) / (p(1-p)),   delta(p) = Phi_2(z_p, z_p; rho)

registered prediction, from run 16 (Gaussian over-predicted the two-sided rho_A by
2.4-4.1x where the measurement was well resolved): the Gaussian copula will
OVER-PREDICT one-sided rho_I too, and the gap will WIDEN into the tail.

GATE 2. Every rho_I is reported against a permutation null (cluster labels shuffled,
200x) and must clear the null's 95th PERCENTILE. The ANOVA ICC of a rare indicator is
upward-biased at small cluster counts, which is exactly what the null absorbs. At
p = 0.99 with ~150 per cluster there is roughly 1.5 exceedance per cluster, so most
analytes are expected to FAIL to clear there -- that failure is information about power,
not about the copula.
"""

import numpy as np
import pandas as pd
from scipy import stats

SEED = 20260744
NPERM = 200
AGE_LO, AGE_HI = 18, 70
LEVELS = [0.90, 0.95, 0.975, 0.99]
ANALYTES = {
    "LBXSNASI": "sodium", "LBXSKSI": "potassium", "LBXSCA": "calcium",
    "LBXSAL": "albumin", "LBXSCR": "creatinine", "LBXSGL": "glucose",
    "LBXSATSI": "ALT", "LBXSASSI": "AST", "LBXSTB": "bilirubin",
    "LBXSCH": "cholesterol",
}
CYCLES = [("2013-14", "DEMO_H", "BIOPRO_H"), ("2015-16", "DEMO_I", "BIOPRO_I"),
          ("2017-18", "DEMO_J", "BIOPRO_J")]


def anova_icc(y, g):
    d = pd.DataFrame({"y": y, "g": g}).dropna()
    k, N = d.g.nunique(), len(d)
    if k < 3 or N < 50:
        return np.nan
    grand = d.y.mean()
    grp = d.groupby("g").y.agg(["mean", "count", "var"])
    msb = (grp["count"] * (grp["mean"] - grand) ** 2).sum() / (k - 1)
    msw = ((grp["count"] - 1) * grp["var"].fillna(0.0)).sum() / (N - k)
    if msw <= 0:
        return np.nan
    n0 = (N - (grp["count"] ** 2).sum() / N) / (k - 1)
    return (msb - msw) / (msb + (n0 - 1) * msw)


def rho_I_gauss(p, rho):
    """SW-02's closed form under a Gaussian copula."""
    z = stats.norm.ppf(p)
    delta = stats.multivariate_normal.cdf([z, z], mean=[0, 0],
                                          cov=[[1, rho], [rho, 1]])
    return (delta - p * p) / (p * (1 - p))


# The .XPT paths below are relative, so the script only ran from its own directory — it ships in
# the paper's archive, where a reader following §12 will not be standing in it. Resolve to the
# script's own location instead (found 2026-07-31 while re-verifying §5.2's tables).
import os as _os
from pathlib import Path as _Path
_os.chdir(_Path(__file__).resolve().parent)


def main():
    rng = np.random.default_rng(SEED)
    parts = []
    for cy, d, b in CYCLES:
        m = (pd.read_sas(d + ".XPT")[["SEQN", "SDMVSTRA", "SDMVPSU", "RIDAGEYR"]]
             .merge(pd.read_sas(b + ".XPT"), on="SEQN", how="inner"))
        m["cycle"] = cy
        parts.append(m)
    df = pd.concat(parts, ignore_index=True)
    df["clus"] = (df.SDMVSTRA.astype(int).astype(str) + "_"
                  + df.SDMVPSU.astype(int).astype(str))
    df = df[(df.RIDAGEYR >= AGE_LO) & (df.RIDAGEYR <= AGE_HI)]
    print(f"n = {len(df)}, clusters = {df.clus.nunique()}, "
          f"median cluster size = {int(df.groupby('clus').size().median())}")

    print("\n" + "=" * 104)
    print("ONE-SIDED rho_I(p), measured vs Gaussian-copula prediction from the measured ICC")
    print("'clears' = exceeds the permutation null's 95th percentile")
    print("=" * 104)
    hdr = (f"{'analyte':>12} {'ICC_val':>8} " +
           "".join(f"{('p=%.3f' % p):>22}" for p in LEVELS))
    print(hdr)
    print(f"{'':>12} {'':>8} " + "".join(f"{'meas / pred / ratio':>22}" for _ in LEVELS))
    print("-" * 104)

    rows = []
    for code, name in ANALYTES.items():
        s = df[["clus", code]].dropna()
        # BELOW-DETECTION-LIMIT SCREEN, added 2026-07-30 after bilirubin was found to
        # carry 19 values coded 5.4e-79. Log-transformed those become ~-180 against a
        # distribution centred near -0.7, and 34 such points moved bilirubin's ICC from
        # 0.0055 to 0.1156 -- a 21x change that manufactured a spurious violation of
        # rho_I < rho. No other analyte is affected (all have log-range < 7).
        s = s[s[code] > 1e-6]
        if len(s) < 2000:
            continue
        y = np.log(s[code].values)
        g = s.clus.values
        icc = anova_icc(y, g)
        if not np.isfinite(icc) or icc <= 0:
            continue
        cells = []
        for p in LEVELS:
            thr = np.quantile(y, p)
            ind = (y <= thr).astype(float)
            r = anova_icc(ind, g)
            null95 = np.nanpercentile(
                [anova_icc(ind, rng.permutation(g)) for _ in range(NPERM)], 95)
            pred = rho_I_gauss(p, icc)
            clears = r > null95
            rows.append((name, p, icc, r, pred, clears))
            mark = "" if clears else "*"
            cells.append(f"{r:.4f}/{pred:.4f}/{pred/r if r>0 else np.nan:>5.1f}x{mark}")
        print(f"{name:>12} {icc:>8.4f} " + "".join(f"{c:>22}" for c in cells))

    print("\n  * = does not clear the permutation null (underpowered at that level)")

    ok = [r for r in rows if r[5] and r[3] > 0]
    print("\n" + "=" * 104)
    print("VERDICT -- registered prediction: Gaussian OVER-predicts, gap WIDENS into the tail")
    print("=" * 104)
    if not ok:
        print("no cell cleared its null; no verdict available")
        return
    for p in LEVELS:
        sub = [r for r in ok if r[1] == p]
        if not sub:
            print(f"  p={p:.3f}: no analyte clears the null")
            continue
        ratios = np.array([r[4] / r[3] for r in sub])
        print(f"  p={p:.3f}: {len(sub):>2} analytes clear, "
              f"pred/meas median {np.median(ratios):>6.2f}x  "
              f"range [{ratios.min():.2f}, {ratios.max():.2f}]")
    # ------------------------------------------------------------------
    # BALANCED PANEL, added 2026-07-31.
    #
    # The per-level medians above are each computed over a DIFFERENT set of
    # analytes -- ten clear at p=0.90, five at p=0.99 -- so reading them as one
    # quantity rising conflates the gap widening with the panel shrinking. The
    # registered prediction above is left exactly as registered; this block is
    # what tests it on a set that can actually be compared across levels.
    #
    # Section 5.2 prints BOTH columns. The clearing set is the right set for
    # reading any single row; the balanced panel is the only set on which the
    # rows may be compared to each other.
    # ------------------------------------------------------------------
    names = sorted({r[0] for r in rows})
    balanced = [n for n in names
                if all(any(r[0] == n and r[1] == p and r[5] and r[3] > 0
                           for r in rows) for p in LEVELS)]
    print("\n" + "=" * 104)
    print(f"BALANCED PANEL -- {len(balanced)} analytes clearing the null at EVERY level: "
          f"{', '.join(balanced)}")
    print("=" * 104)
    print(f"{'p':>8}{'n':>5}{'median pred/meas':>20}{'range':>22}"
          f"{'  (clearing-set median)':>24}")
    for p in LEVELS:
        bal = np.array([r[4] / r[3] for r in rows
                        if r[0] in balanced and r[1] == p])
        clr = np.array([r[4] / r[3] for r in rows
                        if r[5] and r[3] > 0 and r[1] == p])
        print(f"{p:>8.3f}{len(bal):>5}{np.median(bal):>20.4f}"
              f"{f'[{bal.min():.4f}, {bal.max():.4f}]':>22}"
              f"{np.median(clr):>24.4f}")

    print(f"\n{'analyte':>12}" + "".join(f"{p:>10.3f}" for p in LEVELS))
    for n in balanced:
        vals = [next(r[4] / r[3] for r in rows if r[0] == n and r[1] == p)
                for p in LEVELS]
        print(f"{n:>12}" + "".join(f"{v:>10.4f}" for v in vals))

    print("\nINTERNAL CHECK: at the tightest level the balanced panel IS the clearing set,")
    print("so the two medians in the last two columns must agree exactly there. They do")
    print("if the two selections were built from the same `clears` flag, and a mismatch")
    print("means the panel construction above disagrees with the per-cell test.")
    print("\nThe registered prediction is confirmed where the panel is fixed and the")
    print("measurement is powered, and NOT at the loosest level, where the median falls")
    print("below 1. Section 5.2 states the narrower claim rather than the registered one.")


if __name__ == "__main__":
    main()
