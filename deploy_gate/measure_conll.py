#!/usr/bin/env python3
"""Turn PASC's DEFF *ceiling* into a measured DEFF, on their own score and their own corpus.

Ceiling = m_tilde, exact from the grouping. This measures rho_I of the exceedance indicator of
PASC's Eq (10) s_NER, clustered by the -DOCSTART- document, and reports the design effect a
document-blocked calibration set of their size would actually carry.
"""
import json, sys
from pathlib import Path
import numpy as np, pandas as pd
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent)); sys.path.insert(0, str(HERE))
from _icc import rho_indicator, icc_oneway, deff, n_eff
from _fastnull import assert_matches_spec

OUT = HERE / "results"
RNG = np.random.default_rng(20260730)
df = pd.read_parquet(OUT / "conll_ner_scores.parquet")
s, doc = df.s_ner.to_numpy(float), df.doc.to_numpy()
rep = {"n": len(df), "b": int(df.doc.nunique()),
       "atom_mass_at_zero": float((s == 0).mean()), "distinct": int(pd.Series(s).nunique())}
print(f"n={len(df)} docs={df.doc.nunique()} atom mass at 0: {(s==0).mean():.4f} "
      f"distinct {pd.Series(s).nunique()}")

def null(ind, g, k=1000):
    codes = pd.factorize(g)[0]
    return assert_matches_spec(ind, codes, icc_oneway(ind, codes).rho).null(ind, k, RNG)

print("\nFULL POOL, clustered by document:")
rows = []
for p in (0.50, 0.70, 0.80, 0.90, 0.95):
    t = float(np.quantile(s, p)); ind = (s <= t).astype(float)
    realised = float(ind.mean())
    if not (1e-9 < realised < 1 - 1e-9):
        rows.append({"p": p, "reachable": False}); print(f"  p={p}: UNREACHABLE (atom)"); continue
    r = rho_indicator(s, doc, p=p); nl = null(ind, doc)
    rows.append({"p": p, "reachable": True, "realised": realised, "rho_I": r.rho,
                 "m_tilde": r.m_tilde, "deff": r.deff(), "n_eff": r.n_eff(),
                 "null_p95": nl["p95"], "clears": bool(r.rho > nl["p95"])})
    print(f"  p={p:.2f} realised={realised:.3f} rho_I={r.rho:+.4f} m_tilde={r.m_tilde:.2f} "
          f"DEFF={r.deff():.2f} n_eff={r.n_eff():.0f} null={nl['p95']:+.4f} "
          f"{'clears' if r.rho>nl['p95'] else 'INSIDE NULL'}")
rep["full_pool"] = rows

# What a calibration set of PASC's size actually carries, under each sampling design
best = max((r for r in rows if r.get("reachable")), key=lambda r: r["rho_I"])
rho_hat = best["rho_I"]
print(f"\nUsing rho_I = {rho_hat:.4f} (at p={best['p']}), the DEFF a PASC-sized calibration set carries:")
sizes = {}
for n_cal in (200, 500, 1000):
    mts_a, mts_b = [], []
    for _ in range(200):
        pick = RNG.choice(len(s), n_cal, replace=False)
        sz = np.bincount(doc[pick]); sz = sz[sz > 0].astype(float)
        mts_a.append((sz**2).sum()/sz.sum())
    uniq = np.unique(doc)
    for _ in range(50):
        order = RNG.permutation(uniq); keep, tot = [], 0
        for d in order:
            k = int((doc == d).sum())
            if tot + k > n_cal: break
            keep.append(d); tot += k
        sz = np.bincount(doc[np.isin(doc, keep)]); sz = sz[sz > 0].astype(float)
        mts_b.append((sz**2).sum()/sz.sum())
    a, b = float(np.mean(mts_a)), float(np.mean(mts_b))
    da, db = deff(rho_hat, a), deff(rho_hat, b)
    sizes[n_cal] = {"m_tilde_A": a, "m_tilde_B": b, "deff_A": da, "deff_B": db,
                    "n_eff_A": n_cal/da, "n_eff_B": n_cal/db}
    print(f"  n_cal={n_cal:5d}: design A DEFF={da:5.2f} (n_eff {n_cal/da:6.1f})   "
          f"design B DEFF={db:5.2f} (n_eff {n_cal/db:6.1f})   ratio {db/da:.1f}x")
rep["rho_used"] = rho_hat; rep["by_calibration_size"] = sizes
(OUT / "conll_measure.json").write_text(json.dumps(rep, indent=2, default=str))
print(f"\nwrote {OUT/'conll_measure.json'}")
