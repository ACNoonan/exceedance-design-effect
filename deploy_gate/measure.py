#!/usr/bin/env python3
"""`deploygate/D-01` stage 2 — the design effect on a deploy-side abstention gate.

Consumes `results/d01_scores.parquet` from `score_squad2.py`. Runs every gate in PREREG.md §4 before
reporting any headline, and writes `results/d01_measure.json`.

Deliberately separate from scoring so that a scoring bug cannot be laundered through the estimator.
Estimator is `experiments/_icc.py` — the shared spec-pinned form — never a local re-implementation.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.metrics import roc_auc_score

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))          # experiments/ on the path for _icc
from _icc import deff, icc_oneway, n_eff, rho_indicator   # noqa: E402

sys.path.insert(0, str(HERE))
from _fastnull import assert_matches_spec        # noqa: E402

OUT = HERE / "results"
RNG = np.random.default_rng(20260730)
N_PERM = 1000
N_BOOT = 2000

# The registered sweep. The train split adds two deeper levels because it is the FIRST substrate in
# the program with the cluster count to support them: b = 19,029 paragraphs against `empcore`'s
# P5b budget of b* ~ 4,000 for separating a tail floor from a decay. This is an extension of the
# pre-registered sweep, not a replacement — the six registered levels are unchanged and reported.
LEVELS = (0.50, 0.70, 0.80, 0.90, 0.95, 0.99)
LEVELS_TAIL = (0.995, 0.999)

# Geometry written down BEFORE each model run — dev from PREREG.md §1, train from
# `experiments/SUBSTRATE-QUEUE.md`, which computed it by an independent code path
# (`substrate_triage.py`) from the grouping column alone. G-04 asserts against these, so a
# disagreement means the scored frame lost rows, not that the substrate changed.
EXPECTED_BY_SPLIT = {
    "dev": {
        "article":   {"b": 35,   "n": 11873, "m_bar": 339.23, "m_tilde": 364.03},
        "paragraph": {"b": 1204, "n": 11873, "m_bar": 9.86,   "m_tilde": 10.41},
    },
    "train": {
        "article":   {"b": 442,   "n": 130319, "m_bar": 294.839, "m_tilde": 334.681},
        "paragraph": {"b": 19029, "n": 130319, "m_bar": 6.848,   "m_tilde": 8.244},
    },
}


def indicator(scores: np.ndarray, p: float) -> tuple[np.ndarray, float]:
    """1{retain} at the pooled p-quantile of the *retain* score.

    The gate abstains on high `null_odds`, so the retained (answered) set is the low tail. The
    indicator is 1{null_odds <= t_p} and its mean is p by construction — asserted by G-05.
    """
    t = float(np.quantile(scores, p))
    return (scores <= t).astype(float), t


def rho_at(scores: np.ndarray, groups: np.ndarray, p: float) -> tuple[float, float, float]:
    res = rho_indicator(scores, groups, p=p)
    return res.rho, res.m_tilde, res.n


def perm_null(ind: np.ndarray, groups: np.ndarray, n_perm: int = N_PERM) -> dict:
    """Reassign membership at the identical size profile, holding the marginal fixed.

    Routed through `_fastnull`, which is asserted against `_icc.py::icc_oneway` on this exact input
    before a single permutation is drawn — so the null and the measurement cannot come from
    silently different estimators.
    """
    ind = np.asarray(ind, dtype=float)
    codes = pd.factorize(groups)[0]
    spec = icc_oneway(ind, codes).rho
    f = assert_matches_spec(ind, codes, spec)
    return f.null(ind, n_perm, RNG)


def cluster_bootstrap_sd(scores: np.ndarray, groups: np.ndarray, p: float, n_boot: int) -> dict:
    """Dispersion of the realised retained fraction under cluster vs row resampling.

    The threshold is fixed on the FULL pool and each resample's realised retained fraction is
    measured against it, so the quantity is coverage dispersion, not threshold noise.
    """
    _, t = indicator(scores, p)
    ind = (scores <= t).astype(float)
    uniq, inv = np.unique(groups, return_inverse=True)
    b = len(uniq)
    # Per-cluster sums and sizes rather than the arrays themselves: the mean of a concatenation is
    # (sum of sums)/(sum of sizes), identically. The list-of-arrays version was 19,029 concatenations
    # per replicate at the train split — hours. This is two gathers.
    csum = np.bincount(inv, weights=ind, minlength=b)
    csize = np.bincount(inv, minlength=b).astype(float)

    clust = np.empty(n_boot)
    for i in range(n_boot):
        pick = RNG.integers(0, b, b)
        clust[i] = csum[pick].sum() / csize[pick].sum()
    iid = np.empty(n_boot)
    n = len(ind)
    for i in range(n_boot):
        iid[i] = ind[RNG.integers(0, n, n)].mean()
    sd_c, sd_i = float(clust.std(ddof=1)), float(iid.std(ddof=1))
    return {
        "sd_cluster_pp": sd_c * 100,
        "sd_iid_pp": sd_i * 100,
        "ratio": sd_c / sd_i if sd_i else float("nan"),
        "implied_deff": (sd_c / sd_i) ** 2 if sd_i else float("nan"),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--split", default="dev", choices=("dev", "train"))
    args = ap.parse_args()
    tag = "d01" if args.split == "dev" else "d01train"
    levels = LEVELS + (LEVELS_TAIL if args.split == "train" else ())
    EXPECTED = EXPECTED_BY_SPLIT[args.split]

    sc = pd.read_parquet(OUT / f"{tag}_scores.parquet")

    # Grouping comes from the SOURCE frame, joined on the question id, not from the scorer's
    # `context_hash` column. Python's `hash()` of a str is salted per process, so a hash written by
    # one scoring run is not reproducible by the next — fine as a within-run grouping, useless as a
    # published artifact. Joining also gives a composition check the scorer cannot fake.
    src = pd.read_parquet(HERE / "data" / f"squad2_{args.split}.parquet")[["id", "title", "context"]]
    n_before = len(sc)
    sc = sc.drop(columns=["title", "context_hash"]).merge(src, on="id", how="inner", validate="1:1")
    assert len(sc) == n_before, f"merge lost rows: {len(sc)} != {n_before}"
    sc["paragraph"] = pd.factorize(sc.context)[0]

    scores = sc.null_odds.to_numpy(float)
    report: dict = {"split": args.split, "n_questions": int(len(sc)),
                    "merge_preserved_rows": True, "levels": list(levels)}

    # ---------------------------------------------------------------- G-01 instrument is alive
    auroc = float(roc_auc_score(sc.impossible.to_numpy(), scores))
    report["G-01_auroc"] = auroc
    report["G-01_pass"] = bool(auroc >= 0.75)
    print(f"G-01 instrument: AUROC(null_odds vs is_impossible) = {auroc:.4f} "
          f"-> {'PASS' if auroc >= 0.75 else 'FAIL'}")
    if auroc < 0.75:
        print("  G-01 FAILED. Every rho below would be measuring noise; stopping before any headline.")
        (OUT / f"{tag}_measure.json").write_text(json.dumps(report, indent=2))
        return

    # ---------------------------------------------------------------- G-02 (A2)
    distinct = int(pd.Series(scores).nunique())
    modal = float(pd.Series(scores).value_counts().iloc[0] / len(scores))
    report["G-02"] = {"distinct": distinct, "frac_distinct": distinct / len(scores),
                      "modal_mass": modal, "pass": bool(distinct / len(scores) >= 0.95 and modal < 0.01)}
    print(f"G-02 (A2): {distinct}/{len(scores)} distinct ({distinct/len(scores):.4f}), "
          f"modal mass {modal:.5f} -> {'PASS' if report['G-02']['pass'] else 'FAIL'}")

    levels_def = {"article": sc.title.to_numpy(), "paragraph": sc.paragraph.to_numpy()}

    # ---------------------------------------------------------------- G-04 composition
    report["G-04"] = {}
    for name, groups in levels_def.items():
        sz = pd.Series(groups).value_counts().to_numpy(float)
        got = {"b": int(len(sz)), "n": int(sz.sum()),
               "m_bar": float(sz.mean()), "m_tilde": float((sz**2).sum() / sz.sum())}
        exp = EXPECTED[name]
        ok = (got["b"] == exp["b"] and got["n"] == exp["n"]
              and abs(got["m_bar"] - exp["m_bar"]) < 0.02
              and abs(got["m_tilde"] - exp["m_tilde"]) < 0.02)
        report["G-04"][name] = {"expected": exp, "got": got, "pass": bool(ok)}
        print(f"G-04 {name}: b={got['b']} n={got['n']} m_bar={got['m_bar']:.2f} "
              f"m_tilde={got['m_tilde']:.2f} -> {'PASS' if ok else 'FAIL'}")

    # ---------------------------------------------------------------- G-06 positive control
    # Perfectly concordant within article: every member of a cluster on the same side.
    uniq_a = pd.unique(sc.title)
    half = set(uniq_a[: len(uniq_a) // 2])
    synth = np.array([0.0 if t in half else 1.0 for t in sc.title])
    pc = icc_oneway(synth, sc.title.to_numpy())
    report["G-06"] = {"rho": pc.rho, "m_tilde": pc.m_tilde, "deff": pc.deff(),
                      "pass": bool(pc.rho > 0.99)}
    print(f"G-06 positive control: rho={pc.rho:.6f} (want ~1), DEFF={pc.deff():.1f} "
          f"(m_tilde={pc.m_tilde:.1f}) -> {'PASS' if pc.rho > 0.99 else 'FAIL'}")

    # ---------------------------------------------------------------- score ICC vs indicator ICC
    report["score_icc"] = {n: icc_oneway(scores, g).rho for n, g in levels_def.items()}
    print(f"raw-score ICC: article {report['score_icc']['article']:.4f}  "
          f"paragraph {report['score_icc']['paragraph']:.4f}")

    # ---------------------------------------------------------------- the sweep
    report["sweep"] = {}
    for name, groups in levels_def.items():
        rows = []
        for p in levels:
            ind, t = indicator(scores, p)
            res = rho_indicator(scores, groups, p=p)
            null = perm_null(ind, groups)
            row = {
                "p": p, "threshold": t,
                "retained_frac": float(ind.mean()),
                "G-05_pass": bool(abs(ind.mean() - p) < 0.01),
                "rho_I": res.rho, "m_tilde": res.m_tilde,
                "deff": res.deff(), "n_eff": res.n_eff(),
                "null_mean": null["mean"], "null_p95": null["p95"],
                "clears_null": bool(res.rho > null["p95"]),
                "G-03_pass": bool(null["p95"] < 0.5 * res.rho) if res.rho > 0 else False,
            }
            rows.append(row)
            print(f"  {name:9s} p={p:<5.3f} rho_I={res.rho:+.4f}  DEFF={res.deff():7.2f}  "
                  f"n_eff={res.n_eff():8.1f}  null_p95={null['p95']:+.4f}  "
                  f"{'clears' if row['clears_null'] else 'INSIDE NULL'}")
        report["sweep"][name] = rows

    # ---------------------------------------------------------------- cluster bootstrap (paragraph only)
    report["bootstrap_paragraph"] = {}
    for p in (0.80, 0.90):
        bs = cluster_bootstrap_sd(scores, sc.paragraph.to_numpy(), p, N_BOOT)
        report["bootstrap_paragraph"][str(p)] = bs
        print(f"bootstrap paragraph p={p}: sd_cluster={bs['sd_cluster_pp']:.3f}pp "
              f"sd_iid={bs['sd_iid_pp']:.3f}pp ratio={bs['ratio']:.3f} "
              f"implied DEFF={bs['implied_deff']:.2f}")

    # ---------------------------------------------------------------- T-06 answerability control
    # Residualise the exceedance indicator on the answerability label, then re-estimate.
    report["T-06_answerability_control"] = {}
    for name, groups in levels_def.items():
        rows = []
        for p in (0.80, 0.90):
            ind, _ = indicator(scores, p)
            resid = ind.copy()
            for flag in (True, False):
                m = sc.impossible.to_numpy() == flag
                resid[m] = ind[m] - ind[m].mean()
            raw = rho_indicator(scores, groups, p=p).rho
            ctl = icc_oneway(resid, groups).rho
            null = perm_null(resid, groups, n_perm=400)
            rows.append({"p": p, "rho_raw": raw, "rho_controlled": ctl,
                         "retained_frac_of_raw": ctl / raw if raw else float("nan"),
                         "null_p95": null["p95"],
                         "survives": bool(ctl > null["p95"])})
            print(f"T-06 {name:9s} p={p:<5.3f}: rho {raw:+.4f} -> {ctl:+.4f} "
                  f"({ctl/raw*100 if raw else float('nan'):.0f}% retained), "
                  f"null_p95={null['p95']:+.4f} -> {'SURVIVES' if ctl > null['p95'] else 'ABSORBED'}")
        report["T-06_answerability_control"][name] = rows

    # per-article unanswerable and abstain rates, for the interpretation
    g = sc.groupby("title").agg(n=("id", "size"), unanswerable=("impossible", "mean"))
    ind90, _ = indicator(scores, 0.90)
    sc2 = sc.assign(retain90=ind90)
    g["retain90"] = sc2.groupby("title").retain90.mean()
    report["per_article"] = g.sort_values("retain90").to_dict(orient="index")

    (OUT / f"{tag}_measure.json").write_text(json.dumps(report, indent=2, default=str))
    print(f"\nwrote {OUT / (tag + '_measure.json')}")


if __name__ == "__main__":
    main()
