"""§5.3 — CoNLL-2003 under PASC's specified score, per operating level, three ways.

    python analysis/conll/conll_levels.py [--scores PATH] [--reps 4000]

WHY THIS EXISTS (opened 2026-09-25)
v8 §3 reported "a factor of three" between sentence and document sampling at n = 1,000 using
rho_I at p = 0.5, the largest value. PASC operates at 80, 90 and 95% coverage, where rho_I is
smaller. This script reports each level separately, and measures the effective size directly
rather than only plugging an ICC into Proposition 2.

INPUT
`conll_ner_scores.parquet` from the lane `2026-07-29-uq-deploy-gate-clustering`: PASC's Eq (10)
s_NER from dslim/bert-base-NER (revision d1a3e8f1) on the 14,041 CoNLL-2003 training sentences,
with the -DOCSTART- document id. The 25 Sept 2026 rerun from a fresh dataset and model download
reproduced it bit for bit (audit/v9/conll-rerun/PROGRESS.md). Its SHA-256 is checked below.

THREE ESTIMATES PER LEVEL
  (a) ANOVA plug-in: the lane's one-way ICC of the indicator, D = 1 + (m_tilde - 1) rho_I.
  (b) Count estimator: Section 6.1's cluster-count variance, in the unequal-size form that
      B.5's covariance sum gives. At the fitted cutoff, X_j counts document j's rows at or below
      it, and
          v_hat = b/(b-1) * sum_j (X_j - m_j p_hat)^2 / n,    D_hat = v_hat / (p_hat (1 - p_hat)).
      With equal sizes this is exactly Section 6.1's estimator. B.10 proves consistency only for
      equal sizes; here it is a descriptive estimate under Proposition 2's conditions.
  (c) Direct measurement at PASC's calibration size. Draw about 1,000 rows either as sentences
      or as whole documents (with replacement, treating the pool as the population), fit the
      split-conformal cutoff at rank ceil((n+1)p), and evaluate coverage against the full pool's
      sentence-weighted ECDF. The measured effective size is p(1-p) / Var(coverage).

CHECKS THAT COULD HAVE FAILED
  - A permutation null (document labels shuffled, sizes kept) for (b). If the count estimator
    picked up the score distribution rather than document membership, it would clear the null
    after shuffling too.
  - The sentence arm of (c) must give an effective size of about n. With the pool as the
    population, sentences drawn with replacement are independent, whatever their documents, so
    a harness error in the cutoff, rank rule or ECDF evaluation would show up there first.
    (A first version of this script gave that arm a clustered plug-in using the draw's m_tilde
    of about 2.9. That model was wrong for this design; the measured value, about n, showed it.)
  - The document arm of (c) is compared with both pool estimates. Where (a) and (b) disagree,
    the direct measurement decides between them.
  - Ties at the fitted cutoff are counted and reported; B.1 puts atoms outside Theorem 1.
  - Size informativeness (Proposition 2's R2) is checked by Spearman between document size and
    the document's indicator rate. A null association does not establish R2 (Section 6.1).
"""
import argparse, hashlib, json, math, sys
from pathlib import Path
import numpy as np, pandas as pd
from scipy.stats import spearmanr

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
# `external/_icc.py` in the repository; `_icc.py` at the root of the code archive.
sys.path[:0] = [str(ROOT / "external"), str(ROOT)]
from _icc import rho_indicator  # noqa: E402

DEFAULT_SCORES = (Path.home() / "Documents/calibrated-uncertainty/experiments"
                  / "2026-07-29-uq-deploy-gate-clustering/results/conll_ner_scores.parquet")
SCORES_SHA256 = "d15499e815ed59efee4d627b86962a7bab3a03e957654c704355af88f04597e1"
LEVELS = (0.50, 0.80, 0.90, 0.95)
N_CAL = 1000
SEED = 20260925


def rank_cutoff(sorted_s, p):
    n = len(sorted_s); k = math.ceil((n + 1) * p)
    return math.inf if k > n else float(sorted_s[k - 1])


def count_design_effect(s, doc_codes, sizes, p):
    """Unequal-size cluster-count estimate at the pool's own fitted cutoff."""
    n, b = len(s), len(sizes)
    q = rank_cutoff(np.sort(s), p)
    ind = (s <= q).astype(float)
    X = np.bincount(doc_codes, weights=ind, minlength=b)
    p_hat = X.sum() / n
    v_hat = b / (b - 1) * ((X - sizes * p_hat) ** 2).sum() / n
    return q, p_hat, v_hat / (p_hat * (1 - p_hat)), X


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--scores", type=Path, default=DEFAULT_SCORES)
    ap.add_argument("--reps", type=int, default=4000)
    ap.add_argument("--perms", type=int, default=500)
    a = ap.parse_args()

    digest = hashlib.sha256(a.scores.read_bytes()).hexdigest()
    assert digest == SCORES_SHA256, f"score file hash {digest} is not the verified one"
    df = pd.read_parquet(a.scores)
    s = df.s_ner.to_numpy(float)
    doc_codes = pd.factorize(df.doc)[0]
    sizes = np.bincount(doc_codes).astype(float)
    n, b = len(s), len(sizes)
    m_tilde = (sizes ** 2).sum() / n
    rng = np.random.default_rng(SEED)
    out = {"n": n, "b": b, "m_bar": n / b, "m_tilde": m_tilde,
           "size_min_median_max": [int(sizes.min()), float(np.median(sizes)), int(sizes.max())],
           "atom_mass_at_zero": float((s == 0).mean()), "scores_sha256": digest, "levels": {}}
    print(f"n={n}  documents b={b}  mean size {n/b:.2f}  size-biased m_tilde {m_tilde:.2f}  "
          f"sizes {int(sizes.min())}/{np.median(sizes):.0f}/{int(sizes.max())}  "
          f"atom at 0: {(s == 0).mean():.4f}")

    # Pool-level estimates (a) and (b), with the permutation null and assumption checks.
    print("\nFULL POOL")
    for p in LEVELS:
        q, p_hat, D_hat, X = count_design_effect(s, doc_codes, sizes, p)
        rho_count = (D_hat - 1) / (m_tilde - 1)
        rho_anova = rho_indicator(s, doc_codes, p=p).rho
        null = []
        for _ in range(a.perms):
            null.append(count_design_effect(s, rng.permutation(doc_codes), sizes, p)[2])
        null_rho95 = (float(np.quantile(null, 0.95)) - 1) / (m_tilde - 1)
        ties = int((s == q).sum())
        sp = spearmanr(sizes, X / sizes)
        out["levels"][p] = {
            "cutoff": q, "cutoff_above_atom": bool(q > 0), "rows_tied_at_cutoff": ties,
            "p_hat": p_hat, "rho_anova": rho_anova, "D_anova": 1 + (m_tilde - 1) * rho_anova,
            "rho_count": rho_count, "D_count": D_hat, "null_rho_count_p95": null_rho95,
            "clearance": rho_count / null_rho95 if null_rho95 > 0 else None,
            "spearman_size_rate": float(sp.statistic), "spearman_p": float(sp.pvalue)}
        L = out["levels"][p]
        print(f"  p={p:.2f} cutoff={q:.4g} ties={ties}  rho ANOVA {rho_anova:.4f} (D {L['D_anova']:.2f})"
              f"  count {rho_count:.4f} (D {D_hat:.2f})  null95 {null_rho95:+.4f}"
              f"  Spearman(size, rate) {sp.statistic:+.3f} (p={sp.pvalue:.2g})")

    # (c) Direct measurement at PASC's calibration size.
    print(f"\nDIRECT: n about {N_CAL}, {a.reps} draws per design, coverage against the pool ECDF")
    pool_sorted = np.sort(s)
    doc_rows = [np.flatnonzero(doc_codes == j) for j in range(b)]
    cov = {"sentence": {p: [] for p in LEVELS}, "document": {p: [] for p in LEVELS}}
    mt = {"sentence": [], "document": []}
    ns = {"sentence": [], "document": []}
    for _ in range(a.reps):
        pick = rng.integers(0, n, N_CAL)
        docs = []; tot = 0
        while True:
            j = int(rng.integers(0, b))
            if tot + sizes[j] > N_CAL:
                break
            docs.append(j); tot += int(sizes[j])
        rows = np.concatenate([doc_rows[j] for j in docs])
        for name, r in (("sentence", pick), ("document", rows)):
            c = np.bincount(doc_codes[r]); c = c[c > 0].astype(float)
            mt[name].append((c ** 2).sum() / c.sum()); ns[name].append(len(r))
            ss = np.sort(s[r])
            for p in LEVELS:
                qc = rank_cutoff(ss, p)
                cov[name][p].append(1.0 if qc == math.inf
                                    else np.searchsorted(pool_sorted, qc, side="right") / n)
    out["direct"] = {"n_cal_target": N_CAL, "reps": a.reps, "seed": SEED, "designs": {}}
    for name in ("sentence", "document"):
        m_draw, n_draw = float(np.mean(mt[name])), float(np.mean(ns[name]))
        rec = {"mean_n": n_draw, "mean_m_tilde": m_draw, "levels": {}}
        for p in LEVELS:
            x = np.asarray(cov[name][p]); var = x.var(ddof=1)
            # Chi-square interval on the variance, so on the measured effective size.
            se_rel = math.sqrt(2 / (a.reps - 1))
            ne = p * (1 - p) / var
            L = out["levels"][p]
            iid = name == "sentence"  # independent draws from the pool
            rec["levels"][p] = {"mean_coverage": float(x.mean()), "sd": float(math.sqrt(var)),
                                "n_eff_measured": ne,
                                "n_eff_band_95": [ne / (1 + 1.96 * se_rel), ne / (1 - 1.96 * se_rel)],
                                "n_eff_plugin_count": n_draw if iid else n_draw / (1 + (m_draw - 1) * L["rho_count"]),
                                "n_eff_plugin_anova": n_draw if iid else n_draw / (1 + (m_draw - 1) * L["rho_anova"])}
        out["direct"]["designs"][name] = rec
    print(f"  {'level':>5} | {'sentences':>9} | {'documents':>9} {'95% band':>13} | {'count plug-in':>13} | {'ANOVA plug-in':>13} | ratio")
    for p in LEVELS:
        S = out["direct"]["designs"]["sentence"]["levels"][p]
        D = out["direct"]["designs"]["document"]["levels"][p]
        lo, hi = D["n_eff_band_95"]
        print(f"  {p:5.2f} | {S['n_eff_measured']:9.0f} | {D['n_eff_measured']:9.0f} [{lo:4.0f}, {hi:4.0f}]"
              f" | {D['n_eff_plugin_count']:13.0f} | {D['n_eff_plugin_anova']:13.0f}"
              f" | {S['n_eff_measured'] / D['n_eff_measured']:.2f}x")
    for name in ("sentence", "document"):
        r = out["direct"]["designs"][name]
        print(f"  {name}: mean n {r['mean_n']:.1f}, mean m_tilde of draw {r['mean_m_tilde']:.2f}")

    dst = HERE / "conll_levels_RESULTS.json"
    dst.write_text(json.dumps(out, indent=2, default=float))
    print(f"\nwrote {dst.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
