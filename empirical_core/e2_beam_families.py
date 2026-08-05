"""EC-01 E2 — generate ancestry-sharing families and measure rho_I against decode config.

    python e2_beam_families.py --arm beam --width 4 --n-questions 20 --out fam_smoke.json
    python e2_beam_families.py --sweep --n-questions 1000 --out sweep.json

WHAT THIS MEASURES, AND WHY THE ARMS ARE WHAT THEY ARE
SW-02 says calibration units that share a generative ancestor carry less information than their
count suggests, by DEFF = 1 + (m_tilde - 1) * rho_I(p). Every number in the paper is either derived
or measured on ONE released artifact whose decode configuration we did not choose. Here we choose
it, so the design effect becomes a function of a knob rather than a single observation.

TWO ARMS, and the contrast is the experiment:

  beam(w)    beam search, width w, all w beams retained. Siblings share PREFIXES -- the pruning
             keeps a set of sequences that diverge late -- and are additionally the top-w order
             statistics of the score being calibrated.
  sample(k)  k independent temperature samples from the same prompt. Siblings share the PROMPT
             and nothing else: no shared prefix, no joint selection.

sample(k) is the ancestry control. If rho_I is large under beam(w) and small under sample(k) at
matched k = w, the dependence is coming from shared PREFIXES, which is the mechanism §3 names --
not merely from conditioning on a common question. If both are large, prompt-conditioning alone
suffices and the paper's mechanism claim is broader than stated. Either way it is informative, and
neither outcome is available from the released artifact.

WHY NOT A TEMPERATURE SWEEP, WHICH IS WHAT PREREG.md ORIGINALLY ASKED FOR
`e2p_marginal_invariance.py` established that rho_I is a RANK statistic: five strictly monotone
transforms of the released score leave it bit-identical (deviation 0.000e+00), while quantising
transforms move it. So a temperature sweep cannot contaminate rho_I through the score marginal, and
the "hold the marginal fixed" arm registered in PREREG.md was unnecessary. Temperature remains
available as a secondary axis, but it is not the load-bearing contrast.

THE TRAP THIS SCRIPT MUST NOT FALL INTO
DEFF = 1 + (m_tilde - 1) * rho_I. Beam width moves m_tilde DIRECTLY and arithmetically. A DEFF that
grows with width is not evidence that dependence grew. This script therefore reports rho_I and
m_tilde as SEPARATE columns at every configuration and never reports DEFF alone.

SCORE
Length-normalised sequence log-probability, which is what beam search itself ranks by. Because
rho_I is invariant to any strictly increasing transform (verified above), the choice of monotone
rescaling is immaterial; what matters is that the score be CONTINUOUS. The script counts distinct
values and refuses to report rho_I if the score is atomic, which is the (A2) failure that made the
released PRM score's design effect invisible until ties were broken.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
import torch


def anova_icc(c: np.ndarray, m: np.ndarray) -> float:
    """One-way random-effects ICC for 0/1 data from per-family counts. Matches
    prm_measurement.anova_icc (verified to 12 decimals in p5b_cluster_budget.py P1)."""
    k, n = len(m), m.sum()
    grand = c.sum() / n
    ssb = float((m * (c / m - grand) ** 2).sum())
    ssw = float((c - c * c / m).sum())
    msb, msw = ssb / (k - 1), ssw / (n - k)
    m0 = (n - (m ** 2).sum() / n) / (k - 1)
    return float((msb - msw) / (msb + (m0 - 1) * msw))


def rho_I(families: list[np.ndarray], level: float) -> float:
    flat = np.concatenate(families)
    q = np.quantile(flat, level)
    c = np.array([float((f <= q).sum()) for f in families])
    m = np.array([float(len(f)) for f in families])
    if not (0 < c.sum() / m.sum() < 1):
        return float("nan")
    return anova_icc(c, m)


_SOURCE_USED: list[str] = []


def synthetic_questions(n: int) -> list[str]:
    """Self-contained prompts, no network. The smoke proves the PIPELINE — family
    assembly, score extraction, continuity — and none of that depends on the prompts
    being real. The scaled run uses GSM8K."""
    rng = np.random.default_rng(20260729)
    out = []
    for _ in range(n):
        a, b, c = rng.integers(11, 99, 3)
        out.append(f"A shop sold {a} items on Monday, {b} on Tuesday and {c} on "
                   f"Wednesday. How many items were sold in total?")
    return out


def load_questions(n: int, source: str = "auto") -> list[str]:
    """GSM8K if reachable, synthetic otherwise. athena runs with HF_HUB_OFFLINE=1 for
    model loads, so a dataset download is NOT a safe dependency for a gated smoke —
    and a smoke that dies on data access burns a two-strikes attempt on nothing."""
    if source == "synthetic":
        print("questions: source=synthetic (pinned)", flush=True)
        _SOURCE_USED.append("synthetic")
        return synthetic_questions(n)
    try:
        from datasets import load_dataset
        ds = load_dataset("openai/gsm8k", "main", split="train")
        print(f"questions: source=GSM8K train ({len(ds)} available)", flush=True)
        _SOURCE_USED.append("gsm8k")
        return [ds[i]["question"] for i in range(min(n, len(ds)))]
    except Exception as e:  # noqa: BLE001 — any failure falls back; the reason is printed
        if source == "gsm8k":
            raise
        print(f"questions: GSM8K unavailable ({type(e).__name__}: {e}); "
              f"falling back to synthetic", flush=True)
        _SOURCE_USED.append("synthetic-fallback")
        return synthetic_questions(n)


def _mean_pairwise_lcp(seqs):
    """Mean longest-common-prefix over generated tokens, across all sibling pairs,
    normalised by the mean generated length. This is the *divergence depth* of §3.3:
    "beam branches diverging at depth 40 are more alike than branches splitting at the
    root." One number per family, which is the right granularity because Steps 1-2 of
    Theorem 1 depend on the family only through its MEAN pairwise correlation."""
    w = len(seqs)
    if w < 2:
        return float("nan"), float("nan")
    lens = [len(x) for x in seqs]
    tot, npair = 0, 0
    for i in range(w):
        for j in range(i + 1, w):
            a, b = seqs[i], seqs[j]
            k = 0
            for x, y in zip(a, b):
                if x != y:
                    break
                k += 1
            tot += k
            npair += 1
    mean_lcp = tot / npair
    denom = sum(lens) / w
    return float(mean_lcp), float(mean_lcp / denom) if denom > 0 else float("nan")


def generate(model, tok, prompts, arm, width, max_new, temperature, device, batch=8):
    """Return one list of per-sibling scores per prompt, and per-family divergence depth."""
    fams, lcps = [], []
    for i in range(0, len(prompts), batch):
        chunk = prompts[i:i + batch]
        enc = tok([f"Question: {q}\nAnswer:" for q in chunk],
                  return_tensors="pt", padding=True, truncation=True,
                  max_length=256).to(device)
        kw = dict(max_new_tokens=max_new, num_return_sequences=width,
                  return_dict_in_generate=True, output_scores=True,
                  pad_token_id=tok.pad_token_id)
        if arm == "beam":
            kw.update(num_beams=width, do_sample=False, early_stopping=True,
                      length_penalty=1.0)
        else:
            kw.update(do_sample=True, temperature=temperature, top_p=0.95, num_beams=1)
        with torch.no_grad():
            out = model.generate(**enc, **kw)

        if arm == "beam":
            s = out.sequences_scores.detach().float().cpu().numpy()
        else:
            tr = model.compute_transition_scores(out.sequences, out.scores,
                                                 normalize_logits=True)
            tr = tr.detach().float().cpu()
            mask = torch.isfinite(tr)
            s = ((tr.masked_fill(~mask, 0).sum(-1)) /
                 mask.sum(-1).clamp(min=1)).numpy()
        gen = out.sequences[:, enc["input_ids"].shape[1]:].detach().cpu().tolist()
        eos = tok.eos_token_id
        for j in range(len(chunk)):
            fams.append(s[j * width:(j + 1) * width].astype(float))
            sibs = []
            for r in range(width):
                seq = gen[j * width + r]
                if eos is not None and eos in seq:
                    seq = seq[:seq.index(eos)]
                sibs.append(seq)
            lcps.append(_mean_pairwise_lcp(sibs))
        print(f"  {arm}(w={width}) families {len(fams)}/{len(prompts)}", flush=True)
    return fams, lcps


def summarise(fams, arm, width, levels=(0.80, 0.90, 0.95, 0.99), boot=0, rng=None):
    sizes = np.array([len(f) for f in fams], dtype=float)
    flat = np.concatenate(fams)
    m_til = float((sizes ** 2).sum() / sizes.sum())
    n_distinct = int(len(np.unique(flat)))
    atomic = n_distinct < 0.5 * len(flat)
    # Within-family score spread. Unlike rho_I this is NOT degenerate at small b, so it
    # is the only ancestry signal readable at smoke scale — and it is the check that
    # would catch the two arms silently producing the same thing (e.g. do_sample not
    # taking effect). Measured locally at b=6: beam(4) 0.104 vs sample(4) 0.567.
    within_sd = float(np.mean([f.std() for f in fams]))
    row = {"arm": arm, "width": int(width), "b": len(fams), "n": int(sizes.sum()),
           "m_bar": float(sizes.mean()), "m_tilde": m_til,
           "n_distinct": n_distinct, "atomic": bool(atomic),
           "within_family_sd": within_sd,
           "between_family_sd": float(np.std([f.mean() for f in fams]))}
    for p in levels:
        r = rho_I(fams, p) if not atomic else float("nan")
        row[f"rho_I@{p}"] = r
        row[f"DEFF@{p}"] = (1 + (m_til - 1) * r) if np.isfinite(r) else float("nan")
        # Cluster bootstrap over FAMILIES — the resampling unit must be the cluster,
        # not the row, or the interval understates by exactly the design effect being
        # measured. b=1000 gave no intervals at all, so the width trend could not be
        # separated from noise; that gap is what this closes.
        if boot and not atomic:
            bs = np.empty(boot)
            k = len(fams)
            for i in range(boot):
                idx = rng.integers(0, k, k)
                bs[i] = rho_I([fams[j] for j in idx], p)
            bs = bs[np.isfinite(bs)]
            row[f"rho_I@{p}_ci"] = [float(np.percentile(bs, 2.5)),
                                    float(np.percentile(bs, 97.5))]
    return row



def stratify_by_lcp(fams, lcps, levels, boot, rng, n_strata=2):
    """THE MIXTURE TEST.

    §5.1 names two tail shapes: Gaussian (lambda_U = 0, rho_I attenuates to zero) and exact
    duplication (rho_I = q flat at every level). Beam search measured as NEITHER — rho_I decayed
    0.647 -> 0.268 across p = 0.80 -> 0.99 with a CI excluding zero, and only 2 of 8,000 scores
    were exactly tied, so duplication cannot be the floor.

    §3.3 supplies the third shape: "the realistic structure is nested rather than exchangeable —
    beam branches diverging at depth 40 are more alike than branches splitting at the root." If
    families are a MIXTURE of late-diverging (near-comonotone) and early-diverging (near-
    independent) pairs, then lambda_U = w, the *fraction* of near-comonotone pairs, and the pooled
    rho_I(p) attenuates without reaching zero. That is exactly the observed shape.

    This splits families by divergence depth and asks whether the two halves behave differently:

      HIGH-LCP half   predicted: rho_I high and comparatively FLAT into the tail
      LOW-LCP half    predicted: rho_I attenuating toward zero, Gaussian-like

    WHAT WOULD FALSIFY THE MIXTURE. If both halves show the same rho_I(p), divergence depth is not
    what drives the floor and the mechanism is something else — prompt difficulty is already ruled
    out by the sample arm, which shares prompts, shares no prefixes, and returns rho_I ~ 0. A null
    here is therefore informative rather than a shrug.
    """
    rel = np.array([l[1] for l in lcps], dtype=float)
    ok = np.isfinite(rel)
    if ok.sum() < 20:
        return None
    idx = np.argsort(rel[ok])
    fam_ok = [f for f, o in zip(fams, ok) if o]
    cut = len(idx) // n_strata
    p25, p75 = float(np.percentile(rel[ok], 25)), float(np.percentile(rel[ok], 75))
    out = {"rel_lcp_median": float(np.median(rel[ok])),
           "rel_lcp_p25": p25, "rel_lcp_p75": p75, "strata": {}}
    # GUARD. If divergence depth does not VARY across families there are no strata to
    # compare, and printing two halves of a constant as though they were a contrast is a
    # test that cannot fail. Observed locally: synthetic prompts under gpt2 gave
    # rel-LCP = 0.667 for every family, p25 = median = p75.
    out["degenerate"] = bool(p75 - p25 < 0.01)
    if out["degenerate"]:
        out["note"] = ("divergence depth is constant across families (IQR < 0.01); the "
                       "mixture test is not identified on this data and no stratum "
                       "comparison is reported")
        return out
    for si, name in enumerate(("low", "high")):
        sel = idx[:cut] if si == 0 else idx[-cut:]
        sub = [fam_ok[i] for i in sel]
        row = {"n_families": len(sub),
               "rel_lcp_mean": float(np.mean(rel[ok][sel]))}
        for p in levels:
            r = rho_I(sub, p)
            row[f"rho_I@{p}"] = r
            if boot:
                bs = np.empty(boot)
                for i in range(boot):
                    pick = rng.integers(0, len(sub), len(sub))
                    bs[i] = rho_I([sub[j] for j in pick], p)
                bs = bs[np.isfinite(bs)]
                row[f"rho_I@{p}_ci"] = [float(np.percentile(bs, 2.5)),
                                        float(np.percentile(bs, 97.5))]
        out["strata"][name] = row
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default="Qwen/Qwen3-0.6B")
    ap.add_argument("--arm", default="beam", choices=["beam", "sample"])
    ap.add_argument("--width", type=int, default=4)
    ap.add_argument("--widths", default="2,4,8")
    ap.add_argument("--n-questions", type=int, default=20)
    ap.add_argument("--max-new", type=int, default=64)
    ap.add_argument("--temperature", type=float, default=0.8)
    ap.add_argument("--batch", type=int, default=8)
    ap.add_argument("--sweep", action="store_true")
    ap.add_argument("--questions", default="auto", choices=["auto", "gsm8k", "synthetic"])
    ap.add_argument("--dtype", default="float32", choices=["float32", "bfloat16"])
    ap.add_argument("--lcp-strata", action="store_true",
                    help="split beam families by divergence depth and test the mixture")
    ap.add_argument("--boot", type=int, default=0,
                    help="cluster-bootstrap replicates for rho_I CIs (0 = off)")
    ap.add_argument("--save-families", default="",
                    help="npz path for per-family score arrays, so anything can be recomputed")
    ap.add_argument("--out", default="e2_result.json")
    a = ap.parse_args()

    from transformers import AutoModelForCausalLM, AutoTokenizer
    device = "cuda" if torch.cuda.is_available() else (
        "mps" if torch.backends.mps.is_available() else "cpu")
    print(f"device={device} model={a.model}", flush=True)

    tok = AutoTokenizer.from_pretrained(a.model, padding_side="left")
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token
    # float32 by default even on GPU. This model is 0.6B so fp32 is affordable, and
    # athena is ROCm, where bf16 has already produced NaNs across every configuration
    # tried on a 7B model in this repo. rho_I is a rank statistic, so the risk here is
    # not precision loss but ORDER flips among near-tied siblings, which is exactly
    # what the measurement is made of.
    model = AutoModelForCausalLM.from_pretrained(
        a.model, torch_dtype=getattr(torch, a.dtype)).to(device)
    model.eval()

    # MPS/CUDA graph warm-up: the first forward at a shape pays compilation and must not
    # be inside anything timed. (mps-warmup-before-timing)
    with torch.no_grad():
        w = tok(["Question: warm up\nAnswer:"], return_tensors="pt").to(device)
        model.generate(**w, max_new_tokens=4, num_beams=2, num_return_sequences=2,
                       pad_token_id=tok.pad_token_id)
    print("warm-up done", flush=True)

    qs = load_questions(a.n_questions, a.questions)
    print(f"loaded {len(qs)} questions", flush=True)

    configs = ([(arm, w) for w in [int(x) for x in a.widths.split(",")]
                for arm in ("beam", "sample")] if a.sweep else [(a.arm, a.width)])

    _FAMS = {}
    rows, t0 = [], time.time()
    for arm, w in configs:
        t = time.time()
        fams, lcps = generate(model, tok, qs, arm, w, a.max_new,
                              a.temperature, device, a.batch)
        row = summarise(fams, arm, w, boot=a.boot,
                        rng=np.random.default_rng(20260729 + w))
        if a.save_families:
            _FAMS[f"{arm}_w{w}"] = fams
        row["gen_seconds"] = round(time.time() - t, 1)
        if a.lcp_strata and arm == "beam":
            st = stratify_by_lcp(fams, lcps, (0.80, 0.90, 0.95, 0.99), a.boot,
                                 np.random.default_rng(20260730 + w))
            if st:
                row["lcp"] = st
                print(f"  LCP strata w={w}: median rel-LCP {st['rel_lcp_median']:.3f} "
                      f"(IQR {st['rel_lcp_p25']:.3f}-{st['rel_lcp_p75']:.3f})", flush=True)
                if st.get("degenerate"):
                    print(f"    DEGENERATE — {st['note']}", flush=True)
                for nm in [k for k in ("low", "high") if k in st["strata"]]:
                    d = st["strata"][nm]
                    cells = "  ".join(
                        f"p={p}: {d[f'rho_I@{p}']:.3f}" +
                        (f" [{d[f'rho_I@{p}_ci'][0]:.3f},{d[f'rho_I@{p}_ci'][1]:.3f}]"
                         if f"rho_I@{p}_ci" in d else "")
                        for p in (0.80, 0.90, 0.95, 0.99))
                    print(f"    {nm:>4} (rel-LCP {d['rel_lcp_mean']:.3f}, "
                          f"b={d['n_families']}): {cells}", flush=True)
        rows.append(row)
        print(json.dumps(row), flush=True)

    print("\n" + "=" * 100)
    print(f"  {'arm':>7} {'w':>3} {'b':>5} {'n':>6} {'m_tilde':>8} "
          f"{'distinct':>9} {'within_sd':>10} {'rho@.90':>9} {'DEFF@.90':>9}")
    for r in rows:
        print(f"  {r['arm']:>7} {r['width']:>3} {r['b']:>5} {r['n']:>6} "
              f"{r['m_tilde']:>8.2f} {r['n_distinct']:>9} {r['within_family_sd']:>10.4f} "
              f"{r['rho_I@0.9']:>9.4f} {r['DEFF@0.9']:>9.2f}")
    print("=" * 100)
    print("  rho_I and m_tilde are reported SEPARATELY on purpose: DEFF = 1+(m_tilde-1)*rho_I,")
    print("  and beam width moves m_tilde arithmetically. A rising DEFF is not evidence that")
    print("  dependence rose.")

    # Preconditions — each could come out wrong.
    beam_rows = [r for r in rows if r["arm"] == "beam"]
    any_atomic = any(r["atomic"] for r in rows)
    sizes_ok = all(r["m_bar"] == r["width"] for r in rows)
    print("\nPRECONDITIONS")
    print(f"  P1  every family has exactly `width` members -> {'PASS' if sizes_ok else 'FAIL'}")
    print("      would fail if: generation returned fewer sequences than requested, which")
    print("      would silently make m_tilde wrong and every DEFF with it.")
    print(f"  P2  score is NOT atomic -> {'PASS' if not any_atomic else 'FAIL'}")
    print("      would fail if: the score collapses to few values, the (A2) failure that hid")
    print("      the design effect on the released PRM score until ties were broken.")

    # P3 — the arms must actually differ. rho_I is degenerate at small b (two arms
    # coincided to 4 decimals at b=8 locally), so agreement there is NOT evidence the
    # pipeline works; it is evidence the estimator has nothing to chew on. This check
    # reads a statistic that IS informative at small b.
    p3, p3_note = True, "only one arm present — contrast not testable"
    pairs = {}
    for r in rows:
        pairs.setdefault(r["width"], {})[r["arm"]] = r["within_family_sd"]
    both = {w: d for w, d in pairs.items() if {"beam", "sample"} <= set(d)}
    if both:
        ratios = {w: d["sample"] / d["beam"] if d["beam"] > 0 else float("inf")
                  for w, d in both.items()}
        p3 = all(v > 1.5 for v in ratios.values())
        p3_note = "  ".join(f"w={w}: sample/beam within-family sd = {v:.2f}x"
                            for w, v in sorted(ratios.items()))
    # Print N/A, not PASS, when only one arm ran. A check that could not have failed
    # must never render as a pass — that is how a vacuous check gets read as evidence.
    print(f"  P3  beam siblings are TIGHTER than independent samples -> "
          f"{('PASS' if p3 else 'FAIL') if both else 'N/A (not testable)'}")
    print(f"      {p3_note}")
    print("      would fail if: do_sample never took effect and both arms are secretly")
    print("      running beam search, which would make the whole ancestry contrast void")
    print("      while still producing plausible-looking numbers.")

    ok = sizes_ok and not any_atomic and p3
    out = {"rows": rows, "meta": {
        "model": a.model, "n_questions": len(qs), "max_new": a.max_new,
        "temperature": a.temperature, "device": device,
        "questions_source": (_SOURCE_USED or ["unknown"])[0], "dtype": a.dtype,
        "total_seconds": round(time.time() - t0, 1)},
        "preconditions": {"p1_family_sizes_exact": bool(sizes_ok),
                          "p2_score_not_atomic": bool(not any_atomic),
                          "p3_arms_differ": bool(p3)}}
    Path(a.out).write_text(json.dumps(out, indent=2))
    # metrics.json feeds the harness report card.
    Path("metrics.json").write_text(json.dumps(
        {r["arm"] + "_w" + str(r["width"]): {
            "rho_I_at_0.90": r["rho_I@0.9"], "m_tilde": r["m_tilde"],
            "DEFF_at_0.90": r["DEFF@0.9"], "b": r["b"]} for r in rows}, indent=2))
    if a.save_families and _FAMS:
        np.savez_compressed(a.save_families,
                            **{k: np.concatenate(v) for k, v in _FAMS.items()},
                            **{k + "__sizes": np.array([len(f) for f in v])
                               for k, v in _FAMS.items()})
        print(f"wrote {a.save_families} ({len(_FAMS)} configs)")
    print(f"\nwrote {a.out} and metrics.json")
    if not ok:
        print("A PRECONDITION FAILED — no rho_I above may be quoted.")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
