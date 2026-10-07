#!/usr/bin/env python3
"""`deploygate/D-01` stage 1 — score SQuAD 2.0 dev abstention with a real QA model.

Produces one `null_odds` per question: (null start+end logit) - (best non-null span logit sum).
Higher = more likely to abstain. This is the standard SQuAD 2.0 abstention statistic and the thing
a deployed abstain-gate thresholds.

MPS discipline, both from recorded findings in this program:
  * pad every batch to a FIXED length (variable padded shapes recompile the Metal graph per batch,
    measured 11x slower on local model eval)
  * one warm-up forward at the target shape before timing anything (first forward at a shape pays
    graph compilation; timing it was ~66x off and selected a wrong design)

Writes `results/d01_scores.parquet` with one row per question id, and `results/d01_scoring.json`
with the machinery outcome. No ICC is computed here — that is `measure.py`, so a scoring bug cannot
be hidden inside the estimator's output.
"""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import numpy as np
import pandas as pd
import torch
from transformers import AutoModelForQuestionAnswering, AutoTokenizer

HERE = Path(__file__).resolve().parent
DATA = HERE / "data"
OUT = HERE / "results"
OUT.mkdir(exist_ok=True)

MODEL = "deepset/roberta-base-squad2"
MAX_LEN = 384
STRIDE = 128
BATCH = 16
N_BEST = 20
MAX_ANS_LEN = 30
MAX_Q_TOKENS = 64


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--split", default="dev", choices=("dev", "train"),
                    help="dev = the 11,873-question validation set (b=35 articles); "
                         "train = 130,319 questions over 442 articles and 19,029 paragraphs, "
                         "the only tail-capable arm (b >= 4,000 at the paragraph level)")
    ap.add_argument("--limit", type=int, default=0, help="smoke test on the first N questions")
    args = ap.parse_args()
    tag = "d01" if args.split == "dev" else "d01train"
    if args.limit:
        tag += f"_smoke{args.limit}"

    df = pd.read_parquet(DATA / f"squad2_{args.split}.parquet")
    if args.limit:
        df = df.head(args.limit).copy()
    df["impossible"] = df.answers.map(lambda a: len(a["text"]) == 0)
    print(f"questions: {len(df)}  unanswerable: {int(df.impossible.sum())}")

    device = "mps" if torch.backends.mps.is_available() else "cpu"
    tok = AutoTokenizer.from_pretrained(MODEL)
    model = AutoModelForQuestionAnswering.from_pretrained(MODEL).to(device).eval()

    # Cap the QUESTION before tokenising the pair. `truncation="only_second"` raises
    # "Sequence to truncate too short to respect the provided max_length" when the question alone
    # fills max_length, and the train split contains **exactly one** such row out of 130,319: a
    # whitespace-only question of 25,603 tokens in `Antenna_(radio)`. Median question length is 12
    # tokens, so a 64-token cap touches that row and nothing else.
    #
    # Capping rather than DROPPING is deliberate: `deploygate/G-04` asserts the row count against a
    # geometry written down in advance, so silently dropping a row would either trip that gate or,
    # worse, quietly change the denominator. One corrupt question keeps its row and gets whatever
    # score the model gives whitespace.
    q_ids = tok(list(df.question), add_special_tokens=False)["input_ids"]
    n_capped = sum(1 for q in q_ids if len(q) > MAX_Q_TOKENS)
    questions = [
        tok.decode(q[:MAX_Q_TOKENS]) if len(q) > MAX_Q_TOKENS else orig
        for q, orig in zip(q_ids, df.question)
    ]
    print(f"questions capped at {MAX_Q_TOKENS} tokens: {n_capped} of {len(df)}")

    # Tokenise with overflow so long contexts are covered by several features.
    enc = tok(
        questions,
        list(df.context),
        truncation="only_second",
        max_length=MAX_LEN,
        stride=STRIDE,
        return_overflowing_tokens=True,
        # NO return_offsets_mapping: the span filter uses `sequence_ids` instead, and at the
        # train split's ~133k features materialising offsets would build ~51M Python tuples for
        # nothing.
        padding="max_length",          # FIXED shape, deliberately — see module docstring
    )
    sample_map = enc["overflow_to_sample_mapping"]
    n_feat = len(enc["input_ids"])
    print(f"features: {n_feat} for {len(df)} questions (fixed length {MAX_LEN})")

    ids = torch.tensor(enc["input_ids"])
    mask = torch.tensor(enc["attention_mask"])

    # WARM-UP at the exact production shape, excluded from timing.
    with torch.no_grad():
        model(input_ids=ids[:BATCH].to(device), attention_mask=mask[:BATCH].to(device))
    if device == "mps":
        torch.mps.synchronize()

    starts = np.empty((n_feat, MAX_LEN), dtype=np.float32)
    ends = np.empty((n_feat, MAX_LEN), dtype=np.float32)
    t0 = time.perf_counter()
    with torch.no_grad():
        for i in range(0, n_feat, BATCH):
            j = min(i + BATCH, n_feat)
            out = model(
                input_ids=ids[i:j].to(device),
                attention_mask=mask[i:j].to(device),
            )
            starts[i:j] = out.start_logits.float().cpu().numpy()
            ends[i:j] = out.end_logits.float().cpu().numpy()
            if i % (BATCH * 100) == 0:
                el = time.perf_counter() - t0
                print(f"  {j}/{n_feat}  {el:.0f}s  ({j / max(el, 1e-9):.1f} feat/s)", flush=True)
    elapsed = time.perf_counter() - t0
    print(f"forward complete in {elapsed:.0f}s ({n_feat / elapsed:.1f} feat/s)")

    # Per-question aggregation over its features.
    feats_by_sample: dict[int, list[int]] = {}
    for f, s in enumerate(sample_map):
        feats_by_sample.setdefault(int(s), []).append(f)

    # Mask to CONTEXT tokens only, per feature. This is not a nicety: with
    # padding="max_length" the tokeniser returns offsets of (0, 0) for special AND pad tokens
    # rather than None, so an `offsets is None` filter never fires and the best-span search would
    # be free to pick a question token or a pad token. That would corrupt every `null_odds`.
    ctx_mask = np.zeros((n_feat, MAX_LEN), dtype=bool)
    for f in range(n_feat):
        seq = enc.sequence_ids(f)
        ctx_mask[f] = np.array([s == 1 for s in seq], dtype=bool)
    print(f"context tokens per feature: min {ctx_mask.sum(1).min()} "
          f"med {int(np.median(ctx_mask.sum(1)))} max {ctx_mask.sum(1).max()}")
    assert ctx_mask.sum(1).min() > 0, "a feature with no context tokens: stride/truncation is wrong"

    NEG = -1e30
    s_masked = np.where(ctx_mask, starts, NEG)
    e_masked = np.where(ctx_mask, ends, NEG)

    rows = []
    for qi in range(len(df)):
        fl = feats_by_sample.get(qi, [])
        # null score: the CLS (position 0) start+end logit, minimum over features is the
        # convention in the reference SQuAD 2.0 script (a span is only unanswerable if no
        # feature supports an answer).
        null_score = min(float(starts[f][0] + ends[f][0]) for f in fl)
        best = NEG
        for f in fl:
            s_top = np.argpartition(s_masked[f], -N_BEST)[-N_BEST:]
            e_top = np.argpartition(e_masked[f], -N_BEST)[-N_BEST:]
            # outer sum over the candidate grid, then mask the geometrically invalid cells
            grid = s_masked[f][s_top, None] + e_masked[f][None, e_top]
            si = s_top[:, None]
            ei = e_top[None, :]
            valid = (ei >= si) & (ei - si + 1 <= MAX_ANS_LEN)
            if valid.any():
                best = max(best, float(grid[valid].max()))
        rows.append(
            {
                "id": df.id.iloc[qi],
                "title": df.title.iloc[qi],
                "context_hash": hash(df.context.iloc[qi]) & 0xFFFFFFFF,
                "impossible": bool(df.impossible.iloc[qi]),
                "null_score": null_score,
                "best_span": best,
                "null_odds": null_score - best,
                "n_features": len(fl),
            }
        )

    sc = pd.DataFrame(rows)
    sc.to_parquet(OUT / f"{tag}_scores.parquet", index=False)

    meta = {
        "split": args.split,
        "model": MODEL,
        "device": device,
        "n_questions": int(len(sc)),
        "n_features": int(n_feat),
        "max_len": MAX_LEN,
        "stride": STRIDE,
        "batch": BATCH,
        "padding": "max_length (fixed shape)",
        "warmup": True,
        "questions_capped": int(n_capped),
        "max_q_tokens": MAX_Q_TOKENS,
        "forward_seconds": round(elapsed, 1),
        "features_per_second": round(n_feat / elapsed, 2),
        "questions_with_no_feature": int((sc.n_features == 0).sum()),
    }
    (OUT / f"{tag}_scoring.json").write_text(json.dumps(meta, indent=2))
    print(json.dumps(meta, indent=2))


if __name__ == "__main__":
    main()
