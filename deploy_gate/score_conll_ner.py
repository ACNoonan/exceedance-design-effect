#!/usr/bin/env python3
"""PASC stage-1 nonconformity on CoNLL-2003, clustered by document.

Reproduces PASC's Eq (10) with the model PASC names (`dslim/bert-base-NER`):

    s_NER = max over predicted-entity positions t of ( 1 - softmax_max(l_t) )

so the score is theirs, not ours. Grouping is the `-DOCSTART-` document boundary that ships with
CoNLL-2003 and that PASC's per-sentence hash audit cannot see.

Convention recorded: a sentence with no predicted entity has no entity positions to maximise over.
PASC sets s_NED = 0 for sentences with no entities ("trivially covered"); we apply the same
convention to s_NER and report how many sentences it affects, because it puts mass on an atom.
"""
import json
from pathlib import Path
import numpy as np, pandas as pd, torch
from transformers import AutoModelForTokenClassification, AutoTokenizer

HERE = Path(__file__).resolve().parent
D = HERE / "data" / "conll2003"
OUT = HERE / "results"; OUT.mkdir(exist_ok=True)
MODEL = "dslim/bert-base-NER"

def parse(fn):
    out, doc, cur = [], -1, []
    for line in open(D / fn, encoding="latin-1"):
        line = line.rstrip("\n")
        if line.startswith("-DOCSTART-"):
            if cur: out.append((doc, cur)); cur = []
            doc += 1; continue
        if not line.strip():
            if cur: out.append((doc, cur)); cur = []
            continue
        p = line.split()
        if len(p) >= 4: cur.append(p[0])
    if cur: out.append((doc, cur))
    return out

sents = parse("train.txt")
print(f"{len(sents)} sentences over {max(d for d,_ in sents)+1} documents")
dev = "mps" if torch.backends.mps.is_available() else "cpu"
tok = AutoTokenizer.from_pretrained(MODEL)
model = AutoModelForTokenClassification.from_pretrained(MODEL).to(dev).eval()
O_ID = model.config.label2id.get("O", 0)

rows, B = [], 32
with torch.no_grad():
    for i in range(0, len(sents), B):
        chunk = sents[i:i+B]
        enc = tok([w for _, w in chunk], is_split_into_words=True, truncation=True,
                  max_length=256, padding="max_length", return_tensors="pt")
        out = model(**{k: v.to(dev) for k, v in enc.items()}).logits.float().cpu()
        prob = torch.softmax(out, -1)
        pmax, pred = prob.max(-1)
        for j, (doc, words) in enumerate(chunk):
            wid = enc.word_ids(j)
            keep = [t for t, w in enumerate(wid) if w is not None and pred[j, t].item() != O_ID]
            s = float(max((1.0 - pmax[j, t].item()) for t in keep)) if keep else 0.0
            rows.append({"doc": doc, "n_words": len(words), "s_ner": s,
                         "has_entity": bool(keep)})
        if i % (B*100) == 0: print(f"  {i}/{len(sents)}", flush=True)

df = pd.DataFrame(rows)
df.to_parquet(OUT / "conll_ner_scores.parquet", index=False)
meta = {"model": MODEL, "n_sentences": len(df), "n_docs": int(df.doc.nunique()),
        "sentences_with_no_entity": int((~df.has_entity).sum()),
        "atom_mass_at_zero": float((df.s_ner == 0).mean()),
        "distinct_scores": int(df.s_ner.nunique())}
(OUT / "conll_ner_scoring.json").write_text(json.dumps(meta, indent=2))
print(json.dumps(meta, indent=2))
