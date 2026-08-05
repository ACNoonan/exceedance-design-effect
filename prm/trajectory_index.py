"""Recover the trajectory index the release does not carry — and close a §6.1 caveat.

    .venv/bin/python experiments/2026-07-26-sw02-exchangeability-audit/repro-park2025/trajectory_index.py

WHY THIS EXISTS
SW-02 §6.1 ends with a caveat we could not previously discharge:

    "The release carries no trajectory index, so clusters here are *questions* and
     within-trajectory correlation — presumably higher — cannot be separated; this is a
     lower bound."

It is recoverable. park2025 §3.1 Stage 2 takes "all possible prefix trajectories x_{0:t},
t in {0..T}" of each of N_val = 8 trajectories, so the prefixes of one trajectory form a NESTED
CHAIN under string-prefixing. Reconstruct the chains and the trajectory index falls out.

    maximal chain := a prefix that is not a proper string-prefix of any other prefix of the
                     same question. There are 3,961 of them against 500 x 8 = 4,000 nominal
                     trajectories (a few trajectories coincide exactly and deduplicate).

Ambiguity is the ancestry itself: an early prefix shared by two trajectories belongs to both.
That is not noise to be cleaned away — it is the shared-ancestry structure the paper asserts and
never measures. We report the sharing distribution and restrict the trajectory-level ICC to
unambiguous rows.

WHAT THE MEASUREMENT SHOWS, and how it revises the caveat
The caveat's DIRECTION is right and its CONCLUSION is not. rho_I is indeed higher within
trajectory than within question, but the design effect is SMALLER there, because trajectories are
small families and DEFF = 1 + (m_tilde - 1) * rho_I is dominated by size. Since park2025 sample
QUESTIONS ("we sample 500 random questions from MATH training split"), the question is the
sampling unit and the question-level DEFF is the complete number, not a floor beneath a bigger one.
So §6.1 should say "questions are the sampling unit; the trajectory level is nested inside and
carries a higher rho_I but a smaller design effect" — not "this is a lower bound".
"""

from __future__ import annotations

import json
import sys
from collections import defaultdict
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import prm_measurement  # noqa: E402
from prm_measurement import anova_icc  # noqa: E402
# Straight from `verdict`, not via `rig`: rig imports torch for the device shim and nothing here
# touches a GPU. This file ships in the paper's verification archive, where a torch dependency
# would be the difference between a reader running it and not.
from verdict import Precondition, emit_verdict  # noqa: E402

# Deferred to prm_measurement rather than hard-coded relative to this file: in the repo this
# file sits one level below prm_measurement.py, in the paper's verification archive they sit
# side by side. Taking the path from the module that owns it (and downloads it) is right in both.
CACHE = prm_measurement.CACHE
THRESH = 0.750          # §6.1's operating threshold (achieved p = 0.8909)


def deff(fams, thresh=THRESH):
    ind = [(f <= thresh).astype(float) for f in fams]
    sizes = np.array([len(f) for f in fams], dtype=float)
    m_til = float((sizes ** 2).sum() / sizes.sum())
    rho = anova_icc(ind)
    return m_til, rho, 1 + (m_til - 1) * rho


def main():
    rows = json.loads(CACHE.read_text())
    byq = defaultdict(list)
    for r in rows:
        byq[r["question"]].append((r["reasoning_prefix"], r["success_prob"]))

    shared, traj_fams, q_fams, chain_counts = [], [], [], []
    for items in byq.values():
        ps = [p for p, _ in items]
        ys = np.array([y for _, y in items])
        srt = [ps[i] for i in sorted(range(len(ps)), key=lambda i: len(ps[i]))]
        maximal = [p for i, p in enumerate(srt)
                   if not any(o.startswith(p) and o != p for o in srt[i + 1:])]
        chain_counts.append(len(maximal))
        memb = [[m for m in maximal if m.startswith(p)] for p in ps]
        shared.extend(len(m) for m in memb)
        q_fams.append(ys)
        g = defaultdict(list)
        for i, m in enumerate(memb):
            if len(m) == 1:                      # unambiguous: exactly one trajectory
                g[m[0]].append(ys[i])
        traj_fams.extend(np.array(v) for v in g.values() if len(v) >= 2)

    sc = np.array(shared)
    n_chains = int(np.sum(chain_counts))
    covered = int((sc >= 1).sum())

    mt_q, rho_q, d_q = deff(q_fams)
    mt_t, rho_t, d_t = deff(traj_fams)

    print(f"{'=' * 74}\nRAW EVIDENCE — chain reconstruction\n{'=' * 74}")
    print(f"  rows {len(sc)}   maximal chains {n_chains}  (nominal 500 x N_val=8 = 4000)")
    print(f"  every row lies on >=1 chain: {covered}/{len(sc)}")
    print(f"  chains per prefix: mean {sc.mean():.3f}  max {sc.max()}")
    for k in range(1, min(sc.max(), 8) + 1):
        n = int((sc == k).sum())
        if n:
            print(f"     on exactly {k} chain(s): {n:6d}  ({n / len(sc):6.2%})")
    print(f"  chains per question: min {min(chain_counts)} median "
          f"{int(np.median(chain_counts))} max {max(chain_counts)}")

    print(f"\n{'=' * 74}\nTWO LEVELS OF CLUSTERING at threshold {THRESH}\n{'=' * 74}")
    print(f"  {'level':<12}{'b':>6}{'m_tilde':>10}{'rho_I':>9}{'DEFF':>9}{'sqrt(DEFF)':>12}")
    print(f"  {'QUESTION':<12}{len(q_fams):>6}{mt_q:>10.2f}{rho_q:>9.4f}{d_q:>9.2f}"
          f"{np.sqrt(d_q):>12.2f}")
    print(f"  {'TRAJECTORY':<12}{len(traj_fams):>6}{mt_t:>10.2f}{rho_t:>9.4f}{d_t:>9.2f}"
          f"{np.sqrt(d_t):>12.2f}")

    emit_verdict(
        "Is within-trajectory correlation higher than within-question, and is §6.1's "
        "'lower bound' caveat right?",
        evidence=[
            f"rows on exactly {k} chain(s): {int((sc == k).sum())} ({(sc == k).mean():.2%})"
            for k in range(1, min(int(sc.max()), 8) + 1) if (sc == k).sum()
        ] + [
            f"question-level family sizes: {[len(f) for f in q_fams[:8]]}",
            f"trajectory-level family sizes: {[len(f) for f in traj_fams[:12]]}",
        ],
        components={
            "maximal chains recovered": n_chains,
            "nominal trajectories (500 x 8)": 4000,
            "rows on exactly one chain": f"{(sc == 1).mean():.4f}",
            "rho_I within QUESTION": round(rho_q, 4),
            "rho_I within TRAJECTORY": round(rho_t, 4),
            "m_tilde QUESTION": round(mt_q, 2),
            "m_tilde TRAJECTORY": round(mt_t, 2),
            "DEFF QUESTION": round(d_q, 2),
            "DEFF TRAJECTORY": round(d_t, 2),
        },
        preconditions={
            "P1 chain count matches the paper's N_val": Precondition(
                bool(3500 <= n_chains <= 4000),
                "the nesting reconstruction is not recovering trajectories at all — park2025 "
                "§3.1 states N_val = 8 per question over 500 questions, so a count far from "
                "4,000 would mean prefixes do not chain the way Stage 2 describes.",
                f"{n_chains} maximal chains vs 4,000 nominal"),
            "P2 every row is covered": Precondition(
                covered == len(sc),
                "some prefix lies on no maximal chain, which is impossible under string-prefix "
                "nesting and would mean the grouping logic is wrong.",
                f"{covered}/{len(sc)} rows lie on at least one chain"),
            "P3 question-level reproduces §6.1": Precondition(
                bool(abs(mt_q - 61.29) < 0.01 and abs(rho_q - 0.4946) < 0.001),
                "this script's family construction differs from prm_measurement.py's, in which "
                "case the trajectory-level number is not comparable to the published one.",
                f"m_tilde {mt_q:.2f} (61.29), rho_I {rho_q:.4f} (0.4946), DEFF {d_q:.2f} (30.8)"),
        },
        rules=[
            (rho_t > rho_q, f"rho_I IS higher within trajectory ({rho_t:.4f} vs {rho_q:.4f}) — "
                            f"the caveat's DIRECTION is confirmed"),
            (d_t < d_q, f"but the trajectory DEFF is SMALLER ({d_t:.2f} vs {d_q:.2f}), because "
                        f"m_tilde falls {mt_q:.1f} -> {mt_t:.1f}; questions are the sampling "
                        f"unit, so 30.8 is the complete number, NOT a lower bound"),
        ],
    )


if __name__ == "__main__":
    main()
