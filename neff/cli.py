"""CLI: `neff outcomes|scores|passk` — the reporting line from a terminal.

Examples:
    neff outcomes results.csv --cluster-col repo --value-col resolved --unit repo
    neff scores cal.csv --cluster-col prompt --value-col score --level 0.9 --unit prompt
    neff passk --pass-at 1=0.428,2=0.522,3=0.568,4=0.596,5=0.615 --trials 5 --n-items 89
"""

from __future__ import annotations

import argparse
import csv
import json
import sys

from .report import analyze_outcomes, analyze_passk, analyze_scores


def _read_csv(path: str, cluster_col: str, value_col: str) -> tuple[list, list[float]]:
    with open(path, newline="") as fh:
        rows = list(csv.DictReader(fh))
    if not rows:
        sys.exit(f"neff: {path} is empty")
    for col in (cluster_col, value_col):
        if col not in rows[0]:
            sys.exit(f"neff: column {col!r} not in {path} (has: {', '.join(rows[0])})")
    ids = [r[cluster_col] for r in rows]
    vals = [float(r[value_col]) for r in rows]
    return ids, vals


def _parse_pass_at(spec: str) -> dict[int, float]:
    out: dict[int, float] = {}
    for part in spec.split(","):
        k, _, v = part.partition("=")
        out[int(k)] = float(v)
    return out


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(prog="neff", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--unit", default=None, help="name of the resampled unit for the report line")
    common.add_argument("--json", action="store_true", help="print the full readout as JSON")

    p1 = sub.add_parser("outcomes", parents=[common], help="per-observation outcomes with cluster ids")
    p1.add_argument("csv_path")
    p1.add_argument("--cluster-col", default="cluster")
    p1.add_argument("--value-col", default="value")

    p3 = sub.add_parser("scores", parents=[common], help="scores + cluster ids at an operating level")
    p3.add_argument("csv_path")
    p3.add_argument("--cluster-col", default="cluster")
    p3.add_argument("--value-col", default="score")
    p3.add_argument("--level", type=float, required=True, help="operating level p in (0,1)")
    p3.add_argument("--threshold", type=float, default=None,
                    help="fixed threshold (when calibration and deployment pools are separate)")

    p2 = sub.add_parser("passk", parents=[common], help="published accuracy + pass@k spectrum")
    p2.add_argument("--pass-at", required=True,
                    help="comma list k=fraction, e.g. 1=0.428,2=0.522,... (pass@1 is the accuracy)")
    p2.add_argument("--trials", type=int, required=True, help="K, trials per item")
    p2.add_argument("--n-items", type=int, required=True)

    a = ap.parse_args(argv)
    if a.cmd == "outcomes":
        ids, vals = _read_csv(a.csv_path, a.cluster_col, a.value_col)
        rep = analyze_outcomes(vals, ids, unit=a.unit or a.cluster_col)
    elif a.cmd == "scores":
        ids, vals = _read_csv(a.csv_path, a.cluster_col, a.value_col)
        rep = analyze_scores(vals, ids, level=a.level, threshold=a.threshold,
                             unit=a.unit or a.cluster_col)
    else:
        rep = analyze_passk(_parse_pass_at(a.pass_at), K=a.trials, n_items=a.n_items,
                            unit=a.unit or "item")
        if not rep.extras["well_determined"]:
            print("neff: WARNING — spectrum is incomplete (needs pass@1..K); "
                  "the recovery is a least-squares solution, not a unique one", file=sys.stderr)

    print(rep.line())
    if a.json:
        print(json.dumps(rep.to_dict(), indent=2, default=float))


if __name__ == "__main__":
    main()
