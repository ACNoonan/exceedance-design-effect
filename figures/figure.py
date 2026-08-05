"""SW-02 §5 — the ancestry-sharing sweep. Research version.

    python experiments/2026-07-26-sw02-exchangeability-audit/figure.py

Regenerates the table and figure in DRAFT.md.

Per STRUCTURE.md this shares nothing with the lesson version
(`lessons/02-split-conformal.ipynb`) except `calkit.conformal.split_conformal`. Lessons run on
substrates you can throw away; research runs on substrates you have to defend. The simulation
is re-implemented here rather than imported from `lessons/` on purpose.

NOTE: this will raise NotImplementedError until L2 lands `split_conformal` in calkit. That is
deliberate — the paper's central figure cannot be regenerated until the guarantee-bearing line
is owned. The numbers currently in DRAFT.md came from a reference implementation of the same
three lines and should reproduce exactly.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

# calkit/ and _conformal.py sit at the code-archive root; in the paper's working
# tree they are vendored under external/. Cover both layouts.
_HERE = Path(__file__).resolve().parent
for _p in (_HERE.parent / "external", _HERE.parent, _HERE / "external", _HERE):
    sys.path.insert(0, str(_p))
from calkit.conformal import split_conformal  # noqa: E402

HERE = Path(__file__).resolve().parent

N_FAMILIES = 50
FAMILY_SIZE = 4
N_TEST = 2000
ALPHA = 0.10
N_REPS = 600
SEED = 0
BAD = 0.85
RHOS = (0.0, 0.2, 0.4, 0.6, 0.8, 0.95, 1.0)


def ancestry_scores(n_families: int, family_size: int, rho: float, rng) -> np.ndarray:
    """Scores in correlated families; within-family correlation exactly rho.

    Marginally N(0,1) for every rho, so only the dependence structure varies and no
    distribution shift can contaminate the result.
    """
    ancestor = rng.normal(size=(n_families, 1))
    own = rng.normal(size=(n_families, family_size))
    return (np.sqrt(rho) * ancestor + np.sqrt(1.0 - rho) * own).ravel()


def kish_n_eff(n: int, family_size: int, rho: float) -> float:
    return n / (1.0 + (family_size - 1) * rho)


def sweep() -> list[dict]:
    n = N_FAMILIES * FAMILY_SIZE
    rows = []
    for rho in RHOS:
        rng = np.random.default_rng(SEED)
        cov = np.empty(N_REPS)
        for r in range(N_REPS):
            cal = ancestry_scores(N_FAMILIES, FAMILY_SIZE, rho, rng)
            test = rng.normal(size=N_TEST)          # fresh: no siblings in the set
            cov[r] = float(np.mean(test <= split_conformal(cal, ALPHA)))
        p05, p95 = np.percentile(cov, [5, 95])
        rows.append({
            "rho": rho, "n_eff": kish_n_eff(n, FAMILY_SIZE, rho),
            "mean": cov.mean(), "p05": p05, "p95": p95, "width": p95 - p05,
            "frac_below": float(np.mean(cov < BAD)),
        })
    return rows


def main() -> int:
    rows = sweep()
    hdr = f"{'rho':>5} {'n_eff':>7} {'mean':>7} {'p05':>7} {'p95':>7} {'width':>7} {'P(<0.85)':>9} {'w*sqrt(neff)':>13}"
    print(f"n={N_FAMILIES*FAMILY_SIZE} ({N_FAMILIES}x{FAMILY_SIZE}), alpha={ALPHA}, "
          f"{N_REPS} reps, nominal {1-ALPHA:.2f}\n{hdr}")
    for r in rows:
        print(f"{r['rho']:>5.2f} {r['n_eff']:>7.1f} {r['mean']:>7.4f} {r['p05']:>7.4f} "
              f"{r['p95']:>7.4f} {r['width']:>7.4f} {r['frac_below']:>9.3f} "
              f"{r['width']*np.sqrt(r['n_eff']):>13.3f}")

    print(f"\nmean coverage range: {min(r['mean'] for r in rows):.4f}"
          f" - {max(r['mean'] for r in rows):.4f}  <- the statistic everyone reports")
    print(f"P(cov<{BAD}) range:      {min(r['frac_below'] for r in rows):.3f}"
          f" - {max(r['frac_below'] for r in rows):.3f}  <- what a deployer experiences")

    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except ImportError:
        print("\n(matplotlib unavailable; table only)")
        return 0

    rho = [r["rho"] for r in rows]
    fig, ax = plt.subplots(1, 2, figsize=(11, 4))
    ax[0].axhline(1 - ALPHA, color="k", ls="--", lw=1, label=f"nominal {1-ALPHA:.2f}")
    ax[0].fill_between(rho, [r["p05"] for r in rows], [r["p95"] for r in rows],
                       alpha=0.25, label="5th–95th pct across deployments")
    ax[0].plot(rho, [r["mean"] for r in rows], "o-", label="mean coverage")
    ax[0].set_xlabel(r"$\rho$  (within-family correlation)")
    ax[0].set_ylabel("coverage")
    ax[0].set_title("Mean preserved, dispersion inflated")
    ax[0].legend(fontsize=8)

    ax[1].plot(rho, [r["frac_below"] for r in rows], "o-", color="crimson")
    ax[1].set_xlabel(r"$\rho$")
    ax[1].set_ylabel(f"P(coverage < {BAD})")
    ax[1].set_title("Rate of materially under-covered deployments")
    ax2 = ax[1].twinx()
    ax2.plot(rho, [r["n_eff"] for r in rows], "s--", color="grey", alpha=0.6)
    ax2.set_ylabel(r"Kish $n_{\mathrm{eff}}$", color="grey")

    fig.tight_layout()
    out = HERE / "figure_ancestry_sweep.png"
    fig.savefig(out, dpi=150)
    print(f"\nwrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
