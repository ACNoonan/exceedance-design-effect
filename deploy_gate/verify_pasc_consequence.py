#!/usr/bin/env python3
"""Which of PASC's guarantees does clustering actually touch? Simulated, because I asserted
something I had not checked.

THE CLAIM I MADE AND NOW DOUBT: that PASC's "nearly tight up to 1/(n+1)" degrades to 1/(n_eff+1).
That conflates two different guarantees:

  * MARGINAL coverage, averaged over calibration draws. A clustered-but-exchangeable sequence (a de
    Finetti mixture) IS exchangeable, so the rank of the test score among n+1 scores is still
    uniform and BOTH the >= 1-alpha guarantee and the <= 1-alpha+1/(n+1) upper bound should survive.
  * TRAINING-CONDITIONAL coverage, for the one calibration set you actually deployed. That is what
    SW-02 Theorem 1 governs, and its dispersion is p(1-p)/n_eff.

If the simulation shows marginal coverage intact and dispersion inflated, then the honest statement
about PASC is about per-deployment reliability, NOT about its tightness constant -- and my earlier
claim was wrong.

Arm 2 asks the multi-stage question: with K thresholds calibrated on ONE clustered pool, are the
stages' realised levels correlated, and does that inflate the dispersion of JOINT realised coverage
beyond what independent stages would give?
"""
import numpy as np, json
from pathlib import Path

rng = np.random.default_rng(20260730)
OUT = Path(__file__).resolve().parent / "results"; OUT.mkdir(exist_ok=True)
ALPHA, B, M, REPS, NTEST = 0.10, 100, 10, 4000, 4000
N = B * M

def clustered(b, m, rho, k=1):
    """k correlated score dimensions; within-cluster correlation rho via a shared cluster effect."""
    u = rng.normal(size=(b, 1, k)) * np.sqrt(rho)
    e = rng.normal(size=(b, m, k)) * np.sqrt(1 - rho)
    return (u + e).reshape(b * m, k)

def run(rho, k=1, label=""):
    covs, joint = [], []
    idx = int(np.ceil((N + 1) * (1 - ALPHA))) - 1
    for _ in range(REPS):
        cal = clustered(B, M, rho, k)
        if k == 1:
            q = np.sort(cal[:, 0])[idx]
            te = clustered(NTEST, 1, rho, 1)[:, 0]
            covs.append(float((te <= q).mean()))
        else:
            # Bonferroni: each stage at alpha/K on the SAME clustered pool
            ib = int(np.ceil((N + 1) * (1 - ALPHA / k))) - 1
            qs = np.array([np.sort(cal[:, j])[ib] for j in range(k)])
            te = clustered(NTEST, 1, rho, k)[:, :]
            joint.append(float((te <= qs).all(axis=1).mean()))
    a = np.array(covs if k == 1 else joint)
    return {"label": label, "rho": rho, "k": k,
            "mean_coverage": float(a.mean()), "sd_coverage": float(a.std(ddof=1)),
            "target": 1 - ALPHA,
            "upper_bound_1_over_n_plus_1": 1 - ALPHA + 1 / (N + 1),
            "marginal_ge_target": bool(a.mean() >= 1 - ALPHA - 3 * a.std(ddof=1) / np.sqrt(REPS)),
            "marginal_le_upper": bool(a.mean() <= 1 - ALPHA + 1 / (N + 1) + 3 * a.std(ddof=1) / np.sqrt(REPS))}

print(f"n = {N} ({B} clusters x {M}), alpha = {ALPHA}, {REPS} calibration draws\n")
print("ARM 1 -- single threshold (PASC's shared-quantile form)")
res = []
for rho in (0.0, 0.2, 0.5):
    r = run(rho, 1, f"single, rho_score={rho}")
    res.append(r)
    print(f"  rho={rho:.1f}  mean cov={r['mean_coverage']:.4f} (target {1-ALPHA}, "
          f"upper {r['upper_bound_1_over_n_plus_1']:.4f})  sd={r['sd_coverage']:.4f}  "
          f"marginal holds: >= {r['marginal_ge_target']}, <= {r['marginal_le_upper']}")
base = res[0]["sd_coverage"]
for r in res:
    print(f"    rho={r['rho']:.1f} dispersion inflation vs iid: {r['sd_coverage']/base:.2f}x")

print("\nARM 2 -- K=3 Bonferroni thresholds on ONE clustered pool")
res2 = []
for rho in (0.0, 0.2, 0.5):
    r = run(rho, 3, f"K=3 Bonferroni, rho_score={rho}")
    res2.append(r)
    print(f"  rho={rho:.1f}  mean JOINT cov={r['mean_coverage']:.4f} (target >= {1-ALPHA})  "
          f"sd={r['sd_coverage']:.4f}")
b2 = res2[0]["sd_coverage"]
for r in res2:
    print(f"    rho={r['rho']:.1f} joint dispersion inflation vs iid: {r['sd_coverage']/b2:.2f}x")

(OUT / "pasc_consequence.json").write_text(json.dumps({"arm1": res, "arm2": res2}, indent=2))
print(f"\nwrote {OUT/'pasc_consequence.json'}")
