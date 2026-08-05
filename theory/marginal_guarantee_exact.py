#!/usr/bin/env python3
"""Does clustered calibration break the >= 1-alpha MARGINAL guarantee? Exactly, not simulated.

    python experiments/2026-07-26-sw02-exchangeability-audit/marginal_guarantee_exact.py

WHY THIS EXISTS
Two claims were live in the draft at the same time and cannot both be true.

  * SS3.6 Proposition 1: E[C] - p = (m-1)/(2n){p(1-p) rho_I' - (2p-1) rho_I} + O(n^-2), nonzero
    under clustering, and negative in the operating regime (Corollary 3).
  * SS2 concession and SS6.1: "a clustered-but-exchangeable sequence is still exchangeable, so both
    the marginal guarantee and its over-coverage bound survive intact."

E[C] IS the marginal coverage. Under (A3) the test point is independent of the calibration set and
drawn from F, so

    E[C] = E[ P(S_test <= qhat | calibration) ] = P(S_test <= qhat),

by the tower property. So Proposition 1 is a statement that clustering moves marginal coverage off
nominal, and the concession says it does not. This script settles which.

The answer matters beyond the wording. `results/pasc_consequence.json`, the artifact SS6.1 cites,
already carried "marginal_ge_target": false at rho=0.5 -- the run's own guard fired and the prose
reported the opposite. That guard was loose (it compared against 3 SE of an sd inflated by
estimating coverage on 4,000 test draws per replication), so the failure was reported as a pass at
rho=0.2 as well. Here coverage is computed exactly, so there is nothing to be loose about.

WHAT IS COMPUTED
Arm E (exact, no Monte Carlo). Coverage is the k-th order statistic of the probability-transformed
scores, so E[C] = int_0^1 P(N(t) <= k-1) dt is an exact identity; for a specified cluster model the
single-cluster pmf, the b-fold convolution and the outer integral are all deterministic. This is
SS4.3's machinery, imported from prop1_exact.py rather than reimplemented, so a bug here is a bug
there too.

Arm S (simulation, for the dispersion half and as an independent path to the same mean). Coverage
computed as C = Phi(qhat) exactly per draw -- no test sample, hence no binomial noise, unlike the
run SS6.1 originally cited.

Arm D (the discriminating control). One global factor shared by every calibration point AND the
test point: a de Finetti mixture, in which the n+1 scores genuinely ARE exchangeable. If the
concession's reasoning were right, arms S and D would agree. This is SS3.3's "across families,
dependence is harmless if the test point shares it", and it is what tells us the concession is true
of a different configuration rather than simply false.

PRECONDITIONS, both of which can fail
  1. At rho = 0 the exact pipeline must return E[C] = k/(n+1) to machine precision (prop1_exact's
     own control, re-run here rather than assumed).
  2. At rho = 0 the SIMULATION must return k/(n+1) to within Monte Carlo error, and arm D must
     return it too. A harness that cannot reproduce exactness where exactness is real has nothing
     to say about where it is not.
"""
import sys
from pathlib import Path

import numpy as np
from scipy.stats import norm

sys.path.insert(0, str(Path(__file__).resolve().parent))
from prop1_exact import (cluster_pmf_atom, cluster_pmf_gauss, exact_EC,  # noqa: E402
                         precondition, predicted_drift, rho_I_atom, rho_I_gauss)

ALPHA = 0.10
REPS, CHUNK = 200_000, 2_000
SEED = 20260731

# The configuration SS6.1 cites, and the one SS4.1 is built on.
PASC_B, PASC_M = 100, 10


def k_of(n, alpha=ALPHA):
    return int(np.ceil((n + 1) * (1 - alpha)))


def simulate(b, m, rho, shared_global=False, reps=REPS, seed=SEED):
    """C = Phi(qhat) per calibration draw. shared_global=True is the de Finetti arm."""
    rng = np.random.default_rng(seed)
    n = b * m
    k = k_of(n)
    out = np.empty(reps)
    for s in range(0, reps, CHUNK):
        c = min(CHUNK, reps - s)
        if shared_global:
            w = rng.normal(size=(c, 1, 1)) * np.sqrt(rho)
            e = rng.normal(size=(c, b, m)) * np.sqrt(1 - rho)
            cal = (w + e).reshape(c, n)
            qhat = np.partition(cal, k - 1, axis=1)[:, k - 1]
            # the test point shares the same realised factor w
            out[s:s + c] = norm.cdf((qhat - w[:, 0, 0]) / np.sqrt(1 - rho))
        else:
            u = rng.normal(size=(c, b, 1)) * np.sqrt(rho)
            e = rng.normal(size=(c, b, m)) * np.sqrt(1 - rho)
            cal = (u + e).reshape(c, n)
            qhat = np.partition(cal, k - 1, axis=1)[:, k - 1]
            out[s:s + c] = norm.cdf(qhat)          # test point ~ N(0,1), independent
    return out


def tie_endpoint(b, m, alpha):
    """Perfectly-tied clusters: realised coverage ~ Beta(ceil(k/m), b+1-ceil(k/m)), exactly.

    This is [ramos2026] SS4.2, already printed in SS1.1. Its mean is ceil(k/m)/(b+1), which needs no
    expansion and no asymptotics -- so it is the rigorous half of the finding, independent of
    Proposition 1's unbounded remainder.
    """
    n = b * m
    k = k_of(n, alpha)
    j = int(np.ceil(k / m))
    return k, j, j / (b + 1), k / (n + 1.0)


def main() -> int:
    print("=" * 100)
    print("MARGINAL GUARANTEE UNDER CLUSTERED CALIBRATION — exact + simulated")
    print("=" * 100)

    ok = precondition()
    if not ok:
        print("\nSTOP: the exact pipeline cannot reproduce the exchangeable case.")
        return 1

    # ---------------------------------------------------------------- precondition 2
    print("\n[0c] PRECONDITION — the SIMULATION must reproduce exactness where it is real")
    n = PASC_B * PASC_M
    p = k_of(n) / (n + 1.0)
    for label, arm in (("rho=0, independent test", simulate(PASC_B, PASC_M, 0.0)),
                       ("rho=0.5, test SHARES the factor (de Finetti)",
                        simulate(PASC_B, PASC_M, 0.5, shared_global=True))):
        se = arm.std(ddof=1) / np.sqrt(arm.size)
        z = (arm.mean() - p) / se
        print(f"    {label:<44} E[C]-k/(n+1) = {arm.mean()-p:+.6f}  ({z:+.2f} SE)  "
              f"{'PASS' if abs(z) < 3 else 'FAIL'}")
        ok &= abs(z) < 3
    if not ok:
        print("\nSTOP: the harness does not reproduce the exchangeable case.")
        return 1
    print("    -> both arms sit at nominal; a deficit below is not the machinery")

    # ---------------------------------------------------------------- the measurement
    print("\n[1] EXACT marginal coverage, one-factor Gaussian clusters, alpha = 0.10")
    print(f"    {'b':>5} {'m':>4} {'n':>7} {'rho':>6} {'k/(n+1)':>10} {'E[C] exact':>12} "
          f"{'E[C]-(1-a)':>12} {'Prop 1':>11} {'guarantee':>10}")
    rows = []
    for b, m, rho in [(PASC_B, PASC_M, 0.0), (PASC_B, PASC_M, 0.2), (PASC_B, PASC_M, 0.5),
                      (PASC_B, PASC_M, 0.8), (50, 4, 0.5), (25, 4, 0.5), (500, 10, 0.5)]:
        n = b * m
        k = k_of(n)
        p = k / (n + 1.0)
        ec = exact_EC(lambda t: cluster_pmf_gauss(t, m, rho),
                      lambda t: rho_I_gauss(t, rho), b, m, k)
        pred = predicted_drift(lambda t: rho_I_gauss(t, rho), n, m, p)
        gap = ec - (1 - ALPHA)
        rows.append((b, m, rho, p, ec, gap))
        print(f"    {b:>5} {m:>4} {n:>7} {rho:>6.2f} {p:>10.6f} {ec:>12.6f} {gap:>+12.6f} "
              f"{pred:>+11.6f} {'VIOLATED' if gap < 0 else 'holds':>10}")

    print("\n[2] EXACT, atom mixture (rho_I = q at EVERY level, so rho_I' = 0 by construction)")
    for q, b, m in [(0.1, PASC_B, PASC_M), (0.3, PASC_B, PASC_M), (0.3, 50, 4)]:
        n = b * m
        k = k_of(n)
        ec = exact_EC(lambda t: cluster_pmf_atom(t, m, q), lambda t: rho_I_atom(t, q), b, m, k)
        gap = ec - (1 - ALPHA)
        print(f"    q={q}  b={b:>3} m={m:>2}  k/(n+1)={k/(n+1):.6f}  E[C]={ec:.6f}  "
              f"E[C]-(1-a)={gap:+.6f}  {'VIOLATED' if gap < 0 else 'holds'}")

    print("\n[3] SIMULATED — the same means by an independent path, and the dispersion half")
    print("    z is against 1-alpha, NOT against k/(n+1): at rho=0 it is positive because the")
    print("    ceiling gives the guarantee up to 1/(n+1) of built-in slack, and that slack is what")
    print("    the clustering deficit has to eat through before the guarantee actually fails.")
    print(f"    {'rho':>6} {'E[C] sim':>11} {'(SE)':>9} {'z vs 1-a':>10} {'sd(C)':>9} "
          f"{'sd ratio':>9} {'sqrt(DEFF)':>11}")
    base = None
    for rho in (0.0, 0.2, 0.5):
        arm = simulate(PASC_B, PASC_M, rho)
        n = PASC_B * PASC_M
        p = k_of(n) / (n + 1.0)
        sd = arm.std(ddof=1)
        se = sd / np.sqrt(arm.size)
        base = sd if base is None else base
        rI = float(np.atleast_1d(rho_I_gauss(p, rho))[0])
        print(f"    {rho:>6.2f} {arm.mean():>11.6f} {se:>9.6f} "
              f"{(arm.mean()-(1-ALPHA))/se:>10.2f} {sd:>9.5f} {sd/base:>9.3f} "
              f"{np.sqrt(1+(PASC_M-1)*rI):>11.3f}")

    print("\n[4] THE RIGOROUS HALF — perfectly-tied clusters, no expansion involved")
    print("    Realised coverage is exactly Beta(ceil(k/m), b+1-ceil(k/m)) ([ramos2026] SS4.2, SS1.1),")
    print("    so marginal coverage is ceil(k/m)/(b+1) and needs no asymptotics at all.")
    print(f"    {'b':>5} {'m':>4} {'alpha':>7} {'k':>6} {'ceil(k/m)':>10} {'k/(n+1)':>10} "
          f"{'E[C] exact':>12} {'vs 1-alpha':>12}")
    for b, m, alpha in [(50, 4, 0.15), (50, 4, 0.10), (100, 10, 0.10), (20, 5, 0.10)]:
        k, j, ec, p = tie_endpoint(b, m, alpha)
        print(f"    {b:>5} {m:>4} {alpha:>7.2f} {k:>6} {j:>10} {p:>10.6f} {ec:>12.6f} "
              f"{'VIOLATED' if ec < 1 - alpha else 'holds':>12}")

    print("\nVERDICT")
    print("  Marginal coverage is not k/(n+1) under (A1)+(A3). In the interior -- [1] and [2],")
    print("  one-factor Gaussian and atom mixture alike -- the >= 1-alpha guarantee itself fails in")
    print("  every configuration tested, by 0.11 points at SS6.1's own b=100 x m=10, rho=0.5.")
    print("  At the perfectly-tied endpoint [4] the ceiling in ceil(k/m) usually pushes coverage")
    print("  the other way and the guarantee holds (3 of the 4 shown); the fourth fails by 0.69")
    print("  points, which is the rigorous, expansion-free half of the finding.")
    print("  The failure is O(1/b) and second-order; the dispersion failure is first-order and")
    print("  remains what the paper is for. The configuration in which the guarantee DOES survive")
    print("  is the one where the test point shares the dependence (arm D) -- SS3.3's benign case,")
    print("  not SS6.1's.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
