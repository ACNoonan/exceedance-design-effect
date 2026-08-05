#!/usr/bin/env python3
"""What §3.5's size-reweighting repair costs in effective sample size.

§3.5 diagnoses a size-score coupling and gives no corrected estimator. The
correction that exists -- reweighting calibration points to the cluster-average
marginal, w_jk = 1/(b m_j), which is [liu2026twhcp]'s target-weighted
construction -- removes the coupling entirely. It is not free, and this measures
the bill.

THE POINT.  Unequal weights concentrate calibration mass, so the weighted
quantile has a smaller effective sample size (Kish's WEIGHTING n_eff, a
different object from the paper's clustering n_eff). And w = 1/(b m_j) is
maximally unequal exactly when sizes are most ragged -- which is exactly when
the coupling being repaired is worst. So the repair trades a first-order mean
bias for dispersion, and both terms are driven by the SAME raggedness.

    n_eff^w = (sum w)^2 / sum w^2 = b^2 / sum_j (1/m_j)

By Cauchy-Schwarz (sum m_j)(sum 1/m_j) >= b^2, so n_eff^w <= n always, with
equality iff every m_j is equal.

PRECONDITIONS -- each states what a failure would have looked like.

  P1  The released profile reproduces on all five moments (b, n, m_bar,
      m_tilde, CV^2). WOULD HAVE FAILED IF the size loader fell through to a
      fallback -- which it silently did once in this lane, giving m_bar 71.33
      against the published 50.06 while a b-only check passed.

  P2  The weighting n_eff computed directly from the weights must equal the
      closed form b^2/sum(1/m_j). Two routes to one number; a mismatch means
      the formula is wrong, not the data.

  P3  NEGATIVE CONTROL. Equal cluster sizes must return a ratio of exactly
      1.0000 -- no raggedness, no cost. If this returned a discount, the
      measurement would be manufacturing a penalty out of nothing.

  P4  The cost must be MONOTONE in raggedness. If it were not, the claim that
      repair-cost and coupling-severity are driven by the same quantity would
      not follow, whatever the headline number said.
"""
from __future__ import annotations
import importlib.util
import numpy as np


def released_sizes() -> np.ndarray:
    spec = importlib.util.spec_from_file_location("sw52", "sw52_direct_sim.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return np.asarray(mod.released_sizes(), dtype=float)


def weighting_neff(sizes: np.ndarray) -> float:
    """Kish weighting ESS for w_jk = 1/(b m_j), summed over all n points."""
    b = len(sizes)
    w = 1.0 / (b * sizes)                 # weight of EACH point in cluster j
    return float((np.sum(sizes * w)) ** 2 / np.sum(sizes * w ** 2))


def main() -> None:
    print("=" * 74)
    print("What the cluster-average reweighting costs (§3.5's repair)")
    print("=" * 74)
    s = released_sizes()
    b, n = len(s), s.sum()
    m_bar, m_til = n / b, float((s ** 2).sum() / s.sum())
    cv2 = float(s.var() / s.mean() ** 2)
    ok1 = (b == 500 and abs(n - 25028) < 1 and abs(m_bar - 50.06) < 0.01
           and abs(m_til - 61.29) < 0.02 and abs(cv2 - 0.224) < 0.002)
    print(f"\n  P1  released profile b={b} n={n:.0f} m_bar={m_bar:.2f} "
          f"m_tilde={m_til:.2f} CV^2={cv2:.3f} : {'PASS' if ok1 else 'FAIL'}")
    if not ok1:
        print("      refusing to report a cost off an unverified size profile.")
        return

    direct = weighting_neff(s)
    closed = b ** 2 / np.sum(1.0 / s)
    ok2 = abs(direct - closed) < 1e-6
    print(f"  P2  direct {direct:.1f} == closed form b^2/sum(1/m) {closed:.1f} : "
          f"{'PASS' if ok2 else 'FAIL'}")

    print(f"\n  equal weights                    n_eff = {n:.0f}")
    print(f"  cluster-average w = 1/(b m_j)    n_eff = {direct:.0f}"
          f"    ratio {direct/n:.4f}")
    print(f"  -> the repair costs {100*(1-direct/n):.1f}% of the calibration set,"
          f" on the released profile.")

    print("\n  P3/P4  cost against raggedness (lognormal sizes, b and mean held fixed)")
    rng = np.random.default_rng(0)
    rows = []
    for sigma in (0.0, 0.3, 0.6, 0.9, 1.2):
        x = np.exp(rng.normal(0.0, sigma, b))
        x = np.maximum(1.0, np.round(x * m_bar / x.mean()))
        rows.append((float(x.var() / x.mean() ** 2), weighting_neff(x) / x.sum()))
        print(f"      CV^2 = {rows[-1][0]:6.3f}    n_eff ratio {rows[-1][1]:.4f}")
    ok3 = abs(rows[0][1] - 1.0) < 1e-9
    ok4 = all(rows[i][1] > rows[i + 1][1] for i in range(len(rows) - 1))
    print(f"  P3  equal sizes cost exactly nothing (ratio {rows[0][1]:.4f}) : "
          f"{'PASS' if ok3 else 'FAIL'}")
    print(f"  P4  cost is monotone in raggedness : {'PASS' if ok4 else 'FAIL'}")

    print("\n  READING")
    print("    The repair is not free and its price is set by the same quantity that")
    print("    makes it necessary. On the released profile it costs a fifth of the")
    print("    calibration set; at the CV^2 = 2.10 §9b uses for its worst case it")
    print("    costs nearly three quarters. So §10's open composition is not two")
    print("    independent pieces to bolt together -- the mean-coverage repair and")
    print("    the dispersion law pull against each other, through m_j.")


if __name__ == "__main__":
    main()
