"""EC-01 E1 — does the coverage law hold DISTRIBUTIONALLY, or only in variance?

    ../../.venv/bin/python e1_shape_test.py

WHAT IS AT STAKE
SW-30 already concedes, in the paper: the Beta-at-n_eff form "matches those two moments and is the
form we use throughout, as an approximation rather than a corollary: a central limit theorem fixes
two moments, not a distribution." Every percentile column and every 5-95 range in the paper rides
on that approximation. Nothing has ever tested it.

§6.1 measures a dispersion RATIO (4.46x tie-broken). A ratio is a variance statement. This asks the
next question: once the variance is matched, does the SHAPE survive?

THREE REFERENCE LAWS AGAINST ONE EMPIRICAL SAMPLE
  naive      Beta(k, n+1-k) at nominal n = 25,028      the law the field currently assumes
  plugin     Beta at the plug-in n_eff = 812           our formula evaluated on our own estimate
  matched    Beta at the n_eff implied by the MEASURED variance
             -> variance is matched BY CONSTRUCTION, so residual distance is SHAPE ALONE

`matched` is the only arm that tests something not already known, and it is the one that can come
out wrong. Registered in PREREG.md before running: if it is rejected, the Beta form is a variance
statement only and every percentile column in the paper is withdrawn, leaving Theorem 1 -- a CLT,
which never depended on the Beta shape -- intact.

WHY BOTH ARMS
The raw 9-atom score cannot follow ANY continuous law: coverage is confined to the 9 values F
attains at its atoms, so a KS distance against a Beta is large for a reason that has nothing to do
with n_eff. That arm is reported to make the discreteness visible, NOT as evidence about the shape
question. The tie-broken arm is where the shape question is posed.

WHAT THE NUMBERS HERE ARE AND ARE NOT
The empirical sample is a cluster bootstrap over the 500 released questions, so it approximates the
sampling distribution of C rather than drawing from it. KS *p-values* against a fitted law are
therefore indicative only and are not reported as tests. What is reported is the KS DISTANCE
compared ACROSS the three laws on the same sample -- a relative comparison, robust to the
bootstrap's own bias in a way an absolute p-value is not -- plus skewness, the shape statistic the
informative-size channel is predicted to move.

Precondition numbering follows the parent lane's `P1..Pn` convention (prm_dispersion.py); no new
identifier namespace is coined here.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
from scipy.stats import beta as beta_dist, kstest, skew

PARENT = Path(__file__).resolve().parents[1] / "2026-07-26-sw02-exchangeability-audit"
sys.path.insert(0, str(PARENT))
from prm_dispersion import (  # noqa: E402
    JITTER, _flatten, coverage_dist, operating_level, plugin_ratio,
)
from prm_measurement import load  # noqa: E402

SEED = 20260729
REPS = 8000
PLUGIN_NEFF = 812.0          # §6.1 as published


def beta_for(n_eff: float, level: float):
    """The paper's working form, verbatim from `sections/03_coverage_law.md:61`:

        C ~ Beta(p(n_eff - 1), (1-p)(n_eff - 1))

    whose mean is exactly p and whose variance is exactly p(1-p)/n_eff.

    CORRECTED 2026-08-01 (`sw02ext/Q-07b`). This previously built `Beta(k, n_eff+1-k)` with
    k = ceil((n_eff+1)*level) — the exact i.i.d. law, which is NOT what §3.2 defines and NOT what
    the paper's percentile columns use. Rounding k up puts that law's mean above p by up to one
    lattice step 1/(n_eff+1), and at n_eff ~ 800 that is 0.08 sd of the coverage distribution. The
    consequence was arm-dependent, because where ceil lands depends on n_eff: the plug-in arm's
    distance was inflated by 36% (0.0965 against 0.0710 on the identical sample) while the naive
    and matched arms were untouched, the latter only because ceil happened to land on p at
    n_eff = 1,281. A test of "does the paper's law fit" has to instantiate the paper's law.

    `neff_matching_var` below inherits this and thereby becomes exact rather than approximate:
    under this form the variance is p(1-p)/n_eff, so the bisection now inverts a closed form and
    the recovered n_eff is the paper's own definition of n_eff rather than a near neighbour of it.

    Evidence: experiments/2026-08-01-sw02-extensions/runs/Q-07b_beta_parameterisation_audit.log
    (replay of this file's own random stream reproduces the pre-correction numbers bit-exactly,
    so the two parameterisations are compared on the identical sample).
    """
    nu = max(n_eff - 1.0, 1e-9)
    return beta_dist(level * nu, (1 - level) * nu)


def neff_matching_var(var: float, level: float) -> float:
    """n_eff whose Beta variance equals the measured variance. Bisection on a monotone map."""
    lo, hi = 2.0, 1e7
    for _ in range(200):
        mid = np.sqrt(lo * hi)
        if beta_for(mid, level).var() > var:
            lo = mid
        else:
            hi = mid
    return float(np.sqrt(lo * hi))


def compare(sample: np.ndarray, laws: dict) -> dict:
    out = {}
    for name, dist in laws.items():
        out[name] = {
            "ks_D": float(kstest(sample, dist.cdf).statistic),
            "law_sd": float(dist.std()),
            "law_mean": float(dist.mean()),
            "law_skew": float(dist.stats("s")),
        }
    return out


def main() -> int:
    rng = np.random.default_rng(SEED)
    fams = load()
    scores, sizes, starts = _flatten(fams)
    n = len(scores)
    t_star, level = operating_level(scores)

    print("=" * 78)
    print("EC-01 E1 — the SHAPE test: is Beta-at-n_eff a distribution or only two moments?")
    print("=" * 78)
    print(f"released set: n = {n}, b = {len(sizes)} questions")
    print(f"operating point (§6.1's rule): threshold {t_star:.3f}, achieved p = {level:.4f}\n")

    sq, rho, m_til, _ = plugin_ratio(scores, starts, sizes, thresh=t_star)
    print(f"plug-in: rho_I = {rho:.4f}, m_tilde = {m_til:.2f}, sqrt(DEFF) = {sq:.2f}, "
          f"n_eff = {n / (sq ** 2):.0f}")

    result = {"meta": {"n": n, "b": len(sizes), "level": level, "threshold": t_star,
                       "rho_I": rho, "m_tilde": m_til, "plugin_neff": PLUGIN_NEFF,
                       "reps": REPS, "seed": SEED}, "arms": {}}

    for arm_name, sc in (("raw", scores),
                         ("tiebroken", scores + rng.uniform(0, JITTER, n))):
        emp = coverage_dist(sc, starts, sizes, level, "CLUSTER", rng, reps=REPS)
        iid = coverage_dist(sc, starts, sizes, level, "IID", rng, reps=REPS)

        neff_matched = neff_matching_var(float(emp.var(ddof=1)), level)
        laws = {"naive": beta_for(float(n), level),
                "plugin": beta_for(PLUGIN_NEFF, level),
                "matched": beta_for(neff_matched, level)}

        print("\n" + "-" * 78)
        print(f"ARM: {arm_name}    distinct coverage values in sample: {len(np.unique(emp))}")
        print("-" * 78)
        print(f"  empirical   mean {emp.mean():.5f}   sd {emp.std(ddof=1):.5f}   "
              f"skew {skew(emp):+.3f}")
        print(f"  n_eff implied by the measured variance: {neff_matched:.0f}   "
              f"(plug-in says {PLUGIN_NEFF:.0f}, nominal n = {n})")

        cmp_emp = compare(emp, laws)
        print(f"\n  {'law':>9}  {'n_eff':>8}  {'law sd':>9}  {'law skew':>9}  {'KS D':>8}")
        for nm, ne in (("naive", float(n)), ("plugin", PLUGIN_NEFF),
                       ("matched", neff_matched)):
            c = cmp_emp[nm]
            print(f"  {nm:>9}  {ne:>8.0f}  {c['law_sd']:>9.5f}  {c['law_skew']:>+9.3f}  "
                  f"{c['ks_D']:>8.4f}")

        # POSITIVE CONTROL. The iid arm is generated by resampling i.i.d. from the pool, so it
        # MUST be well described by the Beta at (approximately) nominal n. If it is not, the
        # comparison machinery is broken and nothing in the CLUSTER row above is readable.
        ks_iid = float(kstest(iid, laws["naive"].cdf).statistic)
        neff_iid = neff_matching_var(float(iid.var(ddof=1)), level)
        print(f"\n  POSITIVE CONTROL — iid arm vs Beta at nominal n: KS D = {ks_iid:.4f}, "
              f"implied n_eff = {neff_iid:.0f} (want ~{n})")

        result["arms"][arm_name] = {
            "empirical": {"mean": float(emp.mean()), "sd": float(emp.std(ddof=1)),
                          "skew": float(skew(emp)), "n_distinct": int(len(np.unique(emp))),
                          "neff_matched": neff_matched},
            "laws": cmp_emp,
            "positive_control": {"ks_D_iid_vs_naive": ks_iid, "neff_iid": neff_iid,
                                 "ratio_to_nominal": neff_iid / n},
        }

    print("\n" + "=" * 78)
    print("PRECONDITIONS — each could have come out wrong")
    print("=" * 78)

    tb = result["arms"]["tiebroken"]
    p1 = 0.5 <= tb["positive_control"]["ratio_to_nominal"] <= 2.0
    print(f"  P1  iid arm recovers nominal n within 2x "
          f"(implied {tb['positive_control']['neff_iid']:.0f} vs {n}) -> "
          f"{'PASS' if p1 else 'FAIL'}")
    print("      would fail if: the resampler, the varying resampled n, or the Beta")
    print("      parameterisation were wrong. Nothing below is readable without it.")

    d_naive = tb["laws"]["naive"]["ks_D"]
    d_matched = tb["laws"]["matched"]["ks_D"]
    p2 = d_naive > 3 * d_matched
    print(f"  P2  the naive law is decisively worse than the matched one "
          f"(D {d_naive:.4f} vs {d_matched:.4f}) -> {'PASS' if p2 else 'FAIL'}")
    print("      would fail if: the comparison has no power at this sample size, in which")
    print("      case a small D for `matched` is not evidence the shape survives.")

    ok = p1 and p2
    result["preconditions"] = {"p1_iid_recovers_nominal": bool(p1),
                               "p2_naive_rejected": bool(p2)}
    result["verdict"] = {
        "ks_D_matched_tiebroken": d_matched,
        "shape_survives": bool(d_matched < 0.05),
        "note": "relative comparison across laws on one bootstrap sample; not a hypothesis test",
    }

    print("\n" + "=" * 78)
    if not ok:
        print("  A PRECONDITION FAILED — the verdict below may not be quoted.")
    print(f"  Tie-broken arm, shape-only distance for Beta at the MEASURED n_eff: "
          f"D = {d_matched:.4f}")
    print(f"  -> {'shape survives' if d_matched < 0.05 else 'SHAPE DOES NOT SURVIVE'} "
          f"at the 0.05 threshold registered in PREREG.md")
    print("=" * 78)

    out = Path(__file__).resolve().parent / "result_ec01.json"
    out.write_text(json.dumps(result, indent=2))
    print(f"\nwrote {out.name}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
