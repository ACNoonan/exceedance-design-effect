"""§5 states a LIMIT. An extreme-value reader asks about the RATE.

§5's Proposition 3 gives rho_I(p) -> lambda_U, and illustrates with a t-copula
(nu=3, rho=0.6, lambda_U=0.374) reaching it "to within 1e-7 by 1-p = 1e-10".
No conformal application operates at 1-p = 1e-10. Operating levels are
1-p in [0.001, 0.1]. So the question §5 does not answer is whether the limit is
a useful guide THERE, or an asymptote the practitioner never approaches.

If rho_I(0.99) sits close to lambda_U the "floor" language is sound. If it is
far above, the floor is real but not yet felt, and §5's comfort ("tail-dependent
families have a floor") overstates what a practitioner at 99% coverage sees.

REWRITTEN 2026-07-31 -- THE ORIGINAL SHIPPED WITH TWO DEFECTS, BOTH FIXED HERE.

  (1) IT WAS NOT DETERMINISTIC.  It computed the copula diagonal with
      `scipy.stats.multivariate_t.cdf`, which is a RANDOMISED quadrature.  Two
      consecutive runs returned rho_I(0.99) = 0.4000 and 0.3878; at p = 0.9999,
      +1.2799 and -0.9173.  §12 records this script under "each script fixes a
      seed at module scope where it uses randomness" and the archive manifest
      marks its seed cell `n/a` -- a determination made by opening the file,
      since `multivariate_t.cdf` does not look random.  The saturation half of
      this was already caught and written up in integrity.md SW-54 ("returns
      rho_I = 2.0, which is impossible for a correlation"); the NON-DETERMINISM
      is a separate defect and was not.

      Why it is fatal here and not elsewhere: rho_I = [C(p,p) - p^2]/[p(1-p)]
      divides by p(1-p), so error in the diagonal is amplified 101x at p = 0.99
      and 1000x at p = 0.999.  A routine accurate to ~1e-3 in C is useless for
      rho_I in the tail, and near p = 1 the subtraction C - p^2 cancels
      catastrophically on top of that.

  (2) P2 TESTED THE WRONG DIRECTION.  It asserted rho_I approaches lambda_U
      "from below" and checked for a monotone INCREASING sequence.  §5.1's own
      prose says "approaching from above", and that is what is true.  P2 would
      therefore have failed against a perfect integrator.

THE FIX is to stop having a second instrument.  `verify_tail_limit.py` already
solves this correctly -- conditional-survival quadrature at epsrel = 1e-11, so
the small number is computed AS a small number and never as a difference of two
numbers near 1 -- and §5.1 cites it for the same limits.  This script now
imports it rather than reimplementing it.  SW-54's own note said "the paper's
own verify_tail_limit.py already avoids this"; the remaining error was that
this file did not use it.

PRECONDITIONS (each can come out wrong):
  P0  DETERMINISM.  Repeated calls must be bit-identical.  This is the check
      whose absence let the original ship.  WOULD HAVE FAILED IF: the diagonal
      were computed by any randomised or Monte Carlo routine.
  P1  lambda_U from the closed form must equal 2*t_{nu+1}(-sqrt((nu+1)(1-r)/(1+r)))
      = 0.374 at nu=3, r=0.6 -- the number §5 prints.
  P2  rho_I(p) must approach lambda_U from ABOVE, monotonically decreasing, and
      converge: at 1-p = 1e-10 it must agree with lambda_U to ~1e-6, which is
      §5's own claim and a check on the integrator.
  P3  NEGATIVE CONTROL: a GAUSSIAN copula at the same Kendall tau must send
      rho_I -> 0, not to a positive floor. If both go to a floor the integrator
      is not seeing tail dependence at all.
  P4  THE INTEGRATOR'S OWN ERROR, amplified by 1/(p(1-p)), must stay far below
      the gap being reported. A quadrature whose error exceeds the quantity is
      the defect this rewrite exists to remove, so it is asserted rather than
      assumed.
"""
import numpy as np
from scipy import stats

# The paper's validated instrument. Importing rather than reimplementing is the
# point of the 2026-07-31 rewrite -- see the header.
from verify_tail_limit import (
    survival_t,
    survival_gaussian,
    rho_I_from_survival,
)

NU, R = 3, 0.6
EXPS = (1, 2, 3, 4, 6, 10)


def lambda_U_t(nu=NU, r=R):
    return 2.0 * stats.t.cdf(-np.sqrt((nu + 1) * (1 - r) / (1 + r)), df=nu + 1)


def rho_I_t(p, rho=R, nu=NU):
    S, _err = survival_t(p, rho=rho, nu=nu)
    return rho_I_from_survival(p, S)


def main():
    ok = True
    lam = lambda_U_t()
    print("=" * 74)
    print(f"t-copula  nu={NU}, rho={R}   lambda_U = {lam:.4f}")
    print("=" * 74)

    # P0 -- determinism. The check whose absence let the original ship.
    a = [rho_I_t(0.99) for _ in range(3)]
    det = (a[0] == a[1] == a[2])
    ok &= det
    print(f"  P0  deterministic across repeat calls                : "
          f"{'PASS' if det else 'FAIL'}  ({a[0]:.12f})")
    print("      would have failed on the randomised multivariate_t.cdf this replaces")

    # P1 -- closed form matches §5's printed figure
    p1 = abs(lam - 0.374) < 0.002
    ok &= p1
    print(f"  P1  closed-form lambda_U matches §5's printed 0.374  : {'PASS' if p1 else 'FAIL'}")

    # the table
    print()
    print(f"  {'1-p':>10} {'p':>14} {'rho_I(p)':>10} {'/lambda_U':>10} {'gap':>10}")
    rows = []
    for e in EXPS:
        p = 1 - 10.0 ** (-e)
        r_i = rho_I_t(p)
        rows.append((e, p, r_i))
        print(f"  {10.0**-e:>10.0e} {p:>14.10f} {r_i:>10.4f} {r_i/lam:>10.3f} {r_i-lam:>10.2e}")

    # P2 -- monotone DECREASING, approaching from ABOVE, and converged
    mono = all(rows[i][2] >= rows[i + 1][2] - 1e-9 for i in range(len(rows) - 1))
    above = all(r >= lam - 1e-9 for _, _, r in rows)
    conv = abs(rows[-1][2] - lam) < 1e-5
    p2 = mono and above and conv
    ok &= p2
    print()
    print(f"  P2  decreasing, from ABOVE, converged at 1-p=1e-10   : {'PASS' if p2 else 'FAIL'}")
    print(f"      (decreasing={mono}, from-above={above}, |gap|={abs(rows[-1][2]-lam):.2e})")
    print("      the original asserted the opposite direction and would have failed here")

    # P3 -- Gaussian negative control at matched Kendall tau
    tau = 2 / np.pi * np.arcsin(R)
    r_g = float(np.sin(np.pi * tau / 2))
    g = []
    for e in (1, 2, 3, 4):
        p = 1 - 10.0 ** (-e)
        S, _ = survival_gaussian(p, rho=r_g)
        g.append(rho_I_from_survival(p, S))
    p3 = g[-1] < g[0] / 2
    ok &= p3
    print(f"  P3  NEG CTRL Gaussian (matched tau, r={r_g:.3f}) rho_I: "
          f"{', '.join(f'{x:.4f}' for x in g)} -> 0 : {'PASS' if p3 else 'FAIL'}")

    # P4 -- integrator error, AMPLIFIED, must be far below the reported gap
    print()
    worst = 0.0
    for e in EXPS:
        p = 1 - 10.0 ** (-e)
        _S, err = survival_t(p)
        worst = max(worst, err / ((1.0 - p) * p))     # error propagated into rho_I
    smallest_gap = min(abs(r - lam) for _, _, r in rows[:4])
    p4 = worst < 0.01 * smallest_gap
    ok &= p4
    print(f"  P4  amplified quadrature error {worst:.2e} << smallest reported gap "
          f"{smallest_gap:.2e} : {'PASS' if p4 else 'FAIL'}")
    print("      1/(p(1-p)) reaches 1e10 at 1-p=1e-10; this asserts the integrator survives it")

    print()
    print("  READING")
    for e, p, r_i in rows[:4]:
        print(f"    at {100*p:.4g}% coverage rho_I = {r_i:.4f}, "
              f"which is {100*r_i/lam:.0f}% of the floor "
              f"({100*(r_i-lam)/lam:+.0f}% above it)")
    print()
    print("  §5.1 reports the first two of these. Values at 1-p <= 1e-3 are printed")
    print("  for the convergence check only and are not quoted in the paper.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
