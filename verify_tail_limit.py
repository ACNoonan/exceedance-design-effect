"""Gate A1 (ROADMAP Phase 0): numeric check of the tail-limit proposition.

Claim:  lim_{p->1} rho_I(p) = lambda_U   (upper tail-dependence coefficient)
        lim_{p->0} rho_I(p) = lambda_L   (lower tail-dependence coefficient)

with rho_I(p) = (C(p,p) - p^2) / (p(1-p)),  C the copula of two same-cluster scores.

Algebraic route used for the upper end: with S(p) = P(both above the p-quantile),
S(p) = (1-p)^2 + (C(p,p) - p^2), hence

    S(p)/(1-p) = (1-p) + p * rho_I(p)  ->  lambda_U.

Three copulas, three analytic targets:
  1. Gaussian (rho=0.6): tail-independent, lambda_U = 0. rho_I(p) must decay to 0
     (theory: regularly varying with exponent (1-rho)/(1+rho) = 0.25).
  2. Student-t (nu=3, rho=0.6): lambda_U = 2 * T_{nu+1}(-sqrt((nu+1)(1-rho)/(1+rho))).
  3. Clayton (theta=2), lower end: C(u,u) = (2 u^{-theta} - 1)^{-1/theta},
     lambda_L = 2^{-1/theta}. Closed form, no integration.

S(p) is computed by 1-D quadrature of the conditional survival (no Monte Carlo:
we need relative precision at 1-p = 1e-10). Cross-checks at moderate p against
scipy's bivariate normal CDF and the Corollary 2 closed form.

PASS = all three convergences hold (criteria printed at the bottom).
"""

import numpy as np
from scipy import integrate
from scipy.stats import norm, t as tdist, multivariate_normal

RHO = 0.6
NU = 3
THETA = 2.0

# levels approaching 1 (upper-tail checks)
EPS = np.array([1e-1, 1e-2, 1e-3, 1e-4, 1e-6, 1e-8, 1e-10])


def survival_gaussian(p, rho=RHO):
    """S(p) = P(X1 > z_p, X2 > z_p) for bivariate normal, corr rho."""
    zp = norm.ppf(p)
    denom = np.sqrt(1.0 - rho * rho)

    def integrand(u):
        x = zp + u
        return norm.pdf(x) * norm.sf((zp - rho * x) / denom)

    val, err = integrate.quad(integrand, 0.0, np.inf, epsabs=0, epsrel=1e-11, limit=400)
    return val, err


def survival_t(p, rho=RHO, nu=NU):
    """S(p) = P(T1 > t_p, T2 > t_p) for bivariate t (nu, corr rho).

    T2 | T1 = x  ~  rho*x + sqrt((1-rho^2)(nu+x^2)/(nu+1)) * t_{nu+1}.
    """
    tp = tdist.ppf(p, nu)

    def integrand(u):
        x = tp + u
        scale = np.sqrt((1.0 - rho * rho) * (nu + x * x) / (nu + 1.0))
        return tdist.pdf(x, nu) * tdist.sf((tp - rho * x) / scale, nu + 1)

    val, err = integrate.quad(integrand, 0.0, np.inf, epsabs=0, epsrel=1e-11, limit=400)
    return val, err


def rho_I_from_survival(p, S):
    return (S / (1.0 - p) - (1.0 - p)) / p


def rho_I_clayton_lower(u, theta=THETA):
    """rho_I(u) with C(u,u) = (2 u^-theta - 1)^(-1/theta), exact."""
    C = (2.0 * u ** (-theta) - 1.0) ** (-1.0 / theta)
    return (C - u * u) / (u * (1.0 - u))


def main():
    ok = True

    # ---- cross-checks at moderate p: quadrature vs mvn CDF vs Corollary 2 ----
    print("== Cross-check (Gaussian, p in {0.9, 0.99}): survival-quad vs Phi2 diagonal ==")
    cov = [[1.0, RHO], [RHO, 1.0]]
    for p in (0.9, 0.99):
        zp = norm.ppf(p)
        C_mvn = multivariate_normal(mean=[0, 0], cov=cov).cdf([zp, zp])
        rho_I_cor2 = (C_mvn - p * p) / (p * (1 - p))          # Corollary 2 form
        S, _ = survival_gaussian(p)
        rho_I_quad = rho_I_from_survival(p, S)
        d = abs(rho_I_cor2 - rho_I_quad)
        print(f"  p={p}:  rho_I[Phi2]={rho_I_cor2:.8f}  rho_I[quad]={rho_I_quad:.8f}  |diff|={d:.2e}")
        if d > 1e-6:
            ok = False
            print("  ** cross-check FAILED (>1e-6)")

    # ---- 1. Gaussian upper tail: rho_I -> 0, strictly decreasing ----
    print("\n== Gaussian copula (rho=0.6): claim rho_I(p) -> lambda_U = 0 ==")
    vals = []
    for eps in EPS:
        p = 1.0 - eps
        S, _ = survival_gaussian(p)
        r = rho_I_from_survival(p, S)
        vals.append(r)
        # empirical decay exponent vs theory (1-rho)/(1+rho) = 0.25
        print(f"  1-p={eps:.0e}   rho_I={r: .6e}")
    vals = np.array(vals)
    mono = np.all(np.diff(vals) < 0)
    final_small = vals[-1] < 0.05
    slope = np.polyfit(np.log(EPS[2:]), np.log(vals[2:]), 1)[0]
    print(f"  strictly decreasing: {mono};  rho_I at 1-p=1e-10: {vals[-1]:.3e} (<0.05: {final_small})")
    print(f"  empirical decay exponent {slope:.4f}  vs theory (1-rho)/(1+rho) = {(1-RHO)/(1+RHO):.4f}")
    if not (mono and final_small):
        ok = False
        print("  ** Gaussian gate FAILED")

    # ---- 2. t copula upper tail: rho_I -> lambda_U > 0 ----
    lam_U = 2.0 * tdist.cdf(-np.sqrt((NU + 1.0) * (1.0 - RHO) / (1.0 + RHO)), NU + 1)
    print(f"\n== t copula (nu=3, rho=0.6): claim rho_I(p) -> lambda_U = {lam_U:.6f} ==")
    gaps = []
    for eps in EPS:
        p = 1.0 - eps
        S, _ = survival_t(p)
        r = rho_I_from_survival(p, S)
        gaps.append(abs(r - lam_U))
        print(f"  1-p={eps:.0e}   rho_I={r:.6f}   |rho_I - lambda_U|={gaps[-1]:.2e}")
    gaps = np.array(gaps)
    shrink = np.all(np.diff(gaps) < 0)
    final_close = gaps[-1] < 5e-3
    print(f"  gap strictly shrinking: {shrink};  final gap {gaps[-1]:.2e} (<5e-3: {final_close})")
    if not (shrink and final_close):
        ok = False
        print("  ** t-copula gate FAILED")

    # ---- 2b. Atom mixture (prob q identical scores, else independent):
    #          C(t,t) = q*t + (1-q)*t^2  =>  rho_I(p) = q at EVERY level (no attenuation),
    #          and lambda_U = q. The "ties/atoms => tail-dependent" claim, exact. ----
    q_atom = 0.3
    print(f"\n== Atom mixture (q={q_atom}): claim rho_I(p) = q identically, lambda_U = q ==")
    worst = 0.0
    for p in (0.5, 0.9, 0.99, 1 - 1e-6, 1 - 1e-10):
        C = q_atom * p + (1 - q_atom) * p * p
        r = (C - p * p) / (p * (1 - p))
        worst = max(worst, abs(r - q_atom))
        print(f"  p={p}:   rho_I={r:.15f}")
    # tolerance 1e-8: evaluating (C - p^2)/(p(1-p)) at p = 1-1e-10 cancels ~10 digits;
    # the residual is float artifact, not math (the identity rho_I = q is exact algebra)
    print(f"  max |rho_I - q| = {worst:.2e}")
    if worst > 1e-8:
        ok = False
        print("  ** atom-mixture gate FAILED")

    # ---- 3. Clayton lower tail: rho_I -> lambda_L = 2^{-1/theta}, exact ----
    lam_L = 2.0 ** (-1.0 / THETA)
    print(f"\n== Clayton copula (theta=2), lower end: claim rho_I(u) -> lambda_L = {lam_L:.6f} ==")
    final_gap = None
    for u in (1e-3, 1e-6, 1e-9, 1e-12):
        r = rho_I_clayton_lower(u)
        final_gap = abs(r - lam_L)
        print(f"  u={u:.0e}   rho_I={r:.12f}   |rho_I - lambda_L|={final_gap:.2e}")
    if final_gap > 1e-6:
        ok = False
        print("  ** Clayton gate FAILED")

    print("\n" + ("GATE A1: PASS — proposition enters the paper."
                  if ok else "GATE A1: FAIL — proposition stays out; investigate."))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
