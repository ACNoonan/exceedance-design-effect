"""SW-02 — simulation validation of the general-rho coverage theorem.

Division of labour: the derivation is handled elsewhere. This is the empirical side.

The theorem (asymptotic form):

    sqrt(n) (C - p)  ->  N(0, p(1-p)[1 + (m-1) rho_I(p)])
    rho_I(p) = (delta(p) - p^2) / (p(1-p)),   delta(p) = P(X_1 <= q_p, X_2 <= q_p) same cluster

Its boldest claim is **distribution-freeness given the copula diagonal**: the coverage law depends
on the score distribution ONLY through delta(p). Two wildly different dependence structures with
the same delta(p) must produce the same coverage law, and the marginal must not matter at all.

That is a claim simulation can attack directly, so this file attacks it.

Test 1 — MATCHED-DELTA. Gaussian, t(3) and Clayton copulas, each tuned to the SAME delta(p),
         crossed with Gaussian and Exponential marginals. Six configurations, one prediction.
         RESULT: sd agrees to within 1.94% across all six, and within 1.2% of prediction.
         Caveat on reading it: the MARGINAL axis is tautological here and is a code check, not
         evidence — x <= q_p iff u <= p under any monotone marginal, so the two marginal columns
         are bit-identical by construction. The real test is the COPULA axis, and it passes.

Test 2 — MEAN DRIFT vs b.  ** VOID AS WRITTEN — DO NOT READ THE NUMBERS. **
         This simulates C = p + (p - F_hat(q_p)), which is the LINEARIZATION, and E[F_hat(q_p)] = p
         exactly, so its mean is p by construction and the measured "drift" is pure Monte Carlo
         noise (all values sit at or below one standard error). The real drift is precisely the
         Bahadur remainder — the gap between F(s_hat_(k)) and its linearization — which is exactly
         where the derivation says it lives, and which this estimator cannot see because it never
         forms the order statistic.
         Measuring it needs the true C = F(s_hat_(k)), i.e. `calkit.conformal.split_conformal`.
         Blocked on L2. Left in place, clearly labelled, because the failed test is informative:
         it localises the drift to the quantile-estimation step rather than to the dependence.

NOTE ON SCOPE: this deliberately simulates F_hat(q_p) rather than running split conformal, because
step 4 of the derivation gives C = p + (p - F_hat(q_p)) + o_P(n^-1/2). Testing F_hat isolates the
theorem's variance claim from the order-statistic discreteness that contaminates the endpoints
(see DRAFT.md 5.1). The end-to-end conformal version runs once `calkit.conformal.split_conformal`
is implemented — it is L2's typed line and is deliberately not written out here.
"""

from __future__ import annotations

import numpy as np
from scipy.optimize import brentq
from scipy.stats import expon, norm, t as student_t
from scipy.stats import multivariate_normal as mvn

P = 0.90
M = 4          # cluster size
B = 50         # clusters
N = B * M
REPS = 20_000
SEED = 0


# ---------- copulas, each exchangeable in m dimensions ----------

def delta_gauss(r: float) -> float:
    z = norm.ppf(P)
    return float(mvn(mean=[0, 0], cov=[[1, r], [r, 1]]).cdf([z, z]))


def delta_t(r: float, df: int = 3) -> float:
    """P(U1<=p, U2<=p) for a bivariate t copula — Monte Carlo, it has no simple closed form."""
    rng = np.random.default_rng(12345)
    n = 400_000
    L = np.linalg.cholesky([[1, r], [r, 1]])
    z = rng.normal(size=(n, 2)) @ L.T
    w = rng.chisquare(df, size=(n, 1)) / df
    u = student_t.cdf(z / np.sqrt(w), df)
    return float(np.mean((u[:, 0] <= P) & (u[:, 1] <= P)))


def delta_clayton(theta: float) -> float:
    """Clayton: C(u,v) = (u^-t + v^-t - 1)^(-1/t). Closed form on the diagonal."""
    return float((2 * P ** (-theta) - 1) ** (-1 / theta))


def sample_gauss(rng, b, m, r):
    cov = np.full((m, m), r); np.fill_diagonal(cov, 1.0)
    z = rng.multivariate_normal(np.zeros(m), cov, size=b)
    return norm.cdf(z)


def sample_t(rng, b, m, r, df=3):
    cov = np.full((m, m), r); np.fill_diagonal(cov, 1.0)
    z = rng.multivariate_normal(np.zeros(m), cov, size=b)
    w = rng.chisquare(df, size=(b, 1)) / df
    return student_t.cdf(z / np.sqrt(w), df)


def sample_clayton(rng, b, m, theta):
    """Marshall-Olkin frailty construction — exchangeable in any dimension."""
    w = rng.gamma(shape=1.0 / theta, scale=1.0, size=(b, 1))
    v = rng.uniform(size=(b, m))
    return (1.0 - np.log(v) / w) ** (-1.0 / theta)


MARGINALS = {"gauss": norm.ppf, "expon": expon.ppf}


def run(sampler, args, marginal, b=B, m=M, reps=REPS, seed=SEED):
    """Simulate F_hat(q_p) and return the induced coverage C = p + (p - F_hat(q_p))."""
    rng = np.random.default_rng(seed)
    ppf = MARGINALS[marginal]
    q_p = ppf(P)
    out = np.empty(reps)
    for i in range(reps):
        u = sampler(rng, b, m, *args)
        x = ppf(np.clip(u, 1e-12, 1 - 1e-12))
        out[i] = P + (P - np.mean(x <= q_p))
    return out


def main() -> int:
    target_rho_I = 0.5
    target_delta = P * P + target_rho_I * P * (1 - P)
    print(f"p={P}, m={M}, b={B}, n={N}, reps={REPS}")
    print(f"TARGET delta(p) = {target_delta:.6f}  ->  rho_I = {target_rho_I}\n")

    r_g = brentq(lambda r: delta_gauss(r) - target_delta, 1e-6, 0.999)
    th_c = brentq(lambda t: delta_clayton(t) - target_delta, 1e-4, 60)
    r_t = brentq(lambda r: delta_t(r) - target_delta, -0.5, 0.999, xtol=1e-4)
    print(f"tuned:  gaussian r={r_g:.4f}   clayton theta={th_c:.4f}   t(3) r={r_t:.4f}")
    print(f"check:  delta_g={delta_gauss(r_g):.6f}  delta_c={delta_clayton(th_c):.6f}  "
          f"delta_t={delta_t(r_t):.6f}\n")

    n_eff = N / (1 + (M - 1) * target_rho_I)
    sd_pred = np.sqrt(P * (1 - P) / n_eff)
    print(f"THEOREM PREDICTS, for all six configurations:  n_eff={n_eff:.1f}  sd={sd_pred:.5f}\n")

    print("TEST 1 — matched-delta distribution-freeness")
    print(f"{'copula':>9} {'marginal':>9} {'mean':>9} {'sd':>9} {'sd/pred':>9}")
    configs = [("gauss", sample_gauss, (r_g,)), ("t(3)", sample_t, (r_t,)),
               ("clayton", sample_clayton, (th_c,))]
    sds = []
    for name, fn, args in configs:
        for marg in MARGINALS:
            c = run(fn, args, marg)
            sds.append(c.std())
            print(f"{name:>9} {marg:>9} {c.mean():>9.5f} {c.std():>9.5f} "
                  f"{c.std()/sd_pred:>9.3f}")
    spread = (max(sds) - min(sds)) / np.mean(sds)
    print(f"\n  spread across all six: {spread*100:.2f}% of mean sd  "
          f"-> {'CONSISTENT with distribution-freeness' if spread < 0.05 else 'INCONSISTENT'}")

    print("\nTEST 2 — mean drift vs number of clusters  ** VOID AS WRITTEN, see module docstring **")
    print(f"{'b':>5} {'n':>6} {'mean':>9} {'drift':>10} {'drift*b':>9}")
    for b in (25, 50, 100, 200, 400):
        c = run(sample_gauss, (r_g,), "gauss", b=b, reps=max(REPS // 2, 5000))
        drift = c.mean() - P
        print(f"{b:>5} {b*M:>6} {c.mean():>9.5f} {drift:>+10.5f} {drift*b:>+9.4f}")
    print("  These numbers are Monte Carlo noise around an estimator whose mean is p by")
    print("  construction. They are NOT evidence of an O(1/b) drift. Blocked on L2.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
