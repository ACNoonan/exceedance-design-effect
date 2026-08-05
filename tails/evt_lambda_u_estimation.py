"""Can a practitioner estimate their own tail-dependence floor lambda_U?

SW-54's open half. Section 5 tells a reader their design effect has a floor at
lambda_U and never says how lambda_U would be estimated from data. This runs the
estimators Frahm, Junker & Schmidt (2005) survey, at OUR sample sizes, against a
copula whose lambda_U we know in closed form.

Estimators, verbatim from Frahm/Junker/Schmidt, "Estimating the tail-dependence
coefficient: properties and pitfalls", Insurance: Math. & Econ. 37 (2005) 80-100:

  eq (11)  lambda_SEC(k) = 2 - [1 - C_n((n-k)/n, (n-k)/n)] / [1 - (n-k)/n]
  sec 3.5  lambda_CFG    = 2 - 2 exp{ (1/n) sum log[ sqrt(log(1/U_i) log(1/V_i))
                                                     / log(1/max(U_i,V_i)^2) ] }
  sec 4.4  the plateau-finding algorithm that picks k for lambda_SEC.

The unit of observation is ONE PAIR PER CLUSTER, so n = b. That is the
conservative reading: pairs drawn within a cluster are not independent of each
other, so b independent pairs is what a practitioner can be sure they have.

No Monte Carlo shortcuts on the truth: lambda_U comes from Frahm eq (8).
"""

import numpy as np
from scipy import stats

SEED = 20260730
ALPHA = 3          # t_3 copula, as illustrated in section 5
RHO = 0.6          # section 5's correlation parameter
N_REP = 400


# ---------------------------------------------------------------- truth

def lambda_u_t(alpha, rho):
    """Frahm et al. eq (8): lambda = 2 * tbar_{alpha+1}( sqrt((alpha+1)(1-rho)/(1+rho)) )."""
    arg = np.sqrt((alpha + 1) * (1 - rho) / (1 + rho))
    return 2 * stats.t.sf(arg, df=alpha + 1)


def lambda_u_gumbel(theta):
    """lambda_U = 2 - 2^(1/theta)."""
    return 2 - 2 ** (1 / theta)


# ---------------------------------------------------------------- samplers

def sample_t_copula(n, alpha, rho, rng):
    cov = np.array([[1.0, rho], [rho, 1.0]])
    z = rng.multivariate_normal(np.zeros(2), cov, size=n)
    w = rng.chisquare(alpha, size=n) / alpha
    return z / np.sqrt(w)[:, None]


def sample_gaussian_copula(n, rho, rng):
    cov = np.array([[1.0, rho], [rho, 1.0]])
    return rng.multivariate_normal(np.zeros(2), cov, size=n)


def sample_independent(n, rng):
    return rng.normal(size=(n, 2))


def sample_gumbel_copula(n, theta, rng):
    """Marshall-Olkin with a positive-stable(1/theta) frailty.

    V ~ positive stable with Laplace transform exp(-t^a), a = 1/theta, sampled by
    Chambers-Mallows-Stuck; then U_j = exp(-(E_j/V)^a), E_j iid Exp(1).
    Validated by Kendall's tau = 1 - 1/theta (precondition P0).
    """
    a = 1.0 / theta
    phi = rng.uniform(0, np.pi, size=n)
    w = rng.exponential(size=n)
    v = (np.sin((1 - a) * phi) / w) ** ((1 - a) / a) * \
        np.sin(a * phi) / np.sin(phi) ** (1 / a)
    e = rng.exponential(size=(n, 2))
    return np.exp(-(e / v[:, None]) ** a)


# ---------------------------------------------------------------- estimators

def pseudo_obs(x):
    """Ranks scaled to (0,1) — the empirical copula's margins."""
    n = x.shape[0]
    return np.column_stack([stats.rankdata(x[:, j]) / (n + 1) for j in range(x.shape[1])])


def lambda_sec_curve(u):
    """eq (11) evaluated at every threshold k = 1..n-1.

    The copula's DIAGONAL only needs the componentwise max: both coordinates are
    <= t exactly when max(U_i, V_i) <= t. So one sort replaces an O(n^2) sweep.
    """
    n = u.shape[0]
    k = np.arange(1, n)
    t = (n - k) / n
    mx = np.sort(np.maximum(u[:, 0], u[:, 1]))
    both = np.searchsorted(mx, t, side="right") / n      # C_n(t, t)
    return k, 2 - (1 - both) / (1 - t)


def plateau_estimate(lam):
    """Frahm et al. section 4.4, exactly as specified.

    b = floor(0.005 n); box kernel over 2b+1; plateau length m = floor(sqrt(n-2b));
    stop at first k with sum_{i=k+1}^{k+m-1} |lam_i - lam_k| <= 2 sigma;
    estimate = mean of that plateau. No plateau -> 0.
    """
    n = len(lam)
    b = int(np.floor(0.005 * n))
    if b < 1:
        b = 1
    kern = np.ones(2 * b + 1) / (2 * b + 1)
    sm = np.convolve(lam, kern, mode="valid")          # length n - 2b
    m = int(np.floor(np.sqrt(len(sm))))
    sigma = np.std(sm)
    for k in range(len(sm) - m + 1):
        block = sm[k:k + m]
        if np.sum(np.abs(block[1:] - block[0])) <= 2 * sigma:
            return float(np.mean(block))
    return 0.0


def lambda_cfg(u):
    """Frahm et al. section 3.5, the Caperaa-Fougeres-Genest form."""
    U, V = u[:, 0], u[:, 1]
    num = np.sqrt(np.log(1 / U) * np.log(1 / V))
    den = np.log(1 / np.maximum(U, V) ** 2)
    return 2 - 2 * np.exp(np.mean(np.log(num / den)))


# ---------------------------------------------------------------- preconditions

def preconditions():
    """Three checks, each of which could have come out wrong."""
    rng = np.random.default_rng(SEED)
    out = []

    # P1 -- the analytic truth must reproduce section 5's printed 0.374.
    lam = lambda_u_t(ALPHA, RHO)
    out.append(("P1 analytic lambda_U(t_3, rho=0.6) == section 5's 0.374",
                abs(lam - 0.374) < 5e-4,
                f"got {lam:.6f}; would have failed if section 5's number came from a "
                f"different formula than Frahm eq (8)"))

    # P0 -- the Gumbel sampler itself, before it is used as a control.
    #       (The first version of this script failed here: tau 0.4675 vs 0.5556.)
    tau = stats.kendalltau(*sample_gumbel_copula(20000, 2.25, rng).T).statistic
    out.append(("P0 Gumbel(2.25) sampler has Kendall tau = 1 - 1/theta = 0.5556",
                abs(tau - (1 - 1 / 2.25)) < 0.01,
                f"got {tau:.4f}; separates a broken sampler from a broken estimator"))

    # P2 -- CFG must recover a DIFFERENT known copula's lambda_U. Gumbel IS an EV
    #       copula, so this tests the transcription where CFG's assumption holds.
    truth_g = lambda_u_gumbel(2.25)
    ests = [lambda_cfg(pseudo_obs(sample_gumbel_copula(5000, 2.25, rng)))
            for _ in range(20)]
    ok = abs(np.mean(ests) - truth_g) < 0.03
    out.append((f"P2 CFG recovers Gumbel(2.25) lambda_U={truth_g:.3f} at n=5000",
                ok,
                f"got {np.mean(ests):.4f}; would have failed if the transcribed "
                f"formula were wrong or estimated the lower tail"))

    # P2b -- and the endpoints, where every estimator must be exact.
    x = rng.normal(size=20000)
    lam_com = lambda_cfg(pseudo_obs(np.column_stack([x, x])))
    out.append(("P2b CFG is exact at the endpoints (comonotone lambda_U = 1)",
                abs(lam_com - 1.0) < 1e-6,
                f"got {lam_com:.6f}"))

    # P3 -- both estimators must return ~0 under independence.
    lam_c, lam_s = [], []
    for _ in range(20):
        x = sample_independent(2000, rng)
        u = pseudo_obs(x)
        lam_c.append(lambda_cfg(u))
        _, curve = lambda_sec_curve(u)
        lam_s.append(plateau_estimate(curve))
    ok = abs(np.mean(lam_c)) < 0.05 and abs(np.mean(lam_s)) < 0.10
    out.append(("P3 both estimators ~0 under independence (lambda_U = 0)",
                ok,
                f"CFG {np.mean(lam_c):.4f}, SEC+plateau {np.mean(lam_s):.4f}; would "
                f"have failed if either manufactured tail dependence from noise"))
    return out


# ---------------------------------------------------------------- measurement

def run(n, sampler, truth, rng, n_rep=N_REP):
    cfg, sec = [], []
    for _ in range(n_rep):
        u = pseudo_obs(sampler(n, rng))
        cfg.append(lambda_cfg(u))
        _, curve = lambda_sec_curve(u)
        sec.append(plateau_estimate(curve))
    cfg, sec = np.array(cfg), np.array(sec)
    return {
        "n": n, "truth": truth,
        "cfg_mean": cfg.mean(), "cfg_sd": cfg.std(),
        "cfg_rmse": np.sqrt(np.mean((cfg - truth) ** 2)),
        "sec_mean": sec.mean(), "sec_sd": sec.std(),
        "sec_rmse": np.sqrt(np.mean((sec - truth) ** 2)),
        "cfg_raw": cfg, "sec_raw": sec,
    }


if __name__ == "__main__":
    print("PRECONDITIONS")
    for name, ok, detail in preconditions():
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}\n         {detail}")
        if not ok:
            raise SystemExit("precondition failed -- no measurement reported")

    truth = lambda_u_t(ALPHA, RHO)
    rng = np.random.default_rng(SEED + 1)

    print(f"\nTAIL-DEPENDENT CASE: t_{ALPHA} copula, rho={RHO}, true lambda_U = {truth:.4f}")
    print(f"{'n (=b)':>8} {'CFG mean':>10} {'CFG sd':>8} {'CFG rmse':>9} "
          f"{'SEC mean':>10} {'SEC sd':>8} {'SEC rmse':>9}")
    dep = {}
    for n in (250, 500, 1000, 5000):
        r = run(n, lambda k, g: sample_t_copula(k, ALPHA, RHO, g), truth, rng)
        dep[n] = r
        print(f"{n:>8} {r['cfg_mean']:>10.4f} {r['cfg_sd']:>8.4f} {r['cfg_rmse']:>9.4f} "
              f"{r['sec_mean']:>10.4f} {r['sec_sd']:>8.4f} {r['sec_rmse']:>9.4f}")

    print(f"\nTAIL-INDEPENDENT CASE: Gaussian copula, rho={RHO}, true lambda_U = 0")
    print(f"{'n (=b)':>8} {'CFG mean':>10} {'CFG sd':>8} {'SEC mean':>10} {'SEC sd':>8}")
    ind = {}
    for n in (250, 500, 1000, 5000):
        r = run(n, lambda k, g: sample_gaussian_copula(k, RHO, g), 0.0, rng)
        ind[n] = r
        print(f"{n:>8} {r['cfg_mean']:>10.4f} {r['cfg_sd']:>8.4f} "
              f"{r['sec_mean']:>10.4f} {r['sec_sd']:>8.4f}")

    # THE decision a section-5 reader actually has to make: am I tail dependent?
    print("\nCAN A READER TELL THE TWO APART?  (the decision section 5 asks of them)")
    print(f"{'n (=b)':>8} {'estimator':>10} {'dep 5th pct':>12} {'ind 95th pct':>13} "
          f"{'separated':>10}")
    for n in (250, 500, 1000, 5000):
        for key, label in (("cfg_raw", "CFG"), ("sec_raw", "SEC")):
            lo = np.percentile(dep[n][key], 5)
            hi = np.percentile(ind[n][key], 95)
            print(f"{n:>8} {label:>10} {lo:>12.4f} {hi:>13.4f} "
                  f"{'yes' if lo > hi else 'NO':>10}")


# ------------------------------------------------------- all-pairs addendum
def sample_cluster_pairs(b, m, alpha, rho, rng, max_pairs_per_cluster=None):
    """b clusters of m exchangeable t_alpha scores; return WITHIN-cluster pairs.

    Every within-cluster pair has the same bivariate t_alpha copula with
    correlation rho, so each pair is a valid draw from section 5's pair copula --
    but pairs sharing a cluster are not independent of each other. This asks
    whether using all of them buys anything.
    """
    cov = np.full((m, m), rho)
    np.fill_diagonal(cov, 1.0)
    z = rng.multivariate_normal(np.zeros(m), cov, size=b)
    w = rng.chisquare(alpha, size=b) / alpha
    x = z / np.sqrt(w)[:, None]
    iu, ju = np.triu_indices(m, k=1)
    if max_pairs_per_cluster is not None and len(iu) > max_pairs_per_cluster:
        sel = rng.choice(len(iu), max_pairs_per_cluster, replace=False)
        iu, ju = iu[sel], ju[sel]
    return np.column_stack([x[:, iu].ravel(), x[:, ju].ravel()])


if __name__ == "__main__":
    print("\n\nADDENDUM -- does using ALL within-cluster pairs rescue the estimate?")
    print("b = 500 clusters (the released profile), m = 50 (its mean size).")
    truth = lambda_u_t(ALPHA, RHO)
    rng2 = np.random.default_rng(SEED + 99)
    print(f"{'pairs/cluster':>14} {'total pairs':>12} {'CFG mean':>10} {'CFG sd':>8} "
          f"{'SEC mean':>10} {'SEC sd':>8}")
    for ppc in (1, 5, 25, 100):
        cfg, sec = [], []
        for _ in range(60):
            pairs = sample_cluster_pairs(500, 50, ALPHA, RHO, rng2,
                                         max_pairs_per_cluster=ppc)
            u = pseudo_obs(pairs)
            cfg.append(lambda_cfg(u))
            _, curve = lambda_sec_curve(u)
            sec.append(plateau_estimate(curve))
        print(f"{ppc:>14} {500*ppc:>12} {np.mean(cfg):>10.4f} {np.std(cfg):>8.4f} "
              f"{np.mean(sec):>10.4f} {np.std(sec):>8.4f}")
    print(f"\n  truth = {truth:.4f}")
