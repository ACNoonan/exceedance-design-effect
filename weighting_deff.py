"""The two items left open after the nine full reads.

ITEM 1 -- the quantile step. Gill-Vardi-Wellner give a functional CLT for the
known-weight estimator G-circ of the *CDF*. Neither they nor Vardi treat
quantiles (0 hits, both papers). Coverage is a quantile functional, so the step
has to be taken. Delta method on the Hajek ratio, density cancels as in SW-02
Theorem 1 Step 4:

    n*Var(C) -> E_f[pi] * [ (1-p)^2 * m0(q_p) + p^2 * m1(q_p) ]
    m0(t) = int_{s<=t} f/pi ds ,  m1(t) = int_{s>t} f/pi ds

Note it is LEVEL-DEPENDENT, like rho_I(p). Claimed, so it must be tested.

ITEM 2 -- Tibshirani et al. Remark 5 says a matching UPPER bound on weighted
conformal "does not seem possible without further conditions on the weight
functions", because max_i p_i^w can be arbitrarily large. Positivity is such a
condition: if w in [l,u] with Gamma' = u/l, then

    p_i^w = w_i / sum_j w_j  <=  u / ((n+1) l)  =  Gamma'/(n+1)

which is the unweighted 1/(n+1) inflated by exactly Gamma'. Elementary -- but
whether it yields an overshoot of that size is a claim, and is measured here.

Arm B of SW-02 sec 3.5: f(s) = 1 + a(2s-1) on [0,1], pi(s) = (1-a)/f(s).
Selected law is Uniform(0,1); population CDF F(t) = t + a(t^2 - t).
w = 1/pi propto f, so the self-normalisation makes the constant free.

PRECONDITIONS (each can come out wrong):
  P1  a=0: variance formula must collapse to p(1-p). Analytic.
  P2  formula vs simulation at a in {0, 0.5, 0.9}. The real test of ITEM 1.
  P3  the formula must be LEVEL-DEPENDENT -- deff_pi(p) not constant in p.
      If it is flat, the parallel with rho_I(p) is invented.
  P4  max_i p_i^w <= Gamma'/(n+1), measured. The ITEM 2 ingredient.
  P5  weighted split conformal: coverage >= 1-alpha (validity) AND
      overshoot <= Gamma'/(n+1). Gamma'=1 must reduce to the classical
      [1-alpha, 1-alpha+1/(n+1)] band.
  P6  NEGATIVE CONTROL: run the same construction with w == 1 (selection
      ignored). It MUST break. If unweighted also lands in the band, the
      weighting is doing nothing and P5 proves nothing.
"""
import numpy as np
from scipy import integrate, optimize

rng = np.random.default_rng(20260729)
P = 0.90


def f_pop(s, a):
    return 1.0 + a * (2.0 * s - 1.0)


def F_pop(t, a):
    return t + a * (t**2 - t)


def q_pop(p, a):
    """population p-quantile: solve t + a(t^2-t) = p on [0,1]."""
    if a == 0.0:
        return p
    return optimize.brentq(lambda t: F_pop(t, a) - p, 0.0, 1.0)


def w_of(s, a):
    """w = 1/pi propto f. Constant is free under self-normalisation."""
    return f_pop(s, a)


# ---------------------------------------------------------------- ITEM 1

def nvar_formula(a, p=P):
    """n * Var(C) from the delta method. E_f[pi] = (1-a); f/pi = f^2/(1-a)."""
    t = q_pop(p, a)
    Epi = 1.0 - a
    m0 = integrate.quad(lambda s: f_pop(s, a) ** 2 / (1 - a), 0.0, t)[0]
    m1 = integrate.quad(lambda s: f_pop(s, a) ** 2 / (1 - a), t, 1.0)[0]
    return Epi * ((1 - p) ** 2 * m0 + p**2 * m1)


def nvar_sim(a, n=4000, reps=20000, p=P):
    """Hajek-weighted quantile on the SELECTED sample; C = F_pop(qhat)."""
    cov = np.empty(reps)
    for r in range(reps):
        s = rng.random(n)                    # selected law is Uniform
        w = w_of(s, a)
        o = np.argsort(s)
        ss, ws = s[o], w[o]
        cdf = np.cumsum(ws) / ws.sum()
        qhat = ss[np.searchsorted(cdf, p, side="left")]
        cov[r] = F_pop(qhat, a)
    return n * cov.var(), cov.mean()


# ---------------------------------------------------------------- ITEM 2

def weighted_conformal(a, n, reps, p=P):
    """Tibshirani-style weighted split conformal, test-point weight taken at its
    upper bound u (the conservative choice; JRC's u_{n+1} plays the same role).
    Returns (coverage, mean max jump, Gamma')."""
    lo, hi = 1.0 - a, 1.0 + a          # range of w = f on [0,1]
    gam = hi / lo
    cov, jump = np.empty(reps), np.empty(reps)
    for r in range(reps):
        s = rng.random(n)
        w = w_of(s, a)
        o = np.argsort(s)
        ss, ws = s[o], w[o]
        denom = ws.sum() + hi           # + u for the unseen test point
        pw = ws / denom
        jump[r] = pw.max()
        c = np.cumsum(pw)
        idx = np.searchsorted(c, p, side="left")
        qhat = ss[idx] if idx < n else 1.0
        cov[r] = F_pop(qhat, a)
    return cov.mean(), jump.mean(), gam


def unweighted_control(a, n, reps, p=P):
    """P6: same construction, selection ignored (w == 1)."""
    cov = np.empty(reps)
    k = int(np.ceil((n + 1) * p))
    for r in range(reps):
        s = np.sort(rng.random(n))
        cov[r] = F_pop(s[min(k, n) - 1], a)
    return cov.mean()


print("=" * 76)
print("ITEM 1 -- the quantile step: n*Var(C) formula vs simulation, p = 0.90")
print("=" * 76)
print(f"{'a':>5} {'formula':>10} {'sim':>10} {'rel err':>9} {'mean C':>9} {'deff_pi':>9}")
item1 = {}
for a in (0.0, 0.5, 0.9):
    fo = nvar_formula(a)
    si, mc = nvar_sim(a)
    item1[a] = (fo, si, mc)
    print(f"{a:>5.2f} {fo:>10.5f} {si:>10.5f} {abs(fo-si)/fo:>8.2%} {mc:>9.4f} "
          f"{fo/(P*(1-P)):>9.4f}")

print()
print("ITEM 1 -- level dependence of deff_pi(p) at a = 0.9  (P3)")
levels = [0.50, 0.70, 0.80, 0.90, 0.95]
deffs = [nvar_formula(0.9, p) / (p * (1 - p)) for p in levels]
print("  p      " + "".join(f"{p:>9.2f}" for p in levels))
print("  deff_pi" + "".join(f"{d:>9.4f}" for d in deffs))

print()
print("=" * 76)
print("ITEM 2 -- does positivity supply Remark 5's missing condition?")
print("=" * 76)
print(f"{'a':>5} {'Gamma':>7} {'n':>6} {'coverage':>10} {'overshoot':>10} "
      f"{'bound G/(n+1)':>14} {'maxjump':>9} {'G/(n+1)':>9}")
item2 = []
for a in (0.0, 0.5, 0.9):
    for n in (500, 2000):
        cv, jm, gam = weighted_conformal(a, n, reps=8000)
        bound = gam / (n + 1)
        item2.append((a, gam, n, cv, cv - P, bound, jm))
        print(f"{a:>5.2f} {gam:>7.2f} {n:>6d} {cv:>10.4f} {cv-P:>10.4f} "
              f"{bound:>14.4f} {jm:>9.5f} {gam/(n+1):>9.5f}")

print()
print("PRECONDITIONS")
p1 = abs(nvar_formula(0.0) - P * (1 - P)) < 1e-9
print(f"  P1  a=0 formula = p(1-p) = {P*(1-P):.4f}                          : {'PASS' if p1 else 'FAIL'}")

errs = [abs(item1[a][0] - item1[a][1]) / item1[a][0] for a in (0.0, 0.5, 0.9)]
p2 = max(errs) < 0.03
print(f"  P2  formula vs sim, max rel err {max(errs):.2%} (< 3%)              : {'PASS' if p2 else 'FAIL'}")

p3 = (max(deffs) - min(deffs)) > 0.05
print(f"  P3  deff_pi level-dependent, range {max(deffs)-min(deffs):.4f} (> 0.05)   : {'PASS' if p3 else 'FAIL'}")

p4 = all(jm <= bd + 1e-12 for (_, _, _, _, _, bd, jm) in item2)
print(f"  P4  max jump <= Gamma'/(n+1) in every cell                : {'PASS' if p4 else 'FAIL'}")

p5 = all(cv >= P - 2e-3 and (cv - P) <= bd + 2e-3
         for (_, _, _, cv, _, bd, _) in item2)
print(f"  P5  coverage in [1-alpha, 1-alpha + Gamma'/(n+1)] everywhere : {'PASS' if p5 else 'FAIL'}")

ctl = unweighted_control(0.9, 2000, 8000)
p6 = ctl < P - 0.05
print(f"  P6  NEG CTRL unweighted at a=0.9 -> {ctl:.4f}, must break     : {'PASS' if p6 else 'FAIL'}")
