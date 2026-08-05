"""Compound design effect, tightened.

Round 1 could not separate our rho_W formula from Kish's naive rho_I product:
both sat inside the simulation noise of a quantile-based estimate. The quantile
step adds order-statistic discreteness that has nothing to do with the claim
being tested. So test the claim itself:

    n Var( Ghat(t) )  =  [ Var(U)/E[w]^2 ] * [ 1 + (m-1) rho_W ]   at FIXED t

Ghat is the Hajek-weighted empirical CDF. The density-cancellation step carrying
this to coverage is already established (Step 4 / Ghosh), so isolating Ghat is
the honest place to test the composition.

Precision is now the point, so every quantity carries a standard error and the
verdict is stated against it rather than against an eyeballed tolerance.

PRECONDITIONS:
  P1  a=0: ours must equal p(1-p)[1+(m-1)rho_I] within its own SE.
  P2  m=1: bracket exactly 1, ours == naive identically.
  P3  ours within 3 SE of simulation in every cell.
  P4  DECISIVE. Where w correlates with the indicator inside a cluster, naive
      must sit MORE than 3 SE from simulation while ours sits within 3 SE.
      If both fit, rho_W is a distinction without a difference.
  P5  rho_W != rho_I at r>0, a>0 (only there; at r=0 both are ~0 trivially,
      which is why round 1's version of this check was ill-posed).
"""
import numpy as np
from scipy import optimize
from scipy.stats import norm

rng = np.random.default_rng(8675309)
P = 0.90


def f_pop(s, a):  return 1.0 + a * (2.0 * s - 1.0)
def F_pop(t, a):  return t + a * (t**2 - t)


def q_pop(p, a):
    return p if a == 0.0 else optimize.brentq(lambda t: F_pop(t, a) - p, 0.0, 1.0)


def clusters(b, m, r):
    z = rng.standard_normal((b, 1)); e = rng.standard_normal((b, m))
    return norm.cdf(np.sqrt(r) * z + np.sqrt(1 - r) * e)


def moments(a, r, t, reps=2_000_000):
    """Var(U), E[w], rho_W, rho_I from cluster PAIRS. Large reps: these feed
    the prediction, so their noise must be far below the effect being tested."""
    s = clusters(reps, 2, r)
    w = f_pop(s, a); ind = (s <= t).astype(float); G = F_pop(t, a)
    U = w * (ind - G)
    return (U.var(), w.mean(),
            np.corrcoef(U[:, 0], U[:, 1])[0, 1],
            np.corrcoef(ind[:, 0], ind[:, 1])[0, 1])


def sim_var_Ghat(a, r, m, b, reps=200_000):
    """n * Var(Ghat(t)) at fixed t, plus its standard error."""
    t = q_pop(P, a); n = b * m
    G = np.empty(reps)
    CH = 4000
    for lo in range(0, reps, CH):
        k = min(CH, reps - lo)
        s = clusters(k * b, m, r).reshape(k, b * m)
        w = f_pop(s, a)
        G[lo:lo + k] = (w * (s <= t)).sum(1) / w.sum(1)
    v = G.var(ddof=1)
    se = v * np.sqrt(2.0 / (reps - 1))          # SE of a variance estimate
    return n * v, n * se


print("=" * 96)
print("n*Var(Ghat) at fixed t = q_p : does the compound deff run on rho_W or rho_I?")
print("=" * 96)
print(f"{'a':>4} {'r':>4} {'m':>3} {'sim':>9} {'+-SE':>7} {'ours':>9} {'z_ours':>7} "
      f"{'naive':>9} {'z_naive':>8} {'rho_W':>7} {'rho_I':>7}")

rows = []
for a in (0.0, 0.9):
    for r in (0.0, 0.6):
        for m in (1, 4):
            t = q_pop(P, a)
            varU, Ew, rw, ri = moments(a, r, t)
            base = varU / Ew**2
            ours = base * (1 + (m - 1) * rw)
            naive = base * (1 + (m - 1) * ri)
            sim, se = sim_var_Ghat(a, r, m, b=max(1, 400 // m))
            zo, zn = abs(ours - sim) / se, abs(naive - sim) / se
            rows.append(dict(a=a, r=r, m=m, sim=sim, se=se, ours=ours,
                             naive=naive, zo=zo, zn=zn, rw=rw, ri=ri))
            print(f"{a:>4.1f} {r:>4.1f} {m:>3d} {sim:>9.5f} {se:>7.5f} {ours:>9.5f} "
                  f"{zo:>7.2f} {naive:>9.5f} {zn:>8.2f} {rw:>7.4f} {ri:>7.4f}")

print()
print("PRECONDITIONS  (z = |prediction - simulation| / SE)")
p1 = all(abs(d["ours"] - P*(1-P)*(1+(d["m"]-1)*d["ri"])) < 3*d["se"]
         for d in rows if d["a"] == 0.0)
print(f"  P1  a=0 collapses to Theorem 1 within SE                    : {'PASS' if p1 else 'FAIL'}")
p2 = all(d["ours"] == d["naive"] for d in rows if d["m"] == 1)
print(f"  P2  m=1: bracket identically 1                              : {'PASS' if p2 else 'FAIL'}")
p3 = all(d["zo"] < 3 for d in rows)
print(f"  P3  ours within 3 SE everywhere (max z = {max(d['zo'] for d in rows):.2f})           : {'PASS' if p3 else 'FAIL'}")
hard = [d for d in rows if d["a"] > 0 and d["m"] > 1 and d["r"] > 0]
p4 = all(d["zo"] < 3 and d["zn"] > 3 for d in hard)
for d in hard:
    print(f"  P4  DECISIVE a={d['a']} r={d['r']} m={d['m']}: z_ours={d['zo']:.2f} (<3), "
          f"z_naive={d['zn']:.2f} (>3)  : {'PASS' if (d['zo']<3 and d['zn']>3) else 'FAIL'}")
p5 = all(abs(d["rw"] - d["ri"]) > 0.01 for d in hard)
print(f"  P5  rho_W != rho_I at r>0, a>0                              : {'PASS' if p5 else 'FAIL'}")
