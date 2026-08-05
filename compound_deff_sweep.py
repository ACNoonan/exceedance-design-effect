"""Is our 3.6-SE residual a finite-b delta-method artifact, or a real bias?

The Hajek estimator is a RATIO; the delta method is first order, so a residual
of order 1/b is expected and must VANISH as b grows. A residual that does not
shrink is a wrong formula.

DECISIVE PREDICTION: rel_err(ours) ~ C/b, so rel_err * b is roughly constant
and rel_err -> 0. The naive rho_I formula must instead converge to a NONZERO
offset, since it is asymptotically the wrong quantity.
"""
import numpy as np
from scipy import optimize
from scipy.stats import norm
rng = np.random.default_rng(2718281)
P, A, R, M = 0.90, 0.9, 0.6, 4

def f_pop(s,a): return 1.0 + a*(2.0*s-1.0)
def F_pop(t,a): return t + a*(t**2-t)
t = optimize.brentq(lambda x: F_pop(x,A)-P, 0, 1)

def clusters(b,m,r):
    z = rng.standard_normal((b,1)); e = rng.standard_normal((b,m))
    return norm.cdf(np.sqrt(r)*z + np.sqrt(1-r)*e)

s = clusters(3_000_000,2,R); w = f_pop(s,A); ind=(s<=t).astype(float); G=F_pop(t,A)
U = w*(ind-G)
varU, Ew = U.var(), w.mean()
rw = np.corrcoef(U[:,0],U[:,1])[0,1]; ri = np.corrcoef(ind[:,0],ind[:,1])[0,1]
ours  = (varU/Ew**2)*(1+(M-1)*rw)
naive = (varU/Ew**2)*(1+(M-1)*ri)
print(f"asymptotic predictions:  ours {ours:.5f}   naive {naive:.5f}   "
      f"(rho_W {rw:.4f}, rho_I {ri:.4f})\n")

print(f"{'b':>6} {'n':>7} {'sim':>9} {'+-SE':>8} {'z_ours':>7} {'z_naive':>8} "
      f"{'relerr_ours':>12} {'x b':>8}")
res=[]
for b in (25, 50, 100, 200, 400, 800):
    reps = 400_000
    Gh = np.empty(reps); CH = max(1, 2_000_000//(b*M))
    for lo in range(0, reps, CH):
        k=min(CH,reps-lo)
        x = clusters(k*b, M, R).reshape(k, b*M)
        ww = f_pop(x,A)
        Gh[lo:lo+k] = (ww*(x<=t)).sum(1)/ww.sum(1)
    v = Gh.var(ddof=1); se = v*np.sqrt(2.0/(reps-1)); n=b*M
    sim, sesim = n*v, n*se
    zo, zn = abs(ours-sim)/sesim, abs(naive-sim)/sesim
    rel = (ours-sim)/sim
    res.append((b, rel, zo, zn))
    print(f"{b:>6d} {n:>7d} {sim:>9.5f} {sesim:>8.5f} {zo:>7.2f} {zn:>8.2f} "
          f"{rel:>11.3%} {rel*b:>8.3f}")

print()
rels = [abs(r) for _,r,_,_ in res]
mono = all(rels[i] >= rels[i+1]-2e-4 for i in range(len(rels)-1))
prod = [r*b for b,r,_,_ in res]
stable = max(prod)/min(prod) < 4 if min(prod)>0 else False
zn_grows = res[-1][3] > res[0][3]
print(f"  S1  rel_err(ours) shrinks as b grows                 : {'PASS' if mono else 'FAIL'}")
print(f"  S2  rel_err x b roughly constant ({min(prod):.2f}..{max(prod):.2f})  : {'PASS' if stable else 'FAIL'}")
print(f"  S3  NEG CTRL z_naive GROWS with b (fixed offset)      : {'PASS' if zn_grows else 'FAIL'}")
print(f"  S4  z_ours at largest b = {res[-1][2]:.2f}")
