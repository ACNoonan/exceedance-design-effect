"""Does SW-02's (A1)-(A2) imply Francisco-Fuller Condition 6?

C6:  Var{Fhat(x+d) - Fhat(x)} <= C n^{-1} |d|  uniformly, for x, x+d in a
neighbourhood B of q_p.

Claim: with b iid clusters of FIXED size m and equal weights,
  Var{Fhat(x+d)-Fhat(x)} = b^{-1} Var{G_1(x+d)-G_1(x)} <= (m/n) * sup_B f * |d|
so C = m * sup_B f works.  Derivation: N = #{r : x < S_1r <= x+d} <= m, so
Var(N) <= E[N^2] <= m E[N] = m^2 (F(x+d)-F(x)).  Divide by m^2, then by b.

PRECONDITIONS (each can fail):
  A  measured Var must respect the claimed bound at every (x,d,rho,m) cell
  B  the bound must be TIGHT enough to be meaningful -- not off by 10^3
  C  NEGATIVE CONTROL: break fixed-m by giving one cluster O(b) of the mass
     (a single giant cluster). The bound must then FAIL -- otherwise the
     argument is not actually using fixed m and proves nothing.
"""
import numpy as np
rng = np.random.default_rng(5)

def gauss_cluster(b, m, rho):
    z = rng.standard_normal((b, 1)); e = rng.standard_normal((b, m))
    g = np.sqrt(rho) * z + np.sqrt(1 - rho) * e          # equicorrelated
    from scipy.stats import norm
    return norm.cdf(g)                                    # Uniform marginals

def measure(b, m, rho, x, d, reps=6000):
    n = b * m
    diffs = np.empty(reps)
    for r in range(reps):
        s = gauss_cluster(b, m, rho)
        G = ((s <= x + d).mean(1) - (s <= x).mean(1))      # per-cluster
        diffs[r] = G.mean()
    return diffs.var(), n

print(f"{'m':>3} {'rho':>5} {'x':>5} {'d':>7} {'measured Var':>13} {'bound C/n*d':>12} {'ratio':>7}")
ok_A, ratios = True, []
for m in (4, 8):
    for rho in (0.0, 0.6):
        for x in (0.80, 0.90):
            for d in (0.02, 0.05):
                b = 400
                v, n = measure(b, m, rho, x, d)
                C = m * 1.0                                # sup f = 1 (Uniform)
                bound = C * d / n
                ratios.append(v / bound)
                ok_A &= v <= bound * 1.02
                print(f"{m:>3d} {rho:>5.1f} {x:>5.2f} {d:>7.2f} {v:>13.3e} {bound:>12.3e} {v/bound:>7.3f}")

print()
print(f"  A  measured Var <= (m sup f) d / n in every cell      : {'PASS' if ok_A else 'FAIL'}")
print(f"  B  bound tight within 100x (max ratio {max(ratios):.3f})       : "
      f"{'PASS' if max(ratios) > 0.01 else 'FAIL'}")

# C: negative control -- one cluster carries half the total weight
def measure_giant(b, m, x, d, reps=4000):
    """One giant cluster of size b*m/2, rest tiny. Equal-weight-per-UNIT still,
    but cluster sizes are wildly unequal -> jumps can be O(1), not O(m/n)."""
    big = (b * m) // 2
    diffs = np.empty(reps)
    for r in range(reps):
        from scipy.stats import norm
        zb = rng.standard_normal(); sb = norm.cdf(np.sqrt(.9)*zb + np.sqrt(.1)*rng.standard_normal(big))
        rest = rng.random(b * m - big)
        s = np.concatenate([sb, rest])
        diffs[r] = (s <= x + d).mean() - (s <= x).mean()
    return diffs.var(), b * m

vg, ng = measure_giant(400, 8, 0.90, 0.02)
bound_g = 8 * 0.02 / ng
okC = vg > bound_g
print(f"  C  NEG CTRL one giant cluster: Var {vg:.3e} vs bound {bound_g:.3e} "
      f"-> must EXCEED : {'PASS' if okC else 'FAIL'}")
