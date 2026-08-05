"""
Does Jin-Ren-Candes (arXiv:2111.12161) apply to SW-02 Theorem 2's construction?

Theorem 2 (SW-02 sec 3.5):
  Arm A: F  = Unif(0,1), pi  = 1           -> calibration law F_pi  = Unif(0,1)
  Arm B: f' = 1 + a(2s-1), pi' = (1-a)/f'  -> calibration law F'_pi' = Unif(0,1)
  Observationally identical; realised coverage differs by a*p(1-p).

JRC: calibration ~ P, test ~ Ptilde, ratio w = dPtilde/dP bounded l <= w <= u.
Here P = calibration law (Unif), Ptilde = population law F, so w = dF/dF_pi = f'.
Range of f' on [0,1] is [1-a, 1+a], so l = 1-a, u = 1+a, Gamma = (1+a)/(1-a).

TWO procedures, and they are NOT the same threshold:
  Alg 1 (marginal, JRC eq. 8):  Fhat(k) = k*l / (k*l + (n-k)*u + u), take V_[k*].
        Asymptote: t/(1-t) = p*u / ((1-p)*l).
  Alg 2 (PAC / sharp, JRC Prop 4.2): G(t) = max(l*t, 1 - u*(1-t)), vhat = G^{-1}(p).

PRECONDITIONS (each could come out wrong):
  C1  a=0 -> Gamma=1, gap=0, and NO inflation under either algorithm.
  C2  Unadjusted arm-B coverage = p - a*p(1-p)  (paper: 8.1pp at p=.9, a=.9).
  C3  Both algorithms restore coverage >= p in BOTH arms, all a.
  C4  Finite-n Alg 1 matches the Alg 1 asymptote (not the Alg 2 one).
  C5  NEGATIVE CONTROL: Alg 1 must be >= Alg 2's threshold (it is the looser bound).
      If Alg 1 came out sharper, the mapping is wrong.
"""
import numpy as np

rng = np.random.default_rng(7)


def F_B(t, a):
    """CDF of arm B's *population* law: f'(s) = 1 + a(2s-1)."""
    return t + a * (t**2 - t)


def t_alg1(p, lo, hi):
    """Asymptotic threshold of JRC Algorithm 1 (marginal procedure)."""
    odds = p * hi / ((1.0 - p) * lo)
    return odds / (1.0 + odds)


def t_alg2(p, lo, hi):
    """JRC Prop 4.2 worst-case cdf, scores ~ Unif under P: G(t)=max(l t, 1-u(1-t))."""
    cands = []
    if lo > 0 and p / lo <= 1.0:
        cands.append(p / lo)
    t2 = 1.0 - (1.0 - p) / hi
    if t2 <= 1.0:
        cands.append(t2)
    return min(cands) if cands else np.inf


def report(a, p=0.90):
    lo, hi = 1.0 - a, 1.0 + a
    gamma = hi / lo if lo > 0 else np.inf
    t1, t2 = t_alg1(p, lo, hi), t_alg2(p, lo, hi)
    return dict(a=a, gamma=gamma,
                cov_B_plain=F_B(p, a), gap=p - F_B(p, a), pred=a * p * (1 - p),
                t1=t1, covA1=t1, covB1=F_B(t1, a),
                t2=t2, covA2=t2, covB2=F_B(t2, a))


def finite_sample_alg1(a, p=0.90, n=5000, reps=2000):
    """Split conformal on arm B, JRC Alg 1 index k*, evaluated on population F'."""
    lo, hi = 1.0 - a, 1.0 + a
    idx = np.arange(1, n + 1)
    Fhat = (idx * lo) / (idx * lo + (n - idx) * hi + hi)
    ok = np.where(Fhat >= p)[0]
    kstar = ok[0] if len(ok) else n - 1
    k_plain = int(np.ceil((n + 1) * p))
    cp, ca = [], []
    for _ in range(reps):
        cal = np.sort(rng.random(n))
        cp.append(F_B(cal[k_plain - 1], a))
        ca.append(F_B(cal[kstar], a))
    return np.mean(cp), np.mean(ca)


print("=" * 84)
print("SW-02 Theorem 2 construction, viewed through Jin-Ren-Candes")
print("=" * 84)
print(f"{'a':>5} {'Gamma':>7} {'covB plain':>11} {'gap':>8} {'pred':>8} "
      f"{'t(Alg1)':>8} {'covB(1)':>8} {'t(Alg2)':>8} {'covB(2)':>8}")
rows = [report(a) for a in [0.0, 0.2, 0.5, 0.9]]
for r in rows:
    print(f"{r['a']:>5.2f} {r['gamma']:>7.2f} {r['cov_B_plain']:>11.4f} "
          f"{r['gap']:>8.4f} {r['pred']:>8.4f} {r['t1']:>8.4f} {r['covB1']:>8.4f} "
          f"{r['t2']:>8.4f} {r['covB2']:>8.4f}")

print()
print("PRECONDITION CHECKS (each could have failed)")
r0, r9 = rows[0], rows[-1]

c1 = (abs(r0['gamma'] - 1) < 1e-12 and abs(r0['gap']) < 1e-12
      and abs(r0['t1'] - 0.9) < 1e-12 and abs(r0['t2'] - 0.9) < 1e-12)
print(f"  C1  a=0: Gamma=1, gap=0, t1=t2=0.90                      : {'PASS' if c1 else 'FAIL'}")

c2 = abs(r9['gap'] - 0.081) < 5e-4
print(f"  C2  a=0.9 gap = {r9['gap']:.4f} vs paper's 0.081            : {'PASS' if c2 else 'FAIL'}")

c3 = all(r['covA1'] >= 0.9 - 1e-9 and r['covB1'] >= 0.9 - 1e-9
         and r['covA2'] >= 0.9 - 1e-9 and r['covB2'] >= 0.9 - 1e-9 for r in rows)
print(f"  C3  both algorithms >= 0.90 in BOTH arms, all a           : {'PASS' if c3 else 'FAIL'}")

mp, ma = finite_sample_alg1(0.9)
c4 = abs(mp - r9['cov_B_plain']) < 5e-3 and abs(ma - r9['covB1']) < 5e-3
print(f"  C4  finite-n Alg1: plain {mp:.4f} vs {r9['cov_B_plain']:.4f}, "
      f"adj {ma:.4f} vs {r9['covB1']:.4f}   : {'PASS' if c4 else 'FAIL'}")

c5 = all(r['t1'] >= r['t2'] - 1e-12 for r in rows)
print(f"  C5  NEG CONTROL: Alg1 threshold >= Alg2 threshold, all a  : {'PASS' if c5 else 'FAIL'}")

print()
print("READING")
print(f"  Theorem 2's construction at a=0.9 sits at Gamma = {r9['gamma']:.0f}.")
print(f"  The sharp (Alg 2) threshold moves 0.9000 -> {r9['t2']:.4f} and lands arm B at "
      f"{r9['covB2']:.4f} -- it repairs the 8.1pp gap almost exactly.")
print(f"  The marginal (Alg 1) threshold moves to {r9['t1']:.4f}, landing at "
      f"{r9['covB1']:.4f} -- valid but badly overshooting at large Gamma.")
