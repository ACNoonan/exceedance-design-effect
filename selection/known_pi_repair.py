"""
Is SW-02 Theorem 2's tilt repairable when pi is KNOWN?

Survey-sampling reflex (Yang's lineage: Kim, informative sampling): if the
selection probability is known up to a constant AND bounded away from zero,
the tilt is invertible by Hajek weighting -- no sensitivity parameter needed.
If positivity fails, no weight can help. That is a DICHOTOMY, and the paper
currently states neither half.

Arm B of section 3.5:  f'(s) = 1 + a(2s-1),  pi'(s) = (1-a)/f'(s)
  -> selected law is Uniform(0,1); population CDF F'(t) = t + a(t^2 - t).
Unweighted split conformal at p=0.90, a=0.90 lands at 0.819 (the 8.1pp gap).

PRECONDITIONS (each can come out wrong):
  P1  a=0: weights all equal; Hajek must change NOTHING.
  P2  Hajek CDF must recover F'(t) = t + a(t^2-t), not the Uniform we observe.
  P3  Hajek-thresholded conformal must land arm B at 0.90, repairing 8.1pp
      with NO sensitivity parameter supplied.
  P4  NEGATIVE CONTROL -- hard cut-off pi(s)=1{s>tau} violates positivity.
      Weighting must FAIL here. If it "repairs" this too, the dichotomy is
      fake and I have a bug.
  P5  Price: Kish effective sample size from the weights must be < n, and
      must fall as a grows. A repair that costs nothing is a bug.
"""
import numpy as np

rng = np.random.default_rng(11)
P = 0.90


def f_pop(s, a):
    return 1.0 + a * (2.0 * s - 1.0)


def F_pop(t, a):
    return t + a * (t**2 - t)


def pi_soft(s, a):
    return (1.0 - a) / f_pop(s, a)


def hajek_quantile(s_obs, w, p):
    """Weighted p-quantile: smallest t with weighted CDF >= p."""
    o = np.argsort(s_obs)
    s_sorted, w_sorted = s_obs[o], w[o]
    cdf = np.cumsum(w_sorted) / np.sum(w_sorted)
    return s_sorted[np.searchsorted(cdf, p, side="left")]


def kish_neff(w):
    return w.sum() ** 2 / np.sum(w**2)


def run_soft(a, n=20000, reps=400):
    """Selected sample is Uniform(0,1) by construction of arm B."""
    plain, hajek, neffs = [], [], []
    for _ in range(reps):
        s = rng.random(n)                     # observed (selected) scores
        w = 1.0 / pi_soft(s, a)               # inverse selection prob, known
        k = int(np.ceil((n + 1) * P))
        t_plain = np.sort(s)[k - 1]
        t_haj = hajek_quantile(s, w, P)
        plain.append(F_pop(t_plain, a))       # realised coverage on population
        hajek.append(F_pop(t_haj, a))
        neffs.append(kish_neff(w))
    return np.mean(plain), np.mean(hajek), np.mean(neffs) / n


def run_cutoff(tau=0.30, n=20000, reps=200):
    """NEGATIVE CONTROL: pi(s) = 1{s > tau}. Population Uniform(0,1).
    Observed sample is Uniform(tau,1). Positivity fails below tau."""
    plain, weighted = [], []
    for _ in range(reps):
        s = tau + (1.0 - tau) * rng.random(n)      # what survives selection
        w = np.ones(n)                              # 1/pi = 1 wherever pi=1
        k = int(np.ceil((n + 1) * P))
        t_plain = np.sort(s)[k - 1]
        t_w = hajek_quantile(s, w, P)
        plain.append(t_plain)                       # F = identity (Uniform pop)
        weighted.append(t_w)
    return np.mean(plain), np.mean(weighted)


print("=" * 78)
print("Does knowing pi repair Theorem 2's tilt?   target coverage = 0.90")
print("=" * 78)
print(f"{'a':>5} {'Gamma':>7} {'cov plain':>10} {'cov Hajek':>10} {'n_eff/n':>9}")
rows = {}
for a in [0.0, 0.2, 0.5, 0.9]:
    cp, ch, ne = run_soft(a)
    rows[a] = (cp, ch, ne)
    g = (1 + a) / (1 - a) if a < 1 else np.inf
    print(f"{a:>5.2f} {g:>7.2f} {cp:>10.4f} {ch:>10.4f} {ne:>9.4f}")

print()
print("PRECONDITIONS")
cp0, ch0, ne0 = rows[0.0]
p1 = abs(cp0 - ch0) < 2e-3 and abs(ne0 - 1.0) < 1e-9
print(f"  P1  a=0: Hajek changes nothing ({cp0:.4f} vs {ch0:.4f}), n_eff/n={ne0:.4f} : {'PASS' if p1 else 'FAIL'}")

a_chk, t_chk = 0.9, 0.6
s = rng.random(400000)
w = 1.0 / pi_soft(s, a_chk)
emp = np.sum(w[s <= t_chk]) / np.sum(w)
p2 = abs(emp - F_pop(t_chk, a_chk)) < 3e-3
print(f"  P2  Hajek CDF at t=0.6 -> {emp:.4f} vs F_pop {F_pop(t_chk, a_chk):.4f} "
      f"(observed/unweighted would be {t_chk:.4f})   : {'PASS' if p2 else 'FAIL'}")

cp9, ch9, ne9 = rows[0.9]
p3 = abs(cp9 - 0.819) < 5e-3 and abs(ch9 - 0.90) < 5e-3
print(f"  P3  a=0.9: plain {cp9:.4f} (paper's 0.819) -> Hajek {ch9:.4f}, no Gamma  : {'PASS' if p3 else 'FAIL'}")

cop, cow = run_cutoff()
p4 = abs(cop - cow) < 5e-3 and cop > 0.90 + 0.02
print(f"  P4  NEG CTRL cut-off: plain {cop:.4f}, weighted {cow:.4f} -- both wrong  : {'PASS' if p4 else 'FAIL'}")

neffs = [rows[a][2] for a in [0.0, 0.2, 0.5, 0.9]]
p5 = all(neffs[i] >= neffs[i + 1] - 1e-9 for i in range(len(neffs) - 1)) and neffs[-1] < 0.98
print(f"  P5  n_eff/n monotone decreasing in a, ends {neffs[-1]:.4f} < 1           : {'PASS' if p5 else 'FAIL'}")

print()
print("READING")
print(f"  pi known + bounded away from 0  -> tilt is INVERTIBLE. 8.1pp gap closes")
print(f"     to {abs(ch9-0.90)*100:.2f}pp with no sensitivity parameter supplied.")
print(f"  Price is dispersion, not bias: n_eff/n = {ne9:.4f} at Gamma=19, i.e. a")
print(f"     weighting design effect of {1/ne9:.3f} that COMPOSES with Theorem 1's.")
print(f"  Positivity violated (cut-off) -> weighting is powerless ({cow:.4f}); this")
print(f"     is the genuinely non-identified case, and section 6.1's 1024-token")
print(f"     discard is a cut-off.")
