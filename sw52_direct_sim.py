"""SW-52: is the 2.9% gap the LAW running high, or the BOOTSTRAP running low?

SW-24's precondition P4 simulated the released size profile at a known true
rho_I and found: law-at-true-rho_I 5.55, "measured" 5.39 -- a 2.9% gap that
SW-24 attributes to the law. But P4's measured arm IS the cluster bootstrap, so
the instrument is judging itself, and §9b independently reports that the
bootstrap runs low under size skew. Both explanations fit.

A third arm settles it. TRUTH here is the sd of realised coverage across MANY
INDEPENDENT datasets -- never a resampling of one -- which is the design
verify_bootstrap_bias.py uses in the SWE-bench lane. Then:

    law  vs truth   ->  is Proposition 2's m_tilde substitution high?
    boot vs truth   ->  is the cluster bootstrap low at this b and CV^2?

PRECONDITIONS (each can come out wrong):
  P1  the size profile must reproduce §6.1's published b, m_bar, m_tilde, CV^2.
  P2  NEGATIVE CONTROL at rho_I = 0: law, bootstrap and truth must all agree,
      since with independent units there is nothing for either to get wrong.
  P3  the truth arm's own Monte Carlo error must be far below the 2.9% gap being
      attributed, or the comparison cannot decide anything.
"""
import numpy as np
from scipy.stats import norm

rng = np.random.default_rng(52052)
P, RHO_I_TARGET = 0.8909, 0.4941        # §6.1's achieved level; SW-24 P4's INDICATOR ICC

def rho_for_rho_I(target, p):
    """SW-24's 0.4941 is the INDICATOR ICC, not the score correlation. The first
    run set it as the score correlation and landed at rho_I = 0.2507 -- a
    different cell from the one being checked. Solve for the score correlation
    that delivers the target rho_I at this level."""
    from scipy.optimize import brentq
    zq = np.linspace(-8, 8, 4001); w = norm.pdf(zq); w /= w.sum()
    def f(r):
        pi = norm.cdf((norm.ppf(p) - np.sqrt(r) * zq) / np.sqrt(1 - r))
        return ((pi ** 2 * w).sum() - p ** 2) / (p * (1 - p)) - target
    return brentq(f, 1e-6, 0.999999)
N_TRUTH, N_BOOT = 9000, 1200


def released_sizes():
    """§6.1's ACTUAL profile, from the same loader §6.1 uses. No fallback:
    a reconstructed profile silently passed a b-only precondition on the first
    attempt while m_bar was 42% wrong, so this now fails loudly instead."""
    from prm_measurement import load
    return np.array([len(f) for f in load()], dtype=int)


def one_dataset(sizes, rho):
    """One-factor Gaussian within cluster -> Uniform marginals."""
    out = []
    for m in sizes:
        z = rng.standard_normal()
        e = rng.standard_normal(m)
        out.append(norm.cdf(np.sqrt(rho) * z + np.sqrt(1 - rho) * e))
    return np.concatenate(out), sizes


def coverage(scores, p):
    n = scores.size
    k = int(np.ceil((n + 1) * p))
    return np.sort(scores)[min(k, n) - 1]      # F = identity (Uniform)


def truth_sd(sizes, rho, reps=N_TRUTH):
    """Independent datasets. Never a resampling."""
    return np.std([coverage(one_dataset(sizes, rho)[0], P) for _ in range(reps)], ddof=1)


def bootstrap_sd(sizes, rho, reps=N_BOOT, datasets=12):
    """The §6.1 instrument, AVERAGED over independent datasets. A single
    realisation is what made the first attempt uninterpretable."""
    vals = [_boot_once(sizes, rho, reps) for _ in range(datasets)]
    return float(np.mean(vals)), float(np.std(vals, ddof=1))


def _boot_once(sizes, rho, reps):
    scores, _ = one_dataset(sizes, rho)
    starts = np.concatenate([[0], np.cumsum(sizes)])
    fams = [scores[starts[i]:starts[i + 1]] for i in range(len(sizes))]
    b = len(fams)
    out = np.empty(reps)
    for r in range(reps):
        idx = rng.integers(0, b, b)
        out[r] = coverage(np.concatenate([fams[i] for i in idx]), P)
    return out.std(ddof=1)


def law_sd(sizes, rho):
    n = sizes.sum()
    m_til = (sizes.astype(float) ** 2).sum() / sizes.sum()
    # rho_I at level P for a one-factor Gaussian, by quadrature
    z = np.linspace(-8, 8, 4001)
    w = norm.pdf(z); w /= w.sum()
    pi = norm.cdf((norm.ppf(P) - np.sqrt(rho) * z) / np.sqrt(1 - rho))
    delta = (pi ** 2 * w).sum()
    rho_I = (delta - P ** 2) / (P * (1 - P))
    return np.sqrt(P * (1 - P) * (1 + (m_til - 1) * rho_I) / n), rho_I, m_til


sizes = released_sizes()
n, b = int(sizes.sum()), len(sizes)
m_bar = sizes.mean(); m_til = (sizes.astype(float) ** 2).sum() / sizes.sum()
cv2 = m_til / m_bar - 1
print("=" * 74)
print("SW-52: three arms on the released size profile")
print("=" * 74)
print(f"  b={b}  n={n}  m_bar={m_bar:.2f}  m_tilde={m_til:.2f}  CV^2={cv2:.3f}")
ok1 = (b == 500 and n == 25028 and abs(m_bar - 50.06) < 0.05
       and abs(m_til - 61.29) < 0.05 and abs(cv2 - 0.224) < 0.005)
print(f"  P1  ALL of b=500, n=25028, m_bar 50.06, m_tilde 61.29, CV^2 0.224 : "
      f"{'PASS' if ok1 else 'FAIL'}")
assert ok1, "profile does not reproduce §6.1 -- refusing to report anything downstream"

RHO_TRUE = rho_for_rho_I(RHO_I_TARGET, P)
print(f"  score correlation giving rho_I = {RHO_I_TARGET}: rho = {RHO_TRUE:.4f}")
for rho, label in ((RHO_TRUE, f"rho_I = {RHO_I_TARGET} (SW-24 P4's cell)"),):
    ls, rho_I, _ = law_sd(sizes, rho)
    ts = truth_sd(sizes, rho)
    bs, bs_sd = bootstrap_sd(sizes, rho)
    se = ts / np.sqrt(2 * (N_TRUTH - 1))
    print()
    print(f"  {label}   (rho_I = {rho_I:.4f})")
    print(f"    truth  (independent datasets) : {ts:.6f}   +- {se:.6f}")
    print(f"    law    (Prop 2 at true rho_I) : {ls:.6f}   ratio to truth {ls/ts:.4f}")
    print(f"    boot   (§6.1's instrument)    : {bs:.6f}   ratio to truth {bs/ts:.4f}"
          f"   (across-dataset sd {bs_sd:.6f})")
    if True:
        print(f"    P3  truth's own MC error {se/ts:.2%} << the 2.9% being attributed : "
              f"{'PASS' if se/ts < 0.01 else 'FAIL'}")
        print()
        print("    READING")
        print(f"      law is {(ls/ts-1)*100:+.1f}% vs truth;  bootstrap is {(bs/ts-1)*100:+.1f}% vs truth.")
