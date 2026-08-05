"""Is the one-way ANOVA the best ICC estimator on ragged sizes, or just better
than the one it replaced?

§8 recommends the one-way ANOVA form on the exceedance indicator, and
prm_measurement.anova_icc documents why: the naive pair estimator
delta_hat = sum C(c_j,2)/sum C(m_j,2) with a point-weighted p_hat is
inconsistent under unequal sizes, because delta_hat weights families by
m_j(m_j-1) while p_hat weights by m_j.

That diagnosis names a WEIGHTING MISMATCH, not a defect of the pair idea. Match
the weightings and the objection should go away. This tests three estimators
against a known truth on §6.1's released size profile:

  A  one-way ANOVA                      -- what §8 recommends
  B  naive pair (mismatched weights)     -- what §8 rejects
  C  weight-matched pair                 -- p_hat weighted by m_j(m_j-1) to
                                            match delta_hat. Untried here.

SW-24 measured A at ~10% low on this profile. If C is unbiased, §8's
recommendation is beatable and its new "lower bound" caveat can be dropped.

PRECONDITIONS (each can come out wrong):
  P1  EQUAL sizes: all three must be near-unbiased. Isolates raggedness as the
      cause rather than something about the indicator.
  P2  reproduce the DOCUMENTED pathology of B on ragged sizes -- if B behaves,
      the premise for preferring A is not what the docstring says.
  P3  reproduce SW-24's finding that A runs ~10% low on this profile. Today has
      already produced one number that matched a published one on a broken
      measurement, so this is asserted before anything is concluded.
"""
import numpy as np
from scipy.stats import norm
from scipy.optimize import brentq
from prm_measurement import anova_icc, load

rng = np.random.default_rng(31415)
P, RHO_I = 0.8909, 0.4941
REPS = 400


def rho_for_rho_I(target, p):
    z = np.linspace(-8, 8, 4001); w = norm.pdf(z); w /= w.sum()
    def f(r):
        pi = norm.cdf((norm.ppf(p) - np.sqrt(r) * z) / np.sqrt(1 - r))
        return ((pi ** 2 * w).sum() - p ** 2) / (p * (1 - p)) - target
    return brentq(f, 1e-6, 0.999999)


def draw(sizes, rho):
    """Indicator families at the target level, one-factor Gaussian copula."""
    thr = norm.ppf(P)
    out = []
    for m in sizes:
        z = rng.standard_normal()
        g = np.sqrt(rho) * z + np.sqrt(1 - rho) * rng.standard_normal(m)
        out.append((g <= thr).astype(float))
    return out


def pair_naive(fams):
    c = np.array([f.sum() for f in fams]); m = np.array([len(f) for f in fams], float)
    delta = (c * (c - 1)).sum() / (m * (m - 1)).sum()
    p = np.concatenate(fams).mean()                      # point-weighted
    return (delta - p * p) / (p * (1 - p))


def pair_matched(fams):
    """Same delta_hat, but p_hat weighted by m_j(m_j-1) to match it."""
    c = np.array([f.sum() for f in fams]); m = np.array([len(f) for f in fams], float)
    w = m * (m - 1)
    delta = (c * (c - 1)).sum() / w.sum()
    p = (w * (c / m)).sum() / w.sum()                    # weight-matched
    return (delta - p * p) / (p * (1 - p))


rho = rho_for_rho_I(RHO_I, P)
ragged = np.array([len(f) for f in load()], dtype=int)
equal = np.full(len(ragged), int(round(ragged.mean())))
print("=" * 78)
print(f"ICC estimators against a known truth   rho_I = {RHO_I}  (score rho = {rho:.4f})")
print("=" * 78)
print(f"  ragged profile: b={len(ragged)}  m_bar={ragged.mean():.2f}  "
      f"CV^2={(ragged.astype(float)**2).sum()/ragged.sum()/ragged.mean()-1:.3f}")

res = {}
for label, sizes in (("EQUAL sizes", equal), ("RAGGED (released)", ragged)):
    est = {"A anova": [], "B pair naive": [], "C pair matched": []}
    for _ in range(REPS):
        fams = draw(sizes, rho)
        est["A anova"].append(anova_icc(fams))
        est["B pair naive"].append(pair_naive(fams))
        est["C pair matched"].append(pair_matched(fams))
    res[label] = {k: np.array(v) for k, v in est.items()}
    print(f"\n  {label}")
    print(f"    {'estimator':16s} {'mean':>8s} {'bias':>9s} {'sd':>8s} {'>1 or <0':>9s}")
    for k, v in res[label].items():
        bad = int(((v > 1) | (v < 0)).sum())
        print(f"    {k:16s} {v.mean():8.4f} {v.mean()-RHO_I:+9.4f} {v.std(ddof=1):8.4f} {bad:9d}")

print()
eq = res["EQUAL sizes"]; rg = res["RAGGED (released)"]
p1 = all(abs(eq[k].mean() - RHO_I) < 0.02 for k in eq)
print(f"  P1  all three near-unbiased at EQUAL sizes                : {'PASS' if p1 else 'FAIL'}")
p2 = abs(rg["B pair naive"].mean() - RHO_I) > abs(rg["A anova"].mean() - RHO_I)
print(f"  P2  B is worse than A on ragged sizes (documented reason) : {'PASS' if p2 else 'FAIL'}")
relA = (rg["A anova"].mean() - RHO_I) / RHO_I
# P3 REVISED 2026-07-31. It used to assert SW-24's "A runs ~10% low on this profile"
# (-0.16 < relA < -0.04) and had been printing FAIL on every run since 2026-07-30, when that
# finding was traced to three realisations and retracted (integrity.md, SW-24 sub-findings).
# The paper now prints the measured statement -- unbiased in mean, a fifth wider in spread -- so
# the precondition asserts THAT, and can still fail: a drift of more than 2% in either direction
# would break §8's recommendation to use the ANOVA form.
p3 = abs(relA) < 0.02
print(f"  P3  A is unbiased on the released profile, |bias| < 2% (got {relA:+.1%}) : "
      f"{'PASS' if p3 else 'FAIL'}")
print()
print("  READING")
for k, v in rg.items():
    print(f"    {k:16s} {(v.mean()-RHO_I)/RHO_I:+7.1%} bias, sd {v.std(ddof=1):.4f}")
