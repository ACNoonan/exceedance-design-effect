"""SW-02 — ragged family sizes, and how well rho_I can be estimated in practice.

    python experiments/2026-07-26-sw02-exchangeability-audit/ragged_and_estimation.py

Runs today via `experiments/_conformal.py` (research copy of split_conformal, asserted
equivalent to calkit's once L2 lands).

PART A — RAGGED FAMILIES
Cluster j has size m_j. Because clusters are independent,
    Var N(t) = sum_j m_j t(1-t)[1 + (m_j - 1) rho_I(t)]
             = n t(1-t) [ 1 + (m_tilde - 1) rho_I(t) ],    m_tilde = sum m_j^2 / sum m_j.

So Theorem 1 and Proposition 1 hold verbatim with m replaced by the SIZE-BIASED mean cluster
size m_tilde. Since m_tilde = m_bar (1 + CV^2) >= m_bar, ragged families are strictly worse
than equal families of the same mean size, and the naive m_bar can be badly optimistic.

This matters for the paper's live instance: beam search kills branches at different depths, so
surviving families are highly ragged. A beam-like size profile with m_bar = 3.76 has
m_tilde = 8.53 — using m_bar understates the coverage sd by ~30%.

PART B — ESTIMATING rho_I
The recommendation is to estimate delta(p) as the fraction of same-cluster PAIRS with both
members below the conformal threshold. It needs no distributional assumption, but it is a
proportion over sum_j C(m_j, 2) dependent pairs against a data-estimated threshold, so it is
worth knowing its bias and spread before recommending it. Both are measured here.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from scipy.optimize import brentq
from scipy.stats import multivariate_normal, norm

# calkit/ and _conformal.py sit at the code-archive root; in the paper's working
# tree they are vendored under external/. Cover both layouts.
_HERE = Path(__file__).resolve().parent
for _p in (_HERE.parent / "external", _HERE.parent, _HERE / "external", _HERE):
    sys.path.insert(0, str(_p))
from _conformal import split_conformal  # noqa: E402

ALPHA = 0.10
CHUNK = 5_000


def rho_I(p: float, r: float) -> float:
    if r >= 1.0:
        return 1.0
    if r <= 0.0:
        return 0.0
    z = norm.ppf(p)
    d = float(multivariate_normal(mean=[0, 0], cov=[[1, r], [r, 1]]).cdf([z, z]))
    return (d - p * p) / (p * (1 - p))


def rho_I_prime(p: float, r: float, h: float = 1e-4) -> float:
    return (rho_I(p + h, r) - rho_I(p - h, r)) / (2 * h)


def solve_r(target: float, p: float) -> float:
    return brentq(lambda r: rho_I(p, r) - target, 1e-6, 1 - 1e-9, xtol=1e-12)


def m_tilde(sizes) -> float:
    s = np.asarray(sizes, dtype=float)
    return float((s ** 2).sum() / s.sum())


def simulate_ragged(sizes, r, alpha=ALPHA, reps=60_000, seed=0):
    sizes = np.asarray(sizes, dtype=int)
    b, n = len(sizes), int(sizes.sum())
    k = int(np.ceil((n + 1) * (1 - alpha)))
    p = k / (n + 1)
    idx = np.repeat(np.arange(b), sizes)
    rng = np.random.default_rng(seed)
    tot = tot2 = 0.0
    done = 0
    while done < reps:
        c = min(CHUNK, reps - done)
        anc = rng.normal(size=(c, b))[:, idx]
        own = rng.normal(size=(c, n))
        s = np.sqrt(r) * anc + np.sqrt(1 - r) * own
        cov = np.array([norm.cdf(split_conformal(row, alpha)) for row in s])
        tot += cov.sum()
        tot2 += (cov ** 2).sum()
        done += c
    mean = tot / reps
    sd = np.sqrt(max(tot2 / reps - mean ** 2, 0.0))
    return mean, sd, mean - p, sd / np.sqrt(reps), p, n


PATTERNS = {
    "equal m=4":        [4] * 50,
    "mild {3,4,5}":     ([3, 4, 5] * 17)[:50],
    "ragged {1,2,4,9}": ([1, 2, 4, 9] * 13)[:52],
    "beam-like":        [1] * 20 + [2] * 12 + [4] * 8 + [8] * 6 + [16] * 4,
}


def part_a() -> None:
    r = solve_r(0.5, 0.9)
    print(f"\n[A] RAGGED FAMILIES — Gaussian r={r:.4f} (rho_I(0.9)=0.500)\n")
    print(f"{'pattern':>18} {'b':>4} {'n':>5} {'m_bar':>6} {'m_til':>6} {'CV^2':>6} "
          f"{'sd_sim':>7} {'sd(m_til)':>9} {'sd(m_bar)':>9} {'ratio':>6}")
    for name, sizes in PATTERNS.items():
        mean, sd, drift, se, p, n = simulate_ragged(sizes, r)
        mt, mb = m_tilde(sizes), float(np.mean(sizes))
        ri = rho_I(p, r)
        sd_t = np.sqrt(p * (1 - p) * (1 + (mt - 1) * ri) / n)
        sd_b = np.sqrt(p * (1 - p) * (1 + (mb - 1) * ri) / n)
        print(f"{name:>18} {len(sizes):>4} {n:>5} {mb:>6.2f} {mt:>6.2f} {mt/mb - 1:>6.2f} "
              f"{sd:>7.4f} {sd_t:>9.4f} {sd_b:>9.4f} {sd / sd_t:>6.3f}")
    print("\n    ratio = sd_sim/sd(m_tilde); ~1.00 means m_tilde is the right statistic.")

    print("\n    drift also transports:  n*drift = ((m_til-1)/2){p(1-p)rho_I' - (2p-1)rho_I}")
    print(f"{'pattern':>18} {'n':>5} {'n*drift':>9} {'pred(m_til)':>12} {'pred(m_bar)':>12}")
    for name, sizes in PATTERNS.items():
        mean, sd, drift, se, p, n = simulate_ragged(sizes, r, reps=200_000, seed=7)
        mt, mb = m_tilde(sizes), float(np.mean(sizes))
        core = p * (1 - p) * rho_I_prime(p, r) - (2 * p - 1) * rho_I(p, r)
        print(f"{name:>18} {n:>5} {drift * n:>+9.4f} {(mt - 1) / 2 * core:>+12.4f} "
              f"{(mb - 1) / 2 * core:>+12.4f}")


def part_b(reps: int = 4000) -> None:
    print("\n[B] ESTIMATING rho_I FROM SAME-CLUSTER PAIRS IN THE CALIBRATION SET\n")
    print(f"{'b':>5} {'m':>3} {'n':>6} {'pairs':>6} {'true':>6} {'mean_hat':>9} {'sd_hat':>7} "
          f"{'rel_sd':>7} {'n_eff':>7} {'n_eff_hat 5-95%':>18}")
    for b, m in ((25, 4), (50, 4), (200, 4), (1000, 4), (50, 8), (50, 2)):
        n = b * m
        k = int(np.ceil((n + 1) * (1 - ALPHA)))
        p = k / (n + 1)
        r = solve_r(0.5, p)
        rng = np.random.default_rng(0)
        est = np.empty(reps)
        for t in range(reps):
            anc = rng.normal(size=(b, 1))
            own = rng.normal(size=(b, m))
            s = np.sqrt(r) * anc + np.sqrt(1 - r) * own
            q = split_conformal(s.ravel(), ALPHA)
            cnt = (s <= q).sum(axis=1)
            d_hat = (cnt * (cnt - 1) / 2).sum() / (b * m * (m - 1) / 2)
            est[t] = (d_hat - p * p) / (p * (1 - p))
        true = rho_I(p, r)
        lo, hi = np.percentile(est, [5, 95])
        print(f"{b:>5} {m:>3} {n:>6} {b*m*(m-1)//2:>6} {true:>6.3f} {est.mean():>9.3f} "
              f"{est.std(ddof=1):>7.3f} {est.std(ddof=1)/true:>7.2f} "
              f"{n/(1+(m-1)*true):>7.1f} "
              f"{f'[{n/(1+(m-1)*hi):.0f}, {n/(1+(m-1)*lo):.0f}]':>18}")
    print("\n    Biased UPWARD at small b (threshold estimated from the same data), which")
    print("    understates n_eff — the conservative direction. Bias and spread both fall ~1/sqrt(b).")


def main() -> int:
    part_a()
    part_b()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
