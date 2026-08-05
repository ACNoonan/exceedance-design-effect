"""SW-02 — build every figure in the paper.

    python experiments/2026-07-26-sw02-exchangeability-audit/paper/build_figures.py

Writes PDF (for LaTeX) and PNG (for preview) into paper/figures/.

Figures are regenerated from the SAME verified numbers as the tables, computed here rather than
hard-coded wherever the computation is cheap; the two expensive ones (the PRM measurement and the
empirical dose-response) are read from constants recorded alongside their source scripts, because
one needs a 33 MB download and the other lives on a substrate outside this repo.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from scipy.stats import beta as beta_dist, multivariate_normal, norm  # noqa: E402

from _conformal import split_conformal  # noqa: E402

OUT = Path(__file__).resolve().parent / "figures"
OUT.mkdir(exist_ok=True)

plt.rcParams.update({
    "font.size": 8.5, "axes.labelsize": 8.5, "axes.titlesize": 9,
    "xtick.labelsize": 7.5, "ytick.labelsize": 7.5, "legend.fontsize": 7.5,
    "axes.spines.top": False, "axes.spines.right": False,
    "figure.dpi": 150, "savefig.bbox": "tight", "lines.linewidth": 1.4,
})
INK, ACC, WARN, MUTE = "#1a1a1a", "#2166ac", "#b2182b", "#999999"

N_FAM, M, ALPHA, N = 50, 4, 0.10, 200
K = int(np.ceil((N + 1) * (1 - ALPHA)))
P = K / (N + 1)


def rho_I(p, r):
    if r >= 1.0:
        return 1.0
    if r <= 0.0:
        return 0.0
    z = norm.ppf(p)
    d = float(multivariate_normal(mean=[0, 0], cov=[[1, r], [r, 1]]).cdf([z, z]))
    return (d - p * p) / (p * (1 - p))


def save(fig, stem):
    for ext in ("pdf", "png"):
        fig.savefig(OUT / f"{stem}.{ext}")
    plt.close(fig)
    print(f"  wrote figures/{stem}.pdf|.png")


# ---------------------------------------------------------------- fig 1
def fig1_law():
    """The law vs the naive rival, and the coverage distribution it implies."""
    rhos = np.array([0.0, 0.2, 0.4, 0.6, 0.8, 0.95, 1.0])
    sd_sim = np.array([0.0212, 0.0234, 0.0265, 0.0299, 0.0341, 0.0388, 0.0414])
    ri = np.array([rho_I(P, r) for r in rhos])
    sd_law = np.sqrt(P * (1 - P) / (N / (1 + (M - 1) * ri)))
    sd_naive = np.sqrt(P * (1 - P) / (N / (1 + (M - 1) * rhos)))

    fig, ax = plt.subplots(1, 2, figsize=(7.0, 2.7))
    ax[0].plot(rhos, sd_sim, "o", color=INK, ms=5, label="simulated", zorder=3)
    ax[0].plot(rhos, sd_law, "-", color=ACC, label=r"law: $\rho_I(p)$ (exceedances)")
    ax[0].plot(rhos, sd_naive, "--", color=WARN, label=r"naive: $\rho$ (scores)")
    ax[0].set_xlabel(r"within-family score correlation $\rho$")
    ax[0].set_ylabel("sd of coverage")
    ax[0].set_title("(a)  the exceedance design effect")
    ax[0].legend(frameon=False, loc="upper left")

    for r, style, lab in ((0.0, "-", r"$\rho=0$  ($n_{\rm eff}=200$)"),
                          (0.6, "--", r"$\rho=0.6$  ($n_{\rm eff}=102$)"),
                          (1.0, ":", r"$\rho=1$  ($n_{\rm eff}=50$)")):
        ne = N / (1 + (M - 1) * rho_I(P, r))
        nu = ne - 1
        d = beta_dist(P * nu, (1 - P) * nu)
        x = np.linspace(0.78, 0.99, 600)
        ax[1].plot(x, d.pdf(x), style, color=INK if r == 0 else (ACC if r == 0.6 else WARN),
                   label=lab)
    ax[1].axvline(P, color=MUTE, lw=1, ls="-", zorder=0)
    ax[1].text(P, ax[1].get_ylim()[1] * 0.96, " nominal", color=MUTE, fontsize=7, va="top")
    ax[1].set_xlabel("coverage realised by one deployment")
    ax[1].set_ylabel("density")
    ax[1].set_title("(b)  same mean, wider draw")
    ax[1].legend(frameon=False)
    fig.tight_layout()
    save(fig, "fig1_law")


# ---------------------------------------------------------------- fig 2
def fig2_level():
    """rho_I attenuates, and attenuates more in the tail."""
    rr = np.linspace(0, 1, 121)
    fig, ax = plt.subplots(1, 2, figsize=(7.0, 2.7))
    for p, col, ls in ((0.50, MUTE, ":"), (0.90, INK, "-"),
                       (0.95, ACC, "--"), (0.99, WARN, "-.")):
        ax[0].plot(rr, [rho_I(p, r) for r in rr], ls, color=col, label=f"$p={p:g}$")
    ax[0].plot(rr, rr, color=MUTE, lw=0.8, alpha=0.6)
    ax[0].text(0.72, 0.79, "$\\rho_I=\\rho$", color=MUTE, fontsize=7, rotation=38)
    ax[0].set_xlabel(r"score correlation $\rho$")
    ax[0].set_ylabel(r"exceedance correlation $\rho_I(p)$")
    ax[0].set_title("(a)  exceedances are less correlated than scores")
    ax[0].legend(frameon=False, loc="upper left")

    ps = np.linspace(0.55, 0.995, 120)
    for r, col, ls in ((0.3, MUTE, ":"), (0.6, INK, "-"), (0.9, WARN, "--")):
        ax[1].plot(ps, [1 + (M - 1) * rho_I(p, r) for p in ps], ls, color=col,
                   label=fr"$\rho={r:g}$")
    for p, lab in ((0.90, "90%"), (0.95, "95%"), (0.99, "99%")):
        ax[1].plot([p], [1 + (M - 1) * rho_I(p, 0.6)], "o", color=INK, ms=4, zorder=3)
        ax[1].annotate(lab, (p, 1 + (M - 1) * rho_I(p, 0.6)),
                       textcoords="offset points", xytext=(3, 5), fontsize=7)
    ax[1].set_xlabel("target coverage level $p$")
    ax[1].set_ylabel("design effect  $1+(\\tilde m-1)\\rho_I(p)$")
    ax[1].set_title("(b)  weakest where thresholds are set")
    ax[1].legend(frameon=False, loc="lower left")
    fig.tight_layout()
    save(fig, "fig2_level_dependence")


# ---------------------------------------------------------------- fig 3
def fig3_ragged():
    """Ragged families: the size-biased mean is the right statistic."""
    names = ["equal\n$m{=}4$", "mild\n{3,4,5}", "ragged\n{1,2,4,9}", "beam-like"]
    m_bar = np.array([4.00, 3.98, 4.00, 3.76])
    m_til = np.array([4.00, 4.15, 6.38, 8.53])
    sd_sim = np.array([0.0339, 0.0344, 0.0397, 0.0467])
    sd_til = np.array([0.0335, 0.0341, 0.0391, 0.0466])
    sd_bar = np.array([0.0335, 0.0336, 0.0322, 0.0330])
    x = np.arange(len(names))
    fig, ax = plt.subplots(1, 2, figsize=(7.0, 2.7))
    ax[0].bar(x - 0.2, m_bar, 0.4, color=MUTE, label=r"$\bar m$ (average)")
    ax[0].bar(x + 0.2, m_til, 0.4, color=ACC, label=r"$\tilde m$ (size-biased)")
    ax[0].set_xticks(x); ax[0].set_xticklabels(names)
    ax[0].set_ylabel("family size statistic")
    ax[0].set_title("(a)  ragged families are bigger than they look")
    ax[0].legend(frameon=False)

    ax[1].plot(x, sd_sim, "o", color=INK, ms=6, label="simulated", zorder=3)
    ax[1].plot(x, sd_til, "-", color=ACC, label=r"predicted from $\tilde m$")
    ax[1].plot(x, sd_bar, "--", color=WARN, label=r"predicted from $\bar m$")
    ax[1].set_xticks(x); ax[1].set_xticklabels(names)
    ax[1].set_ylabel("sd of coverage")
    ax[1].set_title("(b)  the average family size understates it")
    ax[1].legend(frameon=False)
    fig.tight_layout()
    save(fig, "fig3_ragged")


# ---------------------------------------------------------------- fig 4
def fig4_prm():
    """Measured on the released PRM calibration set.

    Right panel updated 2026-07-27 (SW-24): the headline n_eff is now the MEASURED one from the
    cluster bootstrap (`prm_dispersion.py`: dispersion ratio 4.4x tie-broken -> n_eff ~ 1,293),
    with the plug-in n_eff = 812 kept beside it to show the over-correction under informative
    sizes. Constants recorded here; sources prm_measurement.py + prm_dispersion_RESULTS.txt.
    """
    thr = np.array([0.000, 0.125, 0.250, 0.375, 0.500, 0.625, 0.750, 0.875])
    cov = np.array([0.6744, 0.7639, 0.8062, 0.8342, 0.8553, 0.8737, 0.8909, 0.9145])
    ricc = np.array([0.4355, 0.5007, 0.5254, 0.5367, 0.5307, 0.5177, 0.4946, 0.4274])
    n_tot = 25028
    neff_measured = round(n_tot / 4.4 ** 2)      # 1,293: measured ratio, ties broken
    neff_plugin = 812                            # 1 + (m_til - 1) rho_I at p = 0.891

    fig, ax = plt.subplots(1, 2, figsize=(7.0, 2.7))
    ax[0].plot(cov, ricc, "o-", color=ACC, ms=4)
    ax[0].axhline(0.5986, color=WARN, ls="--", lw=1)
    ax[0].text(0.68, 0.607, "score ICC = 0.599", color=WARN, fontsize=7)
    ax[0].set_xlabel("coverage level $p$ (achievable)")
    ax[0].set_ylabel(r"$\rho_I(p)$ measured")
    ax[0].set_title("(a)  exceedance vs score correlation, real data")

    ax[1].bar([0], [n_tot], 0.5, color=MUTE)
    ax[1].bar([1], [neff_measured], 0.5, color=ACC)
    ax[1].bar([2], [neff_plugin], 0.5, color=WARN)
    ax[1].set_yscale("log")
    ax[1].set_xticks([0, 1, 2])
    ax[1].set_xticklabels(["$n$", "$n_{\\rm eff}$\nmeasured", "$n_{\\rm eff}$\nplug-in"])
    ax[1].set_ylabel("calibration points (log scale)")
    ax[1].set_title("(b)  25,028 points carry ~1,300 (measured)")
    for xi, v in ((0, n_tot), (1, neff_measured), (2, neff_plugin)):
        ax[1].annotate(f"{v:,}", (xi, v), textcoords="offset points",
                       xytext=(0, 4), ha="center", fontsize=8)
    fig.tight_layout()
    save(fig, "fig4_prm")


# ---------------------------------------------------------------- fig 5
def fig5_selection():
    """Selection on score: informative cluster sizes break coverage at first order.

    Single panel since 2026-07-27. This was a 1x2 whose right panel plotted the FT-17 companion
    study's dose-response slopes; that material left the paper when the companion section was cut,
    so plotting it here would illustrate a claim the text no longer makes.
    """
    fig, ax = plt.subplots(figsize=(4.2, 2.9))
    labels = ["independent", "large fams\nscore HIGH", "large fams\nscore LOW"]
    shift = np.array([-0.48, 6.54, -18.10])
    ax.bar(range(3), shift, 0.55, color=[MUTE, ACC, WARN])
    ax.axhline(0, color=INK, lw=0.8)
    ax.set_xticks(range(3)); ax.set_xticklabels(labels)
    ax.set_ylabel("coverage shift (percentage points)")
    ax.set_title("informative sizes: a first-order break")
    ax.annotate("for scale: the design effect\nmoves the mean by < 1 pp",
                xy=(0.5, -12.5), fontsize=7, ha="center", color=MUTE)
    fig.tight_layout()
    save(fig, "fig5_selection")


if __name__ == "__main__":
    print("building figures ->", OUT)
    fig1_law(); fig2_level(); fig3_ragged(); fig4_prm(); fig5_selection()
    print("done")
