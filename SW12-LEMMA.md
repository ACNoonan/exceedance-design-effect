# SW-12: the uniform lattice Edgeworth lemma, written out

**Status: an argument, not yet a referee-grade proof.** Every step is here, every constant
is tracked, and as of the 2026-07-30 revision **every source it leans on has been read in
full** — Part A's estimate moved from an unobtainable textbook to [dolgopyathafouta2020],
which is on the shelf. What it still lacks is a check by someone other than its author, and
it is fixed-$m$. Do not move it into the paper as a theorem on that basis alone. What it is good for now: it fixes exactly what must
be proved, it shows the obstruction §10 named has dissolved, and every quantitative
claim in it has a script behind it.

Written 2026-07-30. Companions: `sw12_uniform_nondegeneracy.py` (step 1),
`sw12_lattice_edgeworth.py` (step 2), `sawtooth_fourier.py` (the suppression estimate
used in Part B), `edgeworth_terms.py` (the integration argument this lemma feeds).

---

## 1. What is being proved, and why §10 needs it

§10 writes the mean coverage as $\mathbb{E}[C] = \int_0^1 \mathbb{P}(N(t) \le k-1)\,\mathrm{d}t$
and needs a pointwise expansion of the integrand whose remainder is $o(b^{-1/2})$
**uniformly in $t$**. Uniformity is the whole difficulty: the integrand is a different
law at every level, and the integral does not care about any single one of them.

Fix a compact window $T = [p-\delta,\, p+\delta] \subset (0,1)$. For $t \in T$ let

$$X(t) \;=\; \#\{i \le m : S_i \le q_t\} \;\in\; \{0,1,\dots,m\}$$

be one cluster's exceedance count, $X_1(t),\dots,X_b(t)$ i.i.d. copies, and
$N_b(t) = \sum_{j\le b} X_j(t)$. Write $\mu(t) = mt$, $\sigma^2(t) = \operatorname{Var}X(t)$,
$\gamma(t) = \mu_3(t)/\sigma^3(t)$, and $\phi_t(\theta) = \mathbb{E}e^{i\theta X(t)}$.

> **Lemma (uniform lattice Edgeworth at the CDF level).** Assume
> **(H1)** $\inf_{t\in T}\rho_I(t) > -1/(m-1)$, and
> **(H2)** for every $t \in T$ the law of $X(t)$ has maximal span 1.
> Then there is $C = C(m, \sigma_-^2, \kappa)$, not depending on $b$, $t$ or $x$, with
> $$\sup_{t \in T}\ \sup_{x \in \mathbb{R}}\ \Bigl|\,\mathbb{P}\bigl(N_b(t) \le x\bigr) - \tilde F_{b,t}(x)\,\Bigr| \;\le\; \frac{C}{b},$$
> $$\tilde F_{b,t}(x) \;=\; \Phi(z) \;-\; \frac{\gamma(t)}{6\sqrt b}\,(z^2-1)\,\varphi(z) \;+\; \frac{Q_1(x)}{\sigma(t)\sqrt b}\,\varphi(z),$$
> $$z = \frac{x - b\mu(t)}{\sigma(t)\sqrt b}, \qquad Q_1(y) = \lfloor y \rfloor - y + \tfrac12 .$$

$O(b^{-1})$ is an order better than the $o(b^{-1/2})$ §10 asks for. That surplus is
bought by $0 \le X \le m$: all moments exist and are bounded by powers of $m$.

**The sign on $Q_1$ is the one place a plausible write-up goes wrong.** With the
opposite sign, `sw12_lattice_edgeworth.py` measures the error decaying at $b^{-0.50}$ —
identical to omitting the term. Two independent confirmations of $+Q_1$: the
measurement, and the continuity correction, since at integer $x$ we have $Q_1 = 1/2$ and
the term reduces to $\Phi\bigl(z + \tfrac{1}{2\sigma\sqrt b}\bigr) - \Phi(z)$ to first
order. My first pass at Part B below produced $-Q_1$ and was wrong.

---

## 2. What step (1) supplies

Proved in §10 and verified in `sw12_uniform_nondegeneracy.py`:

- **(V)** $\sigma^2(t) = m\,t(1-t)\,[\,1 + (m-1)\rho_I(t)\,]$ — the summand variance *is*
  $m t(1-t)$ times the design effect. So (H1) is exactly "the design effect is bounded
  away from zero", and $\rho_I \ge 0$ gives it free.
- $t \mapsto \pi(t) = (\mathbb{P}(X(t)=j))_{j\le m}$ is Lipschitz with a constant depending
  only on $m$, because each $\pi_j$ is a finite combination of copula diagonals and every
  copula is 1-Lipschitz per argument. Hence $\pi(T)$ is **compact** in the simplex.
- Therefore, by continuity + compactness, both are **attained** and so uniform:
  $$\sigma_-^2 := \inf_{t\in T}\sigma^2(t) > 0, \qquad
    \sup_{t\in T}\ \sup_{\eta \le |\theta| \le \pi} |\phi_t(\theta)| \;\le\; 1-\kappa(\eta) < 1 .$$
- Trivially $|X| \le m$, so $|\mu_3| \le m^3$ and every cumulant is bounded by a constant
  times a power of $m$.

(H1) fails only at the Fréchet lower bound $\rho_I = -1/(m-1)$; (H2) fails only when the
count sits on a proper sublattice, i.e. at the comonotone cluster, supported on $\{0,m\}$.
Both are endpoints the paper already excludes, and the script *refuses* both as negative
controls rather than certifying them.

**The one estimate that is neither proved above nor classical, so it is measured.**
Part A needs a single $\eta$, serving every $t \in T$, with
$$|\phi_t(\theta)| \;\le\; e^{-\sigma^2(t)\theta^2/4} \qquad (|\theta| \le \eta).$$
`sw12_lattice_edgeworth.py` P7 finds the largest admissible $\eta$ at each of 25 levels
and reports the smallest: $\eta = 1.287$, attained at $t = 0.912$, on the window
$[0.80, 0.98]$ at $m = 4$. Bounded well away from $0$. A failure here — $\eta \to 0$
somewhere in the window — would break Part A's uniformity, and is what a near-degenerate
summand law would produce.

---

## 3. Part A — the local expansion, uniformly in $t$

**There is no triangular array here, and that is the point.** At fixed $m$ and fixed $t$
the clusters are i.i.d., so $N_b(t)$ is a classical i.i.d. lattice sum. The family is
indexed by $t$, but each member is an ordinary sum. This is why [bock2014]'s Lemma
4.12(i) — proved along a *single convergent sequence* $V_n \to V$ — was the wrong thing
to extend: we never needed an array theorem, only a theorem whose constants we can see.
(The result Part A ends up citing *does* cover arrays. That is incidental here — we use it
at fixed $m$, where each row is i.i.d. — but see the lead at the end of §5, since it is
exactly what a ragged-size version would need.)

Since $N_b$ is integer-valued, Fourier inversion on the circle is exact:
$$\mathbb{P}(N_b = k) \;=\; \frac{1}{2\pi}\int_{-\pi}^{\pi} \phi_t(\theta)^b\, e^{-ik\theta}\,\mathrm{d}\theta .$$
Substitute $\theta = u/(\sigma\sqrt b)$ and let $\psi_{b,t}(u)$ be the characteristic
function of the standardised sum, $z_k = (k - b\mu)/(\sigma\sqrt b)$:
$$\sigma\sqrt b\;\mathbb{P}(N_b = k) \;=\; \frac{1}{2\pi}\int_{|u| \le \pi\sigma\sqrt b} \psi_{b,t}(u)\, e^{-i z_k u}\,\mathrm{d}u .$$

Split at $|u| = \eta\,\sigma\sqrt b$.

**Outer range, $\eta \le |\theta| \le \pi$.** Here $|\psi_{b,t}(u)| = |\phi_t(\theta)|^b \le (1-\kappa)^b$
by step (1), and the range has length at most $2\pi\sigma\sqrt b \le 2\pi m \sqrt b$. So the
outer contribution is at most $m\sqrt b\,(1-\kappa)^b$, which is $o(b^{-r})$ for every $r$,
**uniformly in $t$ because $\kappa$ is uniform**. This is the step that would have needed
an array argument and instead needs only compactness.

**Inner range, $|\theta| \le \eta$.** Standard from here. $\log\phi_t$ admits a third-order
expansion with cumulants bounded by powers of $m$; $\sigma^2 \ge \sigma_-^2$ keeps the
standardisation from degenerating; and §2's measured $\eta$ gives the Gaussian domination
$|\psi_{b,t}(u)| \le e^{-u^2/4}$ needed to integrate the remainder. One obtains
$$\int_{|u| \le \eta\sigma\sqrt b} \Bigl|\, \psi_{b,t}(u) - e^{-u^2/2}\bigl(1 + \tfrac{\gamma}{6\sqrt b}(iu)^3\bigr)\Bigr|\,\mathrm{d}u \;\le\; \frac{C_1}{b},$$
with $C_1 = C_1(m, \sigma_-, \eta)$ — every input to the classical constant is one of the
three quantities step (1) bounded uniformly, so $C_1$ does not depend on $t$. Inverting,
$$\sigma\sqrt b\;\mathbb{P}(N_b = k) \;=\; \varphi(z_k) + \frac{\gamma}{6\sqrt b}\,\mathrm{He}_3(z_k)\,\varphi(z_k) + O(b^{-1}),$$
uniformly in $k \in \mathbb{Z}$ and $t \in T$.

*This is the step stated rather than re-derived, and the source changed on 2026-07-30.*
It was first cited to Petrov, *Sums of Independent Random Variables*, Ch. VII — which we
could not obtain (both editions in copyright; archive.org access-restricted, publishers
paywalled), and whose own notation page warns that unadorned constants "may stand for
different values", so a bare $C$ there carries no declared dependence. **Part A now cites
[dolgopyathafouta2020] Theorem 1.4 / 11.1 instead, which is read in full**, and which is a
better fit than the textbook was:

- It is a **local** expansion for $\mathbb{P}(S_N = k)$, "uniformly in $k \in \mathbb{Z}$" — exactly
  Part A's object. §10 previously set this paper aside because it has no CDF version; that
  objection dissolved when the lemma was split, because Part B supplies the CDF conversion
  ourselves.
- Its constants are **$J = J(K)$ and $R = R(r,K)$ with $K = \sup_j\|X_j\|_{L^\infty}$** — a
  function of the sup-bound and the expansion order alone. Here $K = m$ at every level.
- It is stated for **independent, not identically distributed, uniformly bounded
  integer-valued** summands, and explicitly "in the arrays setup".

Their hypothesis is $M_N := \min_{2 \le h \le 2K}\sum_n \mathbb{P}(X_n \not\equiv m_n(h) \bmod h) \ge R\ln V_N$,
which is a **quantified form of (H2)**: maximal span with a rate. For an i.i.d. row this is
$M_b = b\,\varepsilon(t)$ with
$\varepsilon(t) = \min_{2\le h\le 2m}\bigl[1 - \max_c \mathbb{P}(X(t) \equiv c \bmod h)\bigr]$,
and step (1)'s compactness bounds it below uniformly. Measured (P8): $\varepsilon_- = 0.047$
on $[0.80, 0.98]$ at $m = 4$, attained at $t = 0.98$; the comonotone negative control returns
$0$ exactly, as it must. Since $V_b \le b m^2$, the condition reads $0.047\,b \ge R\ln(bm^2)$ —
linear against a logarithm — so it holds for every $b$ past a threshold depending on
$(m, r, \varepsilon_-)$ and **not on $t$**. That is the uniformity Part A needs, and it comes
from a fully-read source rather than an assertion about a constant we never saw.

---

## 4. Part B — from local to CDF, and where the sawtooth comes from

Let $h(y)$ be the smooth interpolant of the local expansion, $h(y) = \frac{1}{\sigma\sqrt b}g(z_y)$
with $g = \varphi + \frac{\gamma}{6\sqrt b}\mathrm{He}_3\varphi$. Let $\psi(y) = \tfrac12 - \{y\} = Q_1(y)$,
the mean-zero sawtooth, whose distributional derivative is $\psi'(y) = -1 + \sum_{k\in\mathbb{Z}}\delta_k(y)$.
Then
$$\int_{-\infty}^{x}\psi'(y)\,h(y)\,\mathrm{d}y \;=\; \sum_{k \le x} h(k) \;-\; \int_{-\infty}^{x} h(y)\,\mathrm{d}y,$$
and integrating the left side by parts,
$$\boxed{\ \sum_{k\le x} h(k) \;=\; \int_{-\infty}^{x} h(y)\,\mathrm{d}y \;+\; Q_1(x)\,h(x) \;-\; \int_{-\infty}^{x} Q_1(y)\,h'(y)\,\mathrm{d}y.\ }$$

The three terms are, in order: $\Phi(z) + \text{skewness}$; the **sawtooth term**
$+\dfrac{Q_1(x)}{\sigma\sqrt b}\varphi(z)$, with the sign the measurement independently
confirms; and a remainder.

**The remainder is where the naive bound fails and an existing lane result rescues it.**
Crudely, $\int|h'| = O(b^{-1/2})$ — the same order as the drift being computed, so a
modulus bound is useless. What saves it is oscillation: $Q_1$ has mean zero and period 1,
while $h'$ varies on scale $\sigma\sqrt b$. Expanding
$Q_1(y) = \sum_{j\ge1}\frac{\sin(2\pi j y)}{\pi j}$ and integrating each mode against the
Gaussian-derivative envelope of width $\sigma_b = \sigma\sqrt b$ produces
$$\exp\bigl(-2\pi^2 j^2 \sigma_b^2\bigr),$$
which is the estimate `sawtooth_fourier.py` already computes — at $n = 1600$ it is
$e^{-5386}$, below double precision. That script was written while diagnosing an unrelated
quadrature artefact; the suppression it found is exactly the estimate this remainder needs.

Combining Parts A and B, and absorbing the outer-range and remainder contributions into
$C/b$, gives the Lemma. $\blacksquare$

---

## 5. What the argument does **not** cover

1. **Fixed $m$ only.** Ragged cluster sizes restore a genuine triangular array — the
   summands are then non-identically distributed — and Part A's reduction to a classical
   i.i.d. theorem is unavailable. §7's $\tilde m$ substitution is not covered by this lemma.
2. **Part A is cited, not re-derived.** Its source is now read in full, so this is an
   ordinary citation rather than a debt — but the composition of their local theorem with
   our Part B has not been checked by anyone else.
3. **$T$ must be compact and inside $(0,1)$.** §10's tail argument, which is separate,
   handles the levels outside the window by exponential smallness of the cluster counts.
4. **The constant degrades toward the tail.** Measured: the sup error at $b = 1600$ grows
   tenfold from $t = 0.80$ to $t = 0.98$ while the *rate* holds at $b^{-1.02}$. Step (1)
   independently finds $\sigma_-^2$ and $\kappa$ smallest at $t = 0.98$ — two calculations
   written for different purposes agreeing on which end is hard. Any explicit $C$ will
   therefore blow up as $\delta$ grows to reach $t = 1$.

## 6. Depth register

| source | role | depth |
|---|---|---|
| [esseen1945] | the lattice correction and its Fourier modes | `full` — on the shelf, read in lane |
| [bock2014] | the array route, **shown unnecessary** here | `full` — Lemma 4.12(i) read directly |
| [dolgopyathafouta2020] | uniform *local* expansion, constants in $K$ and order | `full` |
| [kolassamccullagh1990] | Bhattacharya–Rao CDF form, no uniformity | `full` |
| [dolgopyathafouta2020] Thm 1.4 / 11.1 | **Part A's local estimate, as of 2026-07-30** | `full` — on the shelf; hypothesis and constants verified in-lane against the artifact |
| Petrov, *Sums of Independent Random Variables* | the route first tried, now **abandoned** | `snippet` — not obtainable (in copyright; archive.org access-restricted, publishers paywalled). Ch. VI is the CLT expansions chapter and Ch. VII the local ones, so the original citation pointed at the right chapter for a local estimate. Front matter and two Ch. VI page images only, at `papers/pdfs/petrov-1975-*`; **no theorem read**, so nothing is cited to it |

`sw12_uniform_nondegeneracy.py` P0–P5 and `sw12_lattice_edgeworth.py` P1–P8 all pass,
including five negative controls that must and do fail: the Fréchet lower bound, the
comonotone cluster (twice — once on $\kappa$, once on $\varepsilon$), and deletion of each of
the two correction terms.

**A lead not pursued.** [dolgopyathafouta2020] covers *independent, not identically
distributed* bounded integer summands. Ragged cluster sizes are exactly that — $X_j$ bounded
by $\max_j m_j$ — so limitation 1 above may be removable through the same citation. Not
claimed: the ragged case also changes the estimand via §7's $\tilde m$ substitution, and that
is a separate argument from the expansion.
