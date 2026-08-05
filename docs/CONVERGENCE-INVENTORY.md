# The convergence inventory: who built which piece, and what their problem never required

**What this is.** The result decomposes into six ingredients. This file records, per field and per
work, which ingredients that work owns — each cell backed by a full read with a live positive
control, never by an impression. It is the evidence base for §7, and it is deliberately kept
separate from §7 so that a cell can be audited without reading prose around it.

**The rule that makes this section safe.** Every claim here is an absence claim, and absence claims
are where this programme has been hurt: four failed on 2026-07-30 alone (Deng and Yao own the
indicator construction; Patton owns the empirical estimator; Field & Welsh own the bootstrap
failure; Brennan & Lockwood own the crossed cut-score SE). So:

1. **A cell is only filled from a full read of the primary text**, with the artifact on disk.
2. **Every zero carries a positive control from the same file**, printed beside it. A count of zero
   for our term is evidence about the *word*, not the *object* — Patton's "quantile dependence" IS
   the copula literature's "tail concentration function", and a term scan on either name misses the
   other.
3. **Every claim is about a composition, not about awareness.** We never write that a field missed
   something. We write which ingredient its own problem did not require, which is both accurate and
   checkable.
4. **A cell that cannot meet 1–3 is left `—` (not assessed).** Empty cells are the work list, not
   a licence to guess.

---

## The six ingredients

| | ingredient | the sharp question |
|---|---|---|
| **P1** | the indicator | is the correlation computed on the *exceedance indicator* $\mathbf 1\{S\le q\}$, rather than on the underlying continuous score? |
| **P2** | a design effect on it | is $1+(m-1)\rho$, a variance inflation factor, or an $n_\text{eff}$ formed **from that indicator's** correlation? |
| **P3** | level-dependence | is the correlation parameter itself shown to move with the threshold level — stated, plotted, or measured at more than one level? |
| **P4** | an estimated threshold | is the threshold a **sample quantile of the same data it governs**, rather than fixed a priori? |
| **P5** | the distribution | is the realised coverage/error rate a **random variable with a law**, rather than a mean, a bound, or a standard error? |
| **P6** | ragged sizes | are unequal cluster sizes handled, e.g. by a size-biased $\tilde m$? |

---

## The table

`Y` owns it · `~` partial, see note · `N` verified absent with a live control · `—` not assessed

| field | representative work | P1 | P2 | P3 | P4 | P5 | P6 | depth |
|---|---|---|---|---|---|---|---|---|
| survey statistics | [kish1965] | **Y** | **Y** | N | **Y** | N | — | targeted, from full OCR |
| survey statistics | [korngraubard1998] | **Y** | **Y** | ~ | N | N | — | full (OCR) |
| cluster trials | [teerenstra2010] | ~ | **Y** | N | N | N | — | full |
| cluster trials | [moulton1986] | — | **Y** | — | N | N | **Y** | full |
| cluster trials (binary) | **[crespi2011]** | **Y** | **Y** | **Y** | N | N | — | full |
| epidemiology | **[katz1993]** | ~ | **Y** | N | N | N | **Y** | full |
| AI eval standards | [nistai8003] | ~ | **Y** | N | N | N | N | full |
| AI eval measurement | [miller2024] | N | N | N | N | N | ~ | full |
| diagnostic medicine | Obuchowski 1997 | — | — | — | — | — | — | **unobtainable** |
| psychometrics | [brennanlockwood1980] | N | **N** | N | ~ | N | n/a | full |
| cluster bootstrap | [fieldwelsh2007] | N | ~ | N | N | ~ | N (excluded) | full |
| copula theory | [venter2002] | **Y** | N | **Y** | N | N | N | full |
| copula theory | [durante2015] | **Y** | — | **Y** | — | — | — | partial |
| econometrics (copulas) | [patton2013] | **Y** | N | **Y** | ~ | N | N | full |
| econometrics (arrays) | [davezies2021] | **Y** | N | N | — | ~ | — | full |
| online experimentation | [deng2018] | **Y** | **Y** | N | **Y** | N | ~ | full |
| online experimentation | [yao2024] | **Y** | **Y** | N | **Y** | N | — | full |
| risk management | [christoffersen1998] | **Y** | N | ~ | ~ | **Y** | n/a | full |
| conformal (dependence) | [ramos2026] | **Y** | ~ | N | **Y** | **Y** | N | not full |
| conformal (weights) | [vejling2026] | N | **Y** | N | **Y** | **Y** | N | full |
| conformal (i.i.d.) | [sanchez2025] | **Y** | N | N | **Y** | **Y** | N | full |
| conformal (bounds) | [lin2022cptd] | ~ | N | N | **Y** | N | N | full |
| LLM outputs | [bay2026] | ~ | **Y** | N | N | N | — | full |
| finite-population inference | [meng2018] | N | ~ | N | N | N | n/a | full |

---

## The two nearest misses, and the fact that carries the section

**Online experimentation owns P1 + P2 + P4, composed and in production.** [deng2018] §4 builds
$Y_i = \mathbf 1\{X_i \le X_{(\lfloor np\rfloor)}\}$ himself and puts a clustered delta-method
variance on it to get a quantile confidence interval, deployed in Microsoft's ExP; [yao2024]
Algorithm 1 inherits it as a correction factor $c = \sigma_I/\sqrt{p(1-p)}$, which is
$\sqrt{\mathrm{DEFF}}$ on the indicator in all but name; GrowthBook ships it. What their problem
never required is P3: Deng's entire §4.3 evaluation sits at $p = 0.95$, Table 3 has no $p$ column,
and he presents the correction as "a simple re-scaling step". Yao reports $c$ at no second level and
carries no correlation parameter in which a level-dependence could be expressed.

**Copula theory and econometrics own P1 + P3, with an estimator and inference.** [venter2002] gives
$R(z) = [1-2z+C(z,z)]/(1-z)$ — the same pair-exceedance probability, as a curve in $z$;
[patton2013] eq. (15) gives its empirical plug-in, plots it across $q\in[0.025,0.975]$ with
bootstrap bands, and tests tail symmetry with a Wald statistic. What their problem never required is
P2: they are describing a dependence structure, not sizing a sample.

**The two halves do not touch, and this is checked in both directions with live controls:**

| in the online-experimentation texts | | in the copula/econometrics texts | |
|---|---|---|---|
| `copula` | **0** | `design effect` | **0** |
| `tail concentration` | **0** | `effective sample` | **0** |
| `quantile dependence` | **0** | `cluster` | **0** |
| `Venter` / `Patton` / `Durante` | **0** | `Kish` / `Deng` | **0** |
| *control* `quantile` | 41, 67 | *control* `copula` | 255, 459 |

Counts are occurrences (not lines) over [deng2018] and [yao2024], and over [venter2002] and
[patton2013], respectively.

**So the empty cell is not P1, P2, P3, P4 or P5 individually — every one of them is owned.** It is
the composition.

**Corrected 2026-07-30.** This previously read "no work in this table holds P2 and P3 together".
That was **false**, and [crespi2011] is the counterexample: the ICC of a binary outcome as a
closed-form function of its prevalence, eq. (5) `rho = (R-1)pi/(1-pi)`, composed with a design effect
and built into trial sample-size formulae. For a dichotomised outcome the prevalence *is* the level,
and since `R = delta(p)/p^2` their eq. (5) is `rho_I(p)` exactly — checked to 9e-15. The claim
survived because the search term was wrong: `threshold` and `level` return 0 in their text, while the
object sits under `prevalence`, which returns 56. Second same-object-different-name miss of the
session, after Patton's "quantile dependence".

**The unclaimed composition is narrower and must be stated as such: P3 with P4, priced as P5.** A
prevalence is a property of a population; nobody in trial design chooses it, so the level is never
coupled to a threshold estimated from the sample it governs, and no passage there reads the ICC at
two levels within one dataset. That coupling, and the dispersion it induces, is the paper.

---

## What each field's own problem did not require

This is the phrasing that goes in §7, and it is not a euphemism — in each case the missing
ingredient is genuinely irrelevant to the question that field was answering.

- **Survey statistics** sized estimates of *means and proportions of fixed events*. A threshold
  estimated from the sample it governs does not arise, so P3 and P4 have nothing to attach to.
- **Cluster trials** dichotomise by clinical definition, fixed in the protocol before data. The
  dichotomy cannot move with a level because there is no level.
- **Copula theory and econometrics** describe a dependence structure and select models. Nothing in
  copula selection asks how many independent observations a correlated sample is worth.
- **Online experimentation** reports one operating point per metric — the p95 or p99 an SLO names.
  Sweeping the level is not a question their product asks.
- **Conformal prediction** has P4 and P5 by construction, and treats every departure from
  exchangeability as *shift* — for which the field's own repair, weighted CP, is correct. Its
  vocabulary has a word for shift and none for dependence, which is §3's thesis.
- **Epidemiology** ([katz1993], added 2026-07-30) estimates design effects for a **disease
  prevalence** under one case definition fixed by protocol — "four or more loose stools per day",
  identically worded across four national surveys. A prevalence is a property of the population
  being surveyed, so there is nothing to sweep and P3 and P4 have nothing to attach to; the only
  sweep in the paper is over **cluster size**, at fixed prevalence and fixed pairwise odds ratio.
  This row is the strongest single entry in the table for P2 ∘ P6, and it is worth stating why the
  cells fall as they do. **P2 = Y and P6 = Y, composed:** eq. (1a) is
  `D = 1 + phi[(sum n_i^2 / N) - 1]`, whose multiplier is the size-biased mean exactly, and eq. (3a)
  substitutes `phi = (p_11 - p^2)/[p(1-p)]` with `p_11` their same-village joint-disease probability
  — i.e. `1 + (m~ - 1) rho_I`, on clusters of 1 to 589. **P1 = `~`, not `Y`:** their outcome is
  natively binary, so there is no underlying continuous score and the indicator-versus-score
  distinction of §4.2 cannot arise there — the same reading as [teerenstra2010]. **P5 = N** with a
  control: `coverage` returns 0 against `design effect` returning throughout. **And a caution that
  is not a cell:** they state, citing Prentice (1988), that a binary correlation is
  prevalence-*range*-constrained. That is a bound rather than a functional dependence, but it means
  the bare observation that a binary ICC moves with prevalence was standard by 1993 and is not
  available as a claim of ours in any range-bound sense.
- **AI evaluation standards** ([nistai8003], added 2026-07-30) size the uncertainty of *generalized
  accuracy* — a mean. **P2 = Y**, explicitly and with attribution: §5.3 prints
  `EST = 1/(1+(t-1) ICC)` and says "We use the effective sample size formula from Kish". **P6 = N**
  and it is structural rather than an oversight: their cluster is one item, what repeats inside it
  is `t` trials, and `t` is a **design constant**, so ragged sizes cannot arise — `size-biased` 0,
  `ragged` 0, `unequal` 0, `cluster size` 0. **P1 = `~`:** the correlated quantity is binary
  correctness, an indicator of a fixed event rather than an exceedance at a chosen level. **P3 and
  P4 = N:** no threshold exists in their estimand for a level to be, which is also why their ICC
  cannot be a competing estimate of `rho_I(p)`.
- **AI evaluation measurement** ([miller2024], added 2026-07-30) corrects standard errors for
  exactly our clustering — items sharing a source passage — and does it with an econometric
  cluster-robust sandwich rather than a decomposition. That is why the row is nearly empty despite
  the collision being real: a sandwich returns a corrected number and leaves no parameter behind.
  **P2 = N** with controls: `design effect` 0, `deff` 0, `intraclass` 0, `ICC` 0, `effective` 0 in
  the body, and the symbol `rho` (U+03C1) **0 occurrences in the whole PDF** — admissible only
  because a codepoint census shows eight other Greek letters extracting cleanly from the same file.
  **P6 = `~`, and this cell is the one to get right:** `n_c` is defined once in his Appendix A and
  never reappears in a formula, but his double sum accrues `n_c(n_c - 1)` cross-terms per cluster,
  so ragged sizes are handled **correctly, silently and implicitly**. Any sentence of ours asserting
  that prior art assumes equal cluster sizes would be false.
- **Finite-population inference under non-probability sampling** ([meng2018], added 2026-08-02) sizes
  the error of a **population mean** when recording is non-random. It is in this table for one cell
  and the reader should be told which, because the row is otherwise empty by construction: there is
  no clustering anywhere in the 42 pages, so five of the six ingredients have nothing to attach to.
  **P2 = `~`, and the cell is deliberately not `Y`.** He does build an $n_\text{eff}$ from a
  correlation, from a standing start — $n_\text{eff} \propto \rho_{R,G}^{-2}$, with the rule of thumb
  that cutting $|\rho_{R,G}|$ by 20% raises it "by more than 50%" — which is the shape of P2. But P2
  as defined above asks for a design effect built from **that indicator's** correlation, and his
  indicator is the *recording* indicator $R_j$ correlated against the *value* $G_j$. That is
  selection, not within-cluster dependence, and the two are different objects that happen to produce
  the same functional form. Marking it `Y` would let a reader infer a clustered design effect that
  is not there; marking it `N` would deny a genuine independent arrival at an $n_\text{eff}$-from-a-
  correlation. `~` with this note is the honest cell. **P6 = `n/a`:** no clusters, so ragged sizes
  cannot arise. **P1, P3, P4, P5 = N** with live controls, counted on the whitespace-flattened text
  against `data defect` 34, `correlation` 38, `effective sample` 10, `design effect` 7, `Kish` 4 and
  9 Greek glyphs extracting (`ρ` 153): `cluster` **0**, `intraclass` **0**, `exchangeab` **0**,
  `threshold` **0**, `order statistic` **0**, `prediction interval` **0**, `conformal` **0**,
  `quantile` **1**, `coverage` **6** — the last all of confidence-interval coverage of a mean.
  **What his own problem never required is a threshold at all.** A population mean has no level, so
  P3 and P4 have nothing to attach to, which is the same structural reason [katz1993] and
  [nistai8003] fail those cells from two other directions.

---

## Gaps — this is the work list, not a set of soft claims

1. **[kish1965] CLOSED 2026-07-30, and it moved two cells.** The gap used to read "not read: no
   accessible scan", with P2 resting on secondary attribution and every other cell inferred from the
   formula's form. The book was OCR'd at 300 dpi (662 pages, `papers/text/kish-1965-survey-sampling.OCR.txt`)
   and the register is **targeted, not `full`** — a textbook is not read cover to cover, so the
   located sections were read and every count is a whole-book scan of the OCR. Two cells changed:
   **P1 and P4 both go to `Y`**, because §12.9 "Standard errors for medians and quantiles" computes
   the variance of a median through the standard error of the *proportion below it* — the exceedance
   indicator — and does so for a threshold that is a sample quantile of the data it governs. What is
   *not* there is the composition: **zero sentences in 662 pages contain both a deff-word and a
   median/quantile word**, checked in both directions against 470 and 98 occurrences respectively.
   P3 stays `N` and now has the sharpest evidence in the census behind it — at p. 377 he writes "if
   we assume that the design effect depends only on $n$", treating level-dependence as an assumption
   to be made rather than a quantity to be measured. **Caveat that must travel: OCR errors are
   certain** (the machine renders `n` as `7` in places), so any glyph-level reading goes back to the
   page image.
2. **Two rows still in retrieval:** diagnostic medicine (Crespi 2011, Obuchowski 1997).
   [brennanlockwood1980] and [fieldwelsh2007] were registered 2026-07-30 with artifact paths
   pointing at the lanes holding them, per `keep-literature-reads-per-lane` — not copied here. Both
   were recorded citation obligations and neither was in `references.md`; the table forced them.

   Both changed something. **[brennanlockwood1980] is the cleanest instance in the census of a field
   holding two operands and never multiplying them** — rater intercorrelations in Table 1, the
   variance of the mean cut score in Eqs 8-10, on facing pages, never combined; `design effect` 0
   against `cutting score` 60. Its P4 is `~` for a reason worth keeping: the cut score *is* estimated
   and its estimation variance *is* propagated, but from a rater x item sample disjoint from the
   person x item scores it governs, so the same-sample coupling never arises — it stops one step
   short. **[fieldwelsh2007]'s P2 is `~`** because var(T) is *exactly* mg sigma^2 [1+(m-1)rho] in
   their algebra and is never factored or named.
3. **[christoffersen1998] CLOSED 2026-07-30; [ramos2026] is still not at full depth** and its cells
   must not be cited as verified absences. Christoffersen was read in full from page images of the
   published article (pp. 841–862) supplied by Adam, and it earned a `Y` on P5 that the stub had not
   claimed: his Figure 1b **plots** realised conditional coverage of a nominal 75% interval wandering
   between roughly 0.4 and 0.9, with a first-order autocorrelation of 0.94 — the object Theorem 1
   gives a law for, drawn as a time series thirty years earlier for a different dependence mechanism.
   **One caveat is structural rather than incidental: no text extraction exists on disk**, so
   `check_citations.py` reports this entry under "no readable artifact" and that is correct
   behaviour, not a defect. Every quote is verifiable only against the page images until someone
   OCRs them, and the demarcation the entry draws — he varies the *power of a test* with the level
   where §5 varies the *dependence parameter* — is the load-bearing one to re-check if they are.
4. **[patton2013] P4 is `~` and needs a decision.** He uses EDF margins, so his $q$ is an empirical
   quantile — but of the *marginal* transform, not a threshold whose sampling variability is the
   object of study. Whether that counts as P4 changes one cell and should be settled by reading his
   §2.3 rather than argued.
5. **P6 is thinly assessed** across the whole table. It is the least contested ingredient — the
   size-biased correction is squarely [moulton1986]'s and we claim only transport — so the cost of
   leaving it sparse is low, but the row should not be presented as complete.
