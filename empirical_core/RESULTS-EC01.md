# EC-01 — results, 2026-07-29

Pre-registered in `PREREG.md` the same day, before any number existed. Two experiments closed, one
redirected, one gate still open.

---

## E1 — the Beta shape survives. H1 confirmed.

**Registered P(H1) = 0.6. Resolved TRUE.**

`e1_shape_test.py` → `result_ec01.json`, `e1_RESULTS.txt`.

Tie-broken arm, cluster bootstrap over the 500 released questions, 8,000 replicates, operating
point p = 0.8909 (§6.1's rule, threshold 0.750):

| law | n_eff | law sd | KS D |
|---|---|---|---|
| naive — Beta at nominal n | 25,028 | 0.00197 | 0.3130 |
| plug-in — Beta at §6.1's n_eff | 812 | 0.01089 | 0.0965 |
| **matched — Beta at the measured n_eff** | **1,281** | **0.00870** | **0.0167** |

**What makes this readable is the positive control.** The i.i.d. arm against Beta at nominal n
gives KS D = 0.0218 and recovers n_eff = 24,306 against a true 25,028 (ratio 0.97). So the matched
law describes *clustered* data about as well as the correct law describes genuinely i.i.d. data —
0.0167 against 0.0218. The residual is at the floor the bootstrap itself imposes.

**This closes SW-30.** The paper concedes in print that "a central limit theorem fixes two moments,
not a distribution," and every percentile column and 5–95 range in it rides on the Beta shape being
right regardless. It now has evidence rather than a caveat. Nothing is withdrawn.

**The pre-registered directional prediction also came in.** PREREG.md predicted that any misfit
would show as empirical left-skew exceeding the law's, driven by the informative-size channel
(Spearman −0.42). Measured: empirical −0.203, law −0.140. Right direction, small magnitude.

**The raw arm behaved exactly as registered, and reporting it was worth it.** Coverage takes only
**5 distinct values** across 8,000 replicates. Every law fails — *including the positive control*
(D = 0.5054, implied n_eff 689 against 25,028). A control that fails here is the correct outcome:
it demonstrates the raw 9-atom score cannot support any continuous law, the correct one included,
which is a stronger statement of §6.1's discreteness point than the dispersion ratio alone makes.

---

## P5 — E3 is not measurable on the released artifact. H2 withdrawn as untestable.

`p5_tail_separability.py` → `result_p5.json`, `p5_RESULTS.txt`.

Proposition 3 makes the level-dependence direction a property of λ_U. E3 was to estimate it on the
PRM set. P5 asked first whether the instrument can see the difference at b = 500.

Two synthetic worlds on the released size profile, **matched at ρ_I(0.90) = 0.3224**: Gaussian
(λ_U = 0, decay) against t(3) (λ_U = 0.300, floor). At p = 0.99 the truth to be separated is
0.179 against 0.309.

| p | gaussian (95% CI) | t(3) (95% CI) | separation fraction |
|---|---|---|---|
| 0.80 | 0.3746 [0.3303, 0.4161] | 0.3125 [0.2742, 0.3503] | 0.17 |
| 0.90 | 0.3377 [0.2849, 0.3908] | 0.3069 [0.2568, 0.3591] | 0.00 |
| 0.95 | 0.2940 [0.2279, 0.3574] | 0.3049 [0.2333, 0.3768] | 0.00 |
| 0.99 | 0.1909 [0.1044, 0.2548] | 0.3080 [0.1784, 0.4002] | **0.25** |

**Verdict: 0.25 against a registered bar of 0.80.** All three preconditions passed — including the
negative control, which requires the two to *overlap* at p = 0.90 where they were matched (0.00,
as it must be). So the verdict is quotable and is not an artifact of a broken instrument.

**The obstruction is variance, not bias.** Relative bias at p = 0.99 is +6.4% (Gaussian) and −0.4%
(t(3)); the relative CI width is **0.79** — the interval is four-fifths of the estimate. An earlier
reading of a smoke run suggested ~40% downward bias; that was Monte Carlo noise at 30 bootstrap
replicates and is **retracted**.

**Consequence for the paper:** §8 recommends estimating ρ_I(p) from same-cluster pairs "at every
level simultaneously." At b in the hundreds that recommendation has no power in the tail, so a
practitioner cannot check which regime their system is in — and §5's comfort that shared ancestry
costs less at tighter levels is exactly what they would want to check. This is a scope caveat the
paper does not currently state.

---

## P5b — the cluster budget. b ≥ 4,000.

`p5b_cluster_budget.py` → `result_p5b.json`, `p5b_RESULTS.txt`.

"Untestable" is weak. Sweeping cluster count at fixed released m̃ = 61.29 turns it into a design
requirement:

| b | n | gaussian (95% CI) | t(3) (95% CI) | separation |
|---|---|---|---|---|
| 500 | 25,264 | 0.1835 [0.0959, 0.2721] | 0.3077 [0.1732, 0.4397] | 0.15 |
| 1,000 | 49,038 | 0.1823 [0.1176, 0.2452] | 0.3112 [0.2081, 0.4211] | 0.30 |
| 2,000 | 100,501 | 0.1747 [0.1252, 0.2248] | 0.3119 [0.2337, 0.3916] | 0.65 |
| **4,000** | **201,055** | 0.1795 [0.1449, 0.2165] | 0.3127 [0.2581, 0.3722] | **0.85** |
| 8,000 | 396,060 | 0.1823 [0.1547, 0.2116] | 0.3062 [0.2682, 0.3464] | 1.00 |

**b\* = 4,000 clusters. The released artifact has 500 — short by 8×.**

The point estimates are stable and near-unbiased at every b (Gaussian ≈ 0.18 against exact 0.1794;
t(3) ≈ 0.31 against exact 0.3187). Only the interval narrows. That is a second, independent
confirmation that the estimator is sound and the obstruction is purely sample size.

Precondition P1: the vectorised count-form ICC agrees with `prm_measurement.anova_icc` to
**12 decimal places** on the released set (0.427376544054 both), so the sweep is running the
paper's own estimator and not a lookalike.

---

## E2-pre — ρ_I is marginal-free. A registered E2 arm is withdrawn before any GPU spend.

`e2p_marginal_invariance.py` → `result_e2pre.json`.

PREREG.md required E2 to include an arm holding the score marginal fixed, on the grounds that a
temperature sweep moves the marginal as well as the ancestry. **That requirement was wrong.** ρ̂_I is
a rank statistic — the paper's own distribution-freeness-given-the-copula result, read backwards.

| arm | transforms | max deviation in ρ̂_I |
|---|---|---|
| **positive** — strictly monotone | affine, log1p, expit, cube, rank-uniform | **0.000e+00** (bit-identical) |
| **negative control** — quantising | round to 1dp, floor to 8 bins | 3.578e-02 |

The negative control is what makes the positive one mean anything: the harness *can* see a marginal
change, it just isn't one here. Arm dropped; E2 gets cheaper.

**The caveat that survives is the real one.** DEFF = 1 + (m̃ − 1)ρ_I, and beam width moves **m̃
directly**. A DEFF rising with beam width may be pure family-size arithmetic with no change in
dependence at all, so E2 must report ρ̂_I and m̃ separately at every configuration. H3 as registered
is the weak form; the informative question is whether **ρ̂_I** moves once m̃ is accounted for.

**Incidental, and it bears on H2b.** The same run prints ρ̂_I by level on the tie-broken released
score: **0.518 (p=0.80) → 0.463 (0.90) → 0.244 (0.95) → 0.054 (0.99)** — a steep decay toward zero,
the tail-independent (λ_U ≈ 0) picture, which is H2b's registered prediction (P = 0.65). Two reasons
this is an observation and **not** a verdict: these are point estimates with no intervals, and P5
established that b = 500 cannot separate a floor from a decay *with* intervals at p = 0.99. It is
suggestive that 0.054 sits below the lower bound of the Gaussian synthetic's CI at the same b, but
the honest statement remains the one P5 registered — untestable at this cluster count.

A second incidental confirmation: `round_8bin` applied to the tie-broken score reproduces the
released variable's pathology exactly — ρ̂_I becomes **undefined at p = 0.95 and 0.99** because
coverage is no longer attainable there. The discreteness argument of §6.1, manufactured on demand.

## E2 — the design effect as a function of a knob. H3 resolves TRUE, for the wrong reason.

`e2_beam_families.py` on athena (`ec01-e2-sweep`, SUCCESS, 93m52s run phase, $0 owned hardware).
**b = 1000 GSM8K questions, Qwen3-0.6B, fp32, `questions_source: gsm8k` verified in the artifact.**
All three preconditions passed, including P3 on both arms.

| arm | w | within_sd | between_sd | ρ_I@.80 | ρ_I@.90 | ρ_I@.95 | m̃ | DEFF@.90 |
|---|---|---|---|---|---|---|---|---|
| **beam** | 2 | 0.0096 | 0.0723 | 0.632 | **0.611** | 0.537 | 2 | 1.61 |
| sample | 2 | 0.1044 | 0.1471 | 0.0005 | **−0.011** | 0.032 | 2 | 0.99 |
| **beam** | 4 | 0.0125 | 0.0513 | 0.644 | **0.561** | 0.488 | 4 | 2.68 |
| sample | 4 | 0.1444 | 0.1109 | 0.057 | **0.086** | 0.063 | 4 | 1.26 |
| **beam** | 8 | 0.0136 | 0.0439 | 0.634 | **0.539** | 0.473 | 8 | 4.77 |
| sample | 8 | 0.1702 | 0.0828 | 0.064 | **0.050** | 0.071 | 8 | 1.35 |

### 1. The ancestry contrast is decisive, and the mechanism is shared prefixes

beam ρ_I sits at **0.47–0.64** at every width and level. sample ρ_I sits at **0.00–0.09**. The gap is
roughly an order of magnitude and dwarfs any plausible sampling error at b = 1000.

So the dependence comes from **shared prefixes and joint top-w selection**, not from conditioning on
a common question. That is the mechanism §3 names, isolated for the first time — and it is not
available from the released artifact, which fixes one decode configuration.

**The sample arm is also a negative control on the entire apparatus, on real data.** ρ̂_I returns
≈ 0 (including −0.011, i.e. straddling zero as an unbiased estimator should) when families share a
prompt but no ancestry. P5's controls were synthetic; this one is the real pipeline, real model, real
questions, and it comes back at zero. Nothing about it is simulated.

### 2. ρ_I is FLAT in beam width — so the DEFF growth is arithmetic

DEFF@.90 climbs 1.61 → 2.68 → 4.77 across widths 2 → 4 → 8. **Almost all of that is m̃.** ρ_I over
the same sweep goes 0.611 → 0.561 → 0.539: flat, if anything mildly *declining*.

H3 as registered — "DEFF is monotone increasing in beam width", P = 0.7 — **resolves TRUE and is
nearly vacuous.** The informative form, registered alongside it, is whether *dependence* rises once
m̃ is accounted for, and the answer is **no**.

**This is the finding, and it is the trap the design was built to catch.** A practitioner who widens
their beam, watches the design effect climb, and reports growing dependence is reporting
`1 + (m̃ − 1)ρ_I` with ρ_I held fixed. Per-unit dependence is a property of the decoding **mode**,
not of the width. Had the script printed DEFF alone — as the naive version of this experiment
would — the write-up would have claimed the opposite.

**Precision caveat, stated plainly.** The beam/sample gap (~0.5) is far outside any interval b = 1000
supports. The *within-arm* width trend spans only 0.072, which is comparable to the CI half-width P5
measured at b = 500. So the safe reading is "ρ_I does not increase with width", not "ρ_I declines".
**The run saved per-configuration summaries but not per-family scores, so intervals cannot be
bootstrapped post hoc — the next run must persist the family arrays.**

### 3. §5's level-dependence appears on data we generated

Within the beam arm ρ_I falls with the coverage level at every width: 0.632 → 0.611 → 0.537 (w=2),
0.644 → 0.561 → 0.488 (w=4), 0.634 → 0.539 → 0.473 (w=8). That is §5's attenuation, measured on a
pipeline we controlled rather than derived under a copula assumption. p = 0.99 is out of reach at
b = 1000 per P5b, so this says nothing about λ_U.

### 4. The mechanism is visible in the raw spreads

beam families are internally tight and far apart (within 0.010–0.014, between 0.044–0.072); sample
families are internally loose and overlapping (within 0.104–0.170, between 0.083–0.147). That *is*
the ICC, before any estimator touches it. And the mild ρ_I decline is legible here too: across
widths beam within_sd rises (0.0096 → 0.0136) while between_sd falls (0.0723 → 0.0439), and both
push the ratio down.

### What it means for the paper

**8,000 beam-search calibration points at width 8 carry about 1,676 points' worth** — measured, on a
configuration we chose. §6 currently has one such number from one released artifact. This adds a
second, with the decode knob attached and an ancestry control beside it.

## E2-tail — b = 4,000, all four arms, with intervals. The strongest result in the lane.

`ec01-e2-tail` on athena, SUCCESS, 16,128 s (4h29m), $0. 4,000 GSM8K questions, Qwen3-0.6B, fp32,
`questions_source: gsm8k` verified. All three preconditions PASS. 400 cluster-bootstrap replicates,
resampling **families**.

**The marginal, named before any number is read.** Coverage here is `F_pop(q̂)` with `F_pop` the
pooled empirical CDF over **all siblings**, so every effective-sample-size figure below is stated
under a **per-beam test marginal** — a future test point is a draw from the pool of generated
sequences — with calibration sets resampled by drawing **questions**. This is the analogue of
SW-23's per-prefix reading (a), under which the family-size channel contributes exactly zero. Under
a per-question marginal these figures would differ and are not claimed.

| arm | w | ρ_I@.80 | ρ_I@.90 | ρ_I@.95 | ρ_I@.99 (95% CI) | DEFF@.90 | DEFF@.99 |
|---|---|---|---|---|---|---|---|
| **beam** | 2 | 0.647 | 0.606 | 0.484 | **0.268** [0.146, 0.399] | 1.61 | 1.27 |
| sample | 2 | 0.049 | 0.059 | 0.069 | 0.041 [−0.010, 0.142] | 1.06 | 1.04 |
| **beam** | 8 | 0.642 | 0.531 | 0.414 | **0.228** [0.172, 0.283] | 4.72 | 2.60 |
| sample | 8 | 0.062 | 0.055 | 0.060 | 0.051 [0.036, 0.075] | 1.39 | 1.36 |

### 1. The ancestry effect survives all the way into the tail

At the tightest level measured, beam(8) still carries ρ_I = 0.228 with a CI comfortably clear of
zero, giving **DEFF = 2.60 at 99% coverage**. Under the per-beam marginal above, 32,000 beam-search
calibration points carry about **12,300 points' worth** there, and about **6,780** at 90% coverage.
Whatever the asymptotic tail behaviour, the discount §5 offers has not arrived by p = 0.99 on a real
decoding pipeline.

### 2. Attenuation belongs to the *prefix* mechanism, not to clustering

The two arms have different **shapes**, which is more informative than their levels:

- **beam attenuates hard** — 0.642 → 0.531 → 0.414 → 0.228, a factor of 2.8 across the range.
- **sample does not attenuate at all** — 0.062 / 0.055 / 0.060 / 0.051, flat within noise.

So §5's level-dependence is a property of prefix-sharing dependence specifically. Prompt-only
clustering produces a small, **level-flat** ρ_I — the signature §5.1 assigns to a
duplication/comonotone component rather than a Gaussian-like latent structure. And the sample arm's
CI excludes zero at three of four levels: prompt-only clustering is small but real, so a system
calibrating on k samples per prompt is not at DEFF = 1 (it is at 1.39 for k = 8, per-beam marginal).

### 3. H3 resolved with intervals, and it moves *against* the naive reading

At b = 1,000 the width trend was inside the noise. It no longer is: beam ρ_I@.90 is
**0.606 [0.567, 0.646] at w = 2 against 0.531 [0.510, 0.556] at w = 8 — CIs disjoint.** Dependence
declines with beam width, by ~12% relative.

Meanwhile DEFF@.90 climbs 1.61 → 4.72. **So the design effect nearly triples while the dependence it
is built from falls.** All of the growth, and more, is m̃ arithmetic. Yesterday's headline was right
and is now sharper: a practitioner widening their beam and reporting a rising design effect is
reporting `1 + (m̃ − 1)ρ_I` with ρ_I moving the other way.

This is also what the §3.3 mixture account predicts — width 8 reaches down to earlier-diverging
branches, lowering the mean pairwise correlation. `ec01-e2-lcp` tests it directly.

### 4. What is NOT established, and a flaw in my own design

**λ_U is not resolved, and the comparison I built for it does not apply.** P5b's Gaussian and t(3)
reference arms were constructed on the *released* size profile — m̃ = 61.3, matched at
ρ_I(0.90) = 0.322. The real beam data is m̃ = 8 with ρ_I(0.90) = 0.531. The references are matched to
neither, so "does the measurement sit with Gaussian or with t(3)" is not a question those arms can
answer for this data. That is a design error in P5b, not a limitation of the measurement.

What the data does establish needs no λ_U: at p = 0.99 the exceedance correlation is
0.228 [0.172, 0.283]. Whether ρ_I plateaus there or continues toward zero beyond 0.99 is unresolved,
and settling it would need reference arms rebuilt at the measured m̃ and ρ_I(0.90).

## What changes in the plan

1. **E3 moves out of the PRM artifact and into E2.** The beam sweep generates its own data, so b is
   ours to choose. E2 must generate **≥ 4,000 families** if it is to answer the tail question at
   all. Without P5b that budget would have been a guess.
2. **H2 is not reported as a null.** It is reported as untestable at b = 500, with the required b
   named. That is a stronger statement than a wide interval.
3. **The paper gains a caveat, not a correction.** §8's estimator recommendation needs a cluster-count
   condition attached. Accumulate-class — nothing published is wrong, a reader is not acting on a
   bad number.
4. **E1 needs no follow-up.** It closed on the first run with its positive control passing.

## EC-00 — census. The breadth table does not exist, and that is the finding.

`census_ec00.json`. **Registered expectation: ≤3 qualify, P(≥4) = 0.3. Resolved: 1 of 13.**

Five systems examined beyond the paper's eight. **None qualify.** The discriminating question was
fixed before searching: do two calibration units *i ≠ j* share a generative ancestor, or does each
unit consume its samples into one score?

| system | calibration unit | ancestry | depth |
|---|---|---|---|
| `2309.03797` Conformal Autoregressive Generation | `(X_i, S_i)` pair, one per input | no | full |
| `2605.30085` CROP — reasoning trace prefixes | complete labeled reasoning instance | no | full |
| `2605.08077` CPR — KGQA path-level | query (aggregated) | no | full |
| `2605.18812` PASC — multi-stage pipelines | example tuple, stages nested | no | snippet, provisional |
| **UaG (Ni et al. 2025)** — hop-level KGQA | **hop** *(third-party claim)* | **likely** | **unsearched** |

**The breadth table the external review proposed cannot be built.** Per PREREG.md, ≤2 qualifying is
itself the result, and the census is printed in the table's place.

**Three things this changes, one of them against interest.**

1. **§6's claim strengthens.** "The PRM case appears genuinely distinctive rather than
   representative" now rests on 13 systems rather than 8, and on the two hardest cases: a paper that
   puts conformal prediction *inside beam search* (`2309.03797`) and a paper certifying *reasoning
   trace prefixes* (CROP) both keep units i.i.d.

2. **§6 gains a far better "bought by design" exemplar.** CROP is the direct methodological contrast
   to `park2025` — same domain, same risk proxies (it cites process reward models explicitly),
   opposite choice of unit. Its Assumption 1: *"steps within a trace may be arbitrarily dependent,
   but complete labeled instances must be exchangeable."* That is the repair, stated in one line, by
   a system that shipped it. The current audit-table row for this mode is a generic placeholder.

3. **§7's "why unnoticed" argument needs weakening, and we should do it ourselves.** §7 attributes
   the gap to four camps that do not cite one another. But CROP and CPR — both 2026 — *independently
   diagnose the ancestry hazard and repair it by choice of calibration unit*. CPR is explicit:
   query-level aggregation "restores exchangeability at the query level." So the hazard **is** being
   noticed by practitioners. What remains underived is the *quantification* — what it costs when
   left unrepaired. That is a narrower and more defensible §7 than the current one, and it is more
   honest.

### The UaG lead, resolved — and the summary was wrong

CPR §2.1 states that UaG's "hop-level calibration strategy introduces sequential dependencies that
directly violate the exchangeability premise." Taken at face value that is a third party asserting
*our* violation, and it would have entered UaG in this census as a second qualifying artifact.
Reading UaG in primary text (`2410.08985`, AAAI 2025) says otherwise, on three counts:

1. **UaG's LTT layer is defensible.** `Dcal` is the training partition of **questions** (WebQSP
   2,826 / CWQ 27,639) — *"Note that for calibration, we use the training partition"* — and the loss
   `L_λ = 1{no correct answer in C_λ(X)}` is evaluated per question. Units are questions.
2. **But the retriever thresholds are a different object, and are unspecified.** The `S₁` scores in
   Eq (4) are computed on `(Q ‖ relations-traversed-so-far, r_j)` pairs — path-prefix-level objects —
   and a training partition of questions generates far more such pairs than questions. Whether
   `q_{α₁}` is a quantile over *pairs* (our structure) or over some per-question aggregate **is
   nowhere stated in the paper**.
3. **CPR's objection is not our objection.** "Sequential dependencies" from applying a fixed
   threshold repeatedly along a path is a multiple-testing / path-length issue at *test* time. Ours
   is about dependent units in the *calibration* set. Different failure, different fix.

**Verdict: does not qualify** — and with no released calibration set it could not have been a
breadth-table row in any case. It belongs in §6's audit table as an **unspecified-unit** case, which
is a weaker and more accurate charge than the one CPR makes.

**This is the memory rule earning its keep:** a model summary — and here, a *published paper's*
one-line summary of another paper — is never a premise. Had we not opened it, the census would have
recorded a qualifying artifact that isn't one, and §6 would have repeated CPR's charge as ours.

## Still open
- **E2** — now budgeted at b ≥ 4,000, not yet designed against athena.
- **Register hygiene** — `references.md:206` marks Donner & Eliasziw 1994 "Read in full" with no
  extraction on disk. Load-bearing for nothing now that Proposition 3 is self-contained.
