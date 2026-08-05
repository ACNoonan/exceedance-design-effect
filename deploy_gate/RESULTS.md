# `deploygate` RESULTS — the design effect on a deployment-side uncertainty gate

*Both arms complete, 2026-07-30. Pre-registration in `PREREG.md`, written and committed before either
measurement ran. All six gates passed on `deploygate/D-01`; `deploygate/G-03` failed in
`deploygate/D-02`'s tail exactly as it was written to.*

**The gap this closes.** §9b:250 names "an abstention or escalation threshold fitted on a labelled
pool with several items per source" as a place Theorem 1 applies, and never measures one. All of the
paper's Theorem-1 instances are training- or eval-side (§6.1 PRM calibration, §9.1 RL filtering, §9b
judge cutoffs). This is the deploy-side gate.

---

## Headline

**An abstention threshold calibrated on SQuAD 2.0 dev's 11,873 questions carries the information of
about 720 — a 95% band of [576, 962] — because the questions come from 35 Wikipedia articles.**
ρ_I(0.90) = 0.0426 against a permutation-null 95th percentile of 0.0012, and m̃ = 364 multiplies it to
DEFF = 16.5.

And on the other arm, **a production moderation threshold calibrated on ToxicChat's 9,586 real prompts
carries the information of about 4,300**, because prompts arrive in template families.

---

## `deploygate/D-01` — SQuAD 2.0, abstention scored by a real QA model

`deepset/roberta-base-squad2`, fp32 on MPS, fixed 384-token shapes with a warm-up forward, 12,165
features for 11,873 questions in 542s. Score is `null_odds` = (null start+end logit) − (best non-null
span logit): the standard SQuAD 2.0 abstention statistic, and what a deployed abstain-gate thresholds.

### Gates

| gate | result |
|---|---|
| `deploygate/G-01` instrument alive | **AUROC 0.9324** against `is_impossible` (bar 0.75) |
| `deploygate/G-02` (A2) | 11,865 / 11,873 distinct (0.9993), modal mass 0.00017 |
| `deploygate/G-04` composition | b, n, m̄, m̃ reproduce `PREREG.md` §1 **exactly at both levels** |
| `deploygate/G-05` sweep variable | realised retained fraction within 6 × 10⁻⁵ of p at every level |
| `deploygate/G-06` positive control | ρ̂ = 1.000000, DEFF = 364.0 = m̃ exactly |
| `deploygate/G-03` not manufactured | nulls 0.0012–0.0014 against measured 0.0175–0.0426 — clears by 13× to 35× |

### The level sweep

| p | ρ_I | DEFF | **n_eff** | null p95 |
|---|---|---|---|---|
| 0.50 | 0.0207 | 8.53 | 1,393 | 0.0012 |
| 0.70 | 0.0254 | 10.22 | 1,161 | 0.0014 |
| 0.80 | 0.0393 | 15.28 | 777 | 0.0013 |
| **0.90** | **0.0426** | **16.48** | **720** | 0.0012 |
| 0.95 | 0.0323 | 12.71 | 934 | 0.0013 |
| 0.99 | 0.0175 | 7.37 | 1,611 | 0.0014 |

Delete-one-article jackknife at p = 0.90: ρ_I = 0.0426 ± 0.0058, 95% CI [0.0312, 0.0540], n_eff band
[576, 962]. Drop-one extremes are 0.0402 (without `Steam_engine`) to 0.0444, so no single article
carries the result. At p = 0.80 the band is [573, 1203].

**ρ_I(p) varies 2.43× across the sweep and is non-monotone, peaking at p = 0.90** — which is where
abstention gates are actually set. An analyst estimating ρ_I at the median and applying it at 0.90
would under-correct by half; estimating at 0.90 and applying it at 0.99 would over-correct by 2.4×.

### Five findings, in order of what they buy the paper

**1. A measured zero-score-correlation instance, on real data.** At the paragraph level the ICC of
the raw `null_odds` **score** is **−0.0026** — indistinguishable from zero — while the **indicator**
ICC at p = 0.90 is **+0.0640**, clears its null (0.0074), and gives DEFF = 1.60. §3's counterexample
of exactly this shape (zero score correlation, positive indicator ICC, DEFF 1.44) is a synthetic
copula construction, and `ICLR-2027-CUT.md` keeps it in the 9pp §3 as a headline object. **It now has
a real-data companion.**

**2. And it corrects a framing claim of ours, in the other direction.** At the *article* level the
indicator ICC (0.0426) **exceeds** the score ICC (0.0352) by 21%. `_icc.py`'s docstring says the score
ICC is "a different and generally larger number", and §6.1's instance is consistent with that (0.599
score vs 0.495 indicator). Here the inequality **reverses**. The defensible claim is that the two
differ and neither bounds the other — not that the score correlation overstates the damage.

**3. The source effect is ancestry, not difficulty — and the evidence is visible without the
decomposition.** `deploygate/T-06` residualises the exceedance indicator on the answerability label
and the effect **survives and rises**: article 0.0426 → 0.0518 (121% retained), paragraph 0.0640 →
0.0873 (136%), both clearing their nulls. Same behaviour as SWE-bench Verified (0.0326 → 0.0367),
opposite to Terminal-Bench 2 where a source effect collapsed into its difficulty label.

The direct evidence is stronger than the decomposition. At a **nominal 90% retention**, realised
per-article retention runs from **75.8%** (`Pharmacy`) to **98.6%** (`Steam_engine`) — a 23-point
spread — while the answerability rate in those same articles is **0.475 vs 0.516**, i.e. flat. The
label balance cannot explain a 23-point swing in gate behaviour. What differs is vocabulary, entity
density and paragraph style: codebase ancestry's analogue in prose.

**4. Two independent routes agree to 0.6%.** At the paragraph level (b = 1,204, where the cluster
bootstrap is trustworthy per §9b's control) the plug-in against a nonparametric cluster bootstrap that
never forms an ICC:

| p | plug-in DEFF | bootstrap-implied DEFF | agreement |
|---|---|---|---|
| 0.80 | 1.38 | 1.38 | 0.4% |
| 0.90 | 1.60 | 1.59 | 0.6% |

They could have disagreed: one is a moment estimator on the indicator, the other a resampling scheme.
This validates Proposition 2 at CV²(m) = 0.055, extending the checked range downward from §9b's
0.640–2.101.

**5. §6.1's nesting structure replicates on the primary substrate too.**
ρ_I(paragraph) = 0.0640 > ρ_I(article) = 0.0426, while DEFF(paragraph) = 1.60 ≪ DEFF(article) = 16.48.
Correlation rises at the finer level; the design effect falls, because m̃ drops 364 → 10.4 and m̃
dominates 1 + (m̃−1)ρ_I. §6.1 found this once, on [park2025], and the paper had to correct itself in
print about which number was complete. Two substrates now, plus `deploygate/D-02`'s five-point sweep.

At p = 0.50 and 0.70 the paragraph-level estimate sits **inside its null** and no effect is reported
there — the same power reading §9b gives SWE-bench Lite, not an absence.

---

## `deploygate/D-02` — ToxicChat under a production moderation score

10,165 real Vicuna-demo prompts carrying `openai_moderation`: eleven continuous per-category scores
from a **deployed** moderation classifier. Exact-normalised duplicates (1,036 rows in a duplicate
group, largest 17) are dropped first, so what is measured is *template ancestry* rather than
copy-paste — exact duplication is §5.1's known exemption (ρ_I ≡ the tie rate), an endpoint rather than
a finding. n = 9,586. Gate score is `mod_max`, the max over categories, which is the deployed decision
statistic. (A2): 9,580 distinct, modal mass 0.00021.

`PREREG.md` registered this arm to produce a **bound**. It produced both a bound and a real effect.

| prefix N | b | singletons | m̃ | ρ_I(0.50) | ρ_I(0.80) | max DEFF | n_eff |
|---|---|---|---|---|---|---|---|
| **4** | 7,493 | 6,778 | **3.90** | +0.335 | **+0.425** | **2.23** | **4,291** |
| 6 | 9,093 | 8,818 | 1.32 | +0.570 | +0.521 | 1.18 | 8,106 |
| 8 | 9,305 | 9,130 | 1.11 | +0.751 | +0.524 | 1.08 | 8,859 |
| 12 | 9,365 | 9,223 | 1.08 | +0.766 | +0.612 | 1.06 | 9,035 |
| 20 | 9,428 | 9,321 | 1.06 | +0.830 | +0.812 | 1.05 | 9,167 |

At N = 4, ρ_I = 0.425 against a null 95th percentile of 0.047 — a factor of nine.

**ρ_I rises monotonically 0.335 → 0.830 as families tighten while DEFF falls monotonically 1.97 →
1.05.** Five points on a controlled knob, saying the same thing as `deploygate/D-01`'s two nesting
levels and §6.1's two.

### The arithmetic point, on three real substrates at different corners

| substrate | ρ_I | m̃ | DEFF | n_eff / n |
|---|---|---|---|---|
| `deploygate/D-02` ToxicChat moderation | **0.425** | 3.90 | 2.23 | 4,291 / 9,586 |
| §9b SWE-bench Verified | **0.033** | 129.2 | 5.18 | 96.5 / 500 |
| `deploygate/D-01` SQuAD 2.0 articles | 0.043 | 364.0 | **16.48** | 720 / 11,873 |

**A thirteen-fold smaller correlation buys a 2.3× larger design effect.** EC-01's E2 established this
on a beam-width sweep over generated data; it now holds across three independent public artifacts.
Either factor read alone tells a practitioner nothing.

### `deploygate/G-03` failed in the tail, and the mechanism is a §8 recipe addition

Beyond p ≈ 0.90 the estimate goes below −1. These are **degeneracies, not tail attenuation**, and are
not reported as level-dependence.

| prefix N | m̃ | **m0 − 1** | MSW/MSB at p=0.99 | ρ_I(0.99) |
|---|---|---|---|---|
| 4 | 3.90 | 0.279 | 0.8 | **+0.178** (in range) |
| 6 | 1.32 | 0.054 | 1.9 | −0.812 |
| 8 | 1.11 | 0.030 | 3.0 | −1.820 |
| 20 | 1.06 | 0.017 | 3.4 | −2.298 |

The ANOVA form is (MSB − MSW)/(MSB + (m0 − 1)·MSW). **As m0 → 1 the denominator collapses to MSB
alone and the estimator becomes unbounded below.** At N = 8 the *design-effect multiplier* m̃ = 1.109
reads as a negligible design effect while the *estimator* has collapsed. m̃ and m0 are different
cluster statistics and only m0 governs stability. `_icc.py` already records the layer-drop lane
reporting an n_eff 1.81× too optimistic by using m0 where m̃ belongs; **this is the converse error —
reading m̃ as licence to trust the ICC.** Recipe: report m0 − 1 alongside b and the largest cluster's
share, and refuse the estimate when m0 − 1 is small.

### A negative worth printing

At N = 4, p = 0.90, **0 of the 11 individual moderation categories clear their own null** (largest
0.066 for `violence/graphic` against 0.072) while the aggregate `mod_max` statistic reaches 0.319.
Stated as a bound rather than an absence: with 715 non-singleton families the per-category detection
floor is ρ_I ≈ 0.073. **The first version of this table was printed as a ranking with no null
attached, and every row of it sat inside the null** — a ranking of noise is indistinguishable from a
ranking of effects until the null is drawn.

---

## Forecast scoring — 8 of 8 true, which is itself a finding about the forecasts

| ID | Proposition | P | Outcome |
|---|---|---|---|
| `deploygate/T-01` | article ρ_I(0.9) clears its null p95 | 0.85 | **TRUE** — 0.0426 vs 0.0012 |
| `deploygate/T-02` | article ρ_I(0.9) ∈ [0.01, 0.15] | 0.75 | **TRUE** — 0.0426 |
| `deploygate/T-03` | DEFF(article) > 4 (n_eff < 3,000) | 0.70 | **TRUE** — 16.48, n_eff 720 |
| `deploygate/T-04` | DEFF(paragraph) < DEFF(article) | 0.80 | **TRUE** — 1.60 vs 16.48 |
| `deploygate/T-05` | ρ_I(paragraph) > ρ_I(article) | 0.80 | **TRUE at p ≥ 0.80** — 0.0640 vs 0.0426; **false at p = 0.50 and 0.70**, where the paragraph estimate is inside its null. The forecast named no level, which was a drafting error; scored at p = 0.90, the level `deploygate/T-01` and `deploygate/T-02` use |
| `deploygate/T-06` | article effect survives the answerability control | **0.55** | **TRUE** — and it *rises*, 0.0426 → 0.0518 |
| `deploygate/T-07` | ρ_I(p) varies ≥ 2× across levels | 0.60 | **TRUE** — 2.43× |
| `deploygate/T-08` | `deploygate/D-02` DEFF ≤ 1.35 for N ≥ 6 | 0.90 | **TRUE** — 1.18 / 1.08 / 1.06 / 1.05 |

**Eight of eight resolving true at a mean stated probability of 0.74 is underconfidence, not skill**,
and the two worst-calibrated rows are the informative ones. `deploygate/T-06` at 0.55 was framed as a
genuine coin-flip between the SWE-bench and Terminal-Bench-2 outcomes; the per-article evidence (flat
answerability against a 23-point retention spread) was already latent in the pre-registration's own §3
and should have moved it to ~0.75. `deploygate/T-07` at 0.60 was hedged when §5's level-dependence had
already been measured on three prior substrates. The lesson is the one `thresheval` recorded:
**a forecast that ignores structure already measured in the frame is hedged rather than uncertain.**

---

## Limitations, as registered and now with numbers

1. **b = 35 at the article level.** Registered as bounding everything, and it does: the jackknife sd
   of 0.0058 on ρ_I becomes a [576, 962] band on n_eff, because m̃ = 364 multiplies it. The point
   estimate alone is not the claim; the band is. The registered prediction that the article level
   would have "no tail power" was **more pessimistic than the outcome** — p = 0.99 cleared its null
   (0.0175 vs 0.0014) — but it remains the least stable row and is quoted with that caveat.
2. **The score is one model's.** ρ_I is a property of (pool, score). This is the structure a deployed
   abstention gate *built on `roberta-base-squad2`* faces; a stronger reader would give a different
   ρ_I, plausibly a larger one, since `deploygate/D-02`'s pattern and §9b's leaderboard result both
   have more deterministic systems clustering more.
3. **SQuAD 2.0's unanswerable questions are adversarially authored** against their paragraph, so the
   pool's marginal is not live traffic. It is the pool a gate is calibrated on, which is the
   theorem's object, but the generalisation to deployment traffic is not measured.
4. **`deploygate/D-02`'s clusters are ours.** Template prefix is a knob; every number is reported
   across its sweep. What argues the structure is real: ρ_I moves monotonically with the knob in the
   direction ancestry predicts, the null sits an order of magnitude below, and the families are
   recognisable — the largest 8-word family is the "hi chatgpt you are going to pretend to" DAN
   template. ToxicChat publishes no user, session or source field, so the per-customer grouping a
   real moderation gate faces is a **lower bound** here, not an estimate.

---

# ADDENDUM — the `squad2-train` arm, 2026-07-30. **The substrate is contaminated, and that is my error.**

Run per `PREREG.md` §5b, registered while the forward pass was in flight. 130,319 questions, 131,823
features, 6,667s. All six gates passed. **And the arm should not have been run as specified.**

## The premise failure, stated first

`deepset/roberta-base-squad2` is fine-tuned on SQuAD 2.0 — the model card says **"Training data:
SQuAD 2.0"** and the HF `datasets` tag is `squad_v2`. Scoring the **train** split with it produces
**in-sample** scores: the model has already seen every question.

I selected this substrate from `experiments/SUBSTRATE-QUEUE.md` on cluster count — b = 442 articles
and b = 19,029 paragraphs — and never asked whether the scorer had seen the pool. The triage filters
for geometry and score availability; **it has no contamination filter**, and I did not supply one.

The contamination is visible in the numbers, not merely suspected:

| | dev (held out) | train (in-sample) | ratio |
|---|---|---|---|
| `deploygate/G-01` AUROC | 0.9324 | **0.9851** | — |
| raw-score ICC, article | 0.0352 | **0.3094** | **8.8×** |
| ρ_I(0.90), article | 0.0426 | 0.0966 | 2.3× |

> **CORRECTION 2026-08-02 — the ICC row above is NOT evidence of contamination, and the arm was
> closed on a partly mis-read diagnosis.** Provenance `squad2_train_contamination_check.py`,
> `results/squad2_contam_control.json`, `results/squad2_label_residual.json`.
>
> **The mechanism.** SQuAD 2.0's unanswerable questions were written for only some train paragraphs:
> **53.0% of train paragraphs are 100% answerable** (9,966 of 18,813) against **0% of dev
> paragraphs**, and 607 of dev's 1,204 sit between 0.45 and 0.55 answerable. Train carries a large
> pile of untouched SQuAD 1.1 paragraphs; dev was built balanced. So the has-answer **label itself**
> clusters: label ICC **0.1893 (train) vs −0.0762 (dev)** at the paragraph level. A shuffle null
> returns −0.0003 / +0.0008, so this is the data and not the estimator.
>
> **The test that establishes it** — an earlier draft of this block compared a *binary* label ICC to
> a *continuous* score ICC and leaned on the two being numerically close, which is not an argument.
> Residualising the score on the label instead:
>
> | | score ICC | label ICC | score ICC, label removed |
> |---|---|---|---|
> | train | +0.2692 | +0.1936 | **+0.1099** |
> | dev | +0.0072 | −0.0761 | **+0.1497** |
>
> The raw gap of **+0.2620 collapses to −0.0398 and reverses sign**: **85% of it is the label**, and
> what remains runs the other way. The score-ICC evidence cannot separate memorisation from
> annotation.
>
> **What stands.** The contamination is still real *a priori* — `deepset/roberta-base-squad2`'s card
> says "Training data: SQuAD 2.0", and that is not in dispute. The AUROC row also stands as a
> measurement (reproduced here at 0.9856 / 0.9326 on a 420-paragraph sample against the recorded
> 0.9851 / 0.9324), though SQuAD 2.0's dev unanswerables were human-validated in a way train's were
> not, which is an untested alternative explanation for part of it.
>
> **What falls.** The sentence "the contamination is visible in the numbers, not merely suspected"
> is too strong for the ICC evidence. The right statement is that contamination is certain from the
> model card and the numbers cannot confirm it, because a construction artifact predicts the same
> pattern.
>
> **And a substrate defect that is worse than the contamination, because no model choice fixes it:**
> train's unanswerable questions cluster by paragraph and article and dev's do not. Any ρ_I measured
> on `squad2-train` is therefore partly a measurement of the annotation protocol, not of a deployed
> gate's uncertainty. That is `SK-02`/`SK-06` territory and it closes the row for the tail-power use
> it was wanted for, independently of which scorer is used.

> **A portability note on the DEV arm, which is the anchor.** Once the label effect is removed both
> splits show the scorer's own paragraph-level clustering at **~0.11–0.15**. Dev's raw 0.0072 is not
> wrong — it is the correct design effect *for a calibration set built with balanced answerability* —
> but it is low **because** dev's labels are balanced by construction (label ICC −0.076 pulls it
> toward zero), not because abstention scores fail to cluster. A deployment pool whose answerability
> clusters by document would show materially more. This does not disturb §4.2's use of this
> substrate, which rests on the *contrast* between score ICC and indicator ICC rather than on the
> magnitude, and which the suppression makes conservative rather than fragile.

**Consequence.** The train arm measures how article-clustered this model's *memorisation* is, not how
article-clustered a deployed abstention gate's uncertainty is. **Every deploy-gate claim continues to
rest on the dev arm alone**, and the train ρ_I values must not be quoted as an abstention-gate design
effect. Nothing in the `deploygate/D-01` dev section or `deploygate/D-02` changes.

## What survives, because it does not depend on the score at all

The permutation null shuffles the indicator across units at a **fixed size profile and fixed
marginal**, so its width is a property of (b, cluster sizes, p) — **not of the scores**. The two
findings below are therefore contamination-free.

**1. `deploygate/T-12` fails, and the mechanism registered in advance is why.** At the paragraph level
with b = 19,029 — comfortably past `empcore`'s P5b budget of b\* ≈ 4,000 — the far tail is still
underpowered:

| p | paragraph ρ_I | null p95 | verdict |
|---|---|---|---|
| 0.50 | +0.2446 | 0.0024 | clears |
| 0.90 | +0.0685 | 0.0028 | clears |
| 0.95 | +0.0425 | 0.0029 | clears |
| 0.99 | +0.0008 | 0.0048 | **inside null** |
| 0.995 | −0.0090 | 0.0069 | **inside null** |
| 0.999 | −0.0310 | 0.0142 | **inside null** |

The null widens **6×** from p = 0.50 to p = 0.999 on identical clusters. `PREREG.md` §5b registered
exactly this before the run: *"b ≥ 4,000 is necessary for tail power and not sufficient — what also
has to be large is the count of units in the rare class."* At p = 0.999 only ~130 of 130,319 units are
in the abstain class.

**2. And the corollary is counterintuitive: fewer, larger clusters buy MORE tail power.** At p = 0.999
the **article** level (b = 442, m̃ = 335) clears its null cleanly — ρ_I = 0.0034 against 0.0005 — while
the **paragraph** level (b = 19,029, m̃ = 8.2) does not, at 0.0142. Same pool, same 130 tail units:
442 clusters can register how those units concentrate; 19,029 clusters almost all contain none.

**This directly opposes "more clusters is better", which is how a cluster-count budget reads.** P5b's
condition needs a second clause, and the quantity it should be written in is the **expected rare-class
count per cluster**, `n(1−p)/b` — 0.29 at the article level here against 0.0068 at the paragraph level.

## Reported, but confounded — not to be interpreted

Attenuation is monotone and enormous on this arm (article ρ_I 0.2616 → 0.0034 across p = 0.50 → 0.999,
a 77-fold decay; paragraph 0.2446 → −0.0310). It is the cleanest level-dependence curve in the
program **and it is measured on an in-sample score**, so it describes memorisation's exceedance
correlation. It is recorded, not claimed.

`deploygate/T-06` also **reverses between arms**: on dev the answerability control *raised* ρ_I
(121–149% retained), on train it *cuts* it to 16–53%, both still clearing their nulls. That
divergence is confounded by contamination and is not interpreted here.

## Forecast scoring — 4 false, 1 unresolved, against 8 of 8 true on the first arms

| ID | Proposition | P | Outcome |
|---|---|---|---|
| `deploygate/T-09` | train article ρ_I(0.90) ∈ [0.02, 0.08] | 0.75 | **FALSE** — 0.0966, above the band. Contamination is the likely cause |
| `deploygate/T-10` | jackknife sd ≤ half of dev's 0.0058 | 0.70 | **FALSE** — 0.0056 at b = 442 against 0.0058 at b = 35. **The forecast was mis-specified**: it named *absolute* sd while 12.6× more clusters buys *relative* precision. Relative width did fall, 13.6% → 5.8% (2.3×), short of the √12.6 ≈ 3.6× predicted |
| `deploygate/T-11` | paragraph ρ_I(0.999) < ρ_I(0.90) | 0.70 | **UNRESOLVED**, as pre-registered — readable only if `deploygate/T-12` passes. (At the *article* level, where it is readable, it holds: 0.0034 < 0.0966) |
| `deploygate/T-12` | paragraph ρ_I(0.999) clears its null | 0.50 | **FALSE** — −0.0310 against 0.0142 |
| `deploygate/T-13` | plug-in and bootstrap agree within 10% at p = 0.90 | 0.85 | **FALSE** — 1.50 vs 1.71, a 14.0% gap (dev: 0.6%) |

Four misses at a mean stated 0.70, immediately after eight hits at 0.74. The first set was
underconfident on a substrate I understood; this set was **overconfident on a substrate I had not
checked**. The two rows about the score's behaviour would both have been rated far lower had the
contamination been known, which is the point — those forecasts were conditioned on a premise that was
false.

## What this changes elsewhere

- **`experiments/SUBSTRATE-QUEUE.md` gains a contamination filter**, between the geometry step and the
  score step. It costs one model-card lookup.
- **§8's cluster-count recommendation** should carry the rare-class-per-cluster clause above, which is
  a structural result and does not depend on this arm's contamination.
- **The dev arm's registered limitation stands unrepaired.** b = 35 and the [576, 962] band are
  unchanged; this run did not fix them. The repair is the same run with a QA model *not* trained on
  SQuAD 2.0, which recovers the b = 442 geometry with an out-of-sample score.

---

# ADDENDUM 2 — `deploygate/D-03`, AdversarialQA. **The gate failed and the arm did not deliver.**

Run per `PREREG.md` §5c, registered before the forward pass. 33,000 questions, 33,337 features,
1,791s. The arm existed to repair `deploygate/D-01`'s b = 35 limitation with question-clean data at
b = 456 titles, m̃ = 102.6. **It does not.**

## `deploygate/G-01` failed, and `measure_adversarialqa.py` stopped before printing a single ρ_I

| gate | result |
|---|---|
| `deploygate/G-07` (two-sided, new) | mean F1 **0.3363**, EM **0.2235** — inside the registered [0.10, 0.70] band. Spans decode correctly and there is no leakage |
| `deploygate/G-01` (rewritten: abstain-when-wrong) | AUROC(`null_odds` vs `is_wrong`) = **0.5854** against a bar of **0.70** — **FAIL** |

The bar was set at 0.70 in advance and is not renegotiated now that the number is 0.585. Per the
pre-registration, an instrument this weak means *"every ρ_I is measuring nothing, and a null would be
uninformative rather than negative"* — so **no article-level ρ_I is reported from this arm, and
`deploygate/D-01`'s dev split remains the only clean deploy-gate instance in the lane.** The b = 35
limitation stands.

## The failure is itself the most interesting thing here

The same score, from the same model, on the same task family:

| substrate | what `null_odds` is asked to predict | AUROC |
|---|---|---|
| SQuAD 2.0 dev | formal unanswerability | **0.9324** |
| AdversarialQA | **its own errors** | **0.5854** |

An abstention score that separates answerable from unanswerable almost perfectly is **barely above
chance at knowing when it is wrong** on adversarially-authored questions. Those are different targets
and the gap is not by itself a contradiction — but a deployed gate is bought for the second one. The
practical reading: **an abstention gate validated on unanswerability can degrade to near-useless
exactly where it is most needed**, and the standard validation would not show it.

That is a claim about gates, not about clustering, and it is offered at the depth one substrate and
one model can bear.

## Secondary, and a DIFFERENT estimand — reported as such

With the abstention score disqualified, one question remains well-posed on an instrument that *did*
pass its gate (correctness, `deploygate/G-07`): **are the model's errors clustered by source
document?** No abstention score is involved. An error rate is a **mean of binary outcomes**, so this
is the design-effect half of the paper and **not** Theorem 1.

**ICC of the error indicator = 0.0068, m̃ = 102.6 → DEFF 1.69, n_eff = 19,547 of 33,000**, clearing a
permutation null of 0.0015 by 4.5×. Across 426 titles with n ≥ 20 the per-title error rate runs
**0.348 to 0.881** — a 53-point spread.

So a reported error rate on this benchmark carries the weight of about 19,500 of its 33,000 questions.
That is a real finding and it is the SWE-bench shape again — a small ICC multiplied by a large m̃ —
but it is a Route-B result and must never be quoted as an abstention-coverage number.

**And F1 reproduces §9.1's coarse-score story on a third substrate.** Modal mass **0.5113** sits at
F1 = 0, with another atom at F1 = 1. Only p = 0.50 and 0.70 are reachable (ρ_I 0.0073 and 0.0059,
DEFF 1.74 and 1.60, both clearing); at p ≥ 0.80 realised retention is **1.000** — the threshold lands
on an atom boundary and the level cannot be expressed at all. The first version of this script printed
those rows as "INSIDE NULL", which would have reported an atom boundary as an absence of clustering.
They are now labelled **UNREACHABLE**, which is what they are.

## Forecast scoring

| ID | P | Outcome |
|---|---|---|
| `deploygate/T-14`, `deploygate/T-15`, `deploygate/T-16`, `deploygate/T-17` | 0.85 / 0.70 / 0.75 / 0.65 | **UNRESOLVED** — all four are ρ_I claims and the gate blocked the ρ_I |
| `deploygate/T-18` | 0.70 | **FALSE** — AUROC 0.5854 against a predicted [0.65, 0.85] |

The only row that resolves resolves against me: I expected an abstention score to predict its own
errors far better than it does. Four unresolved rows are the correct bookkeeping — a blocked
measurement is not a null, and scoring them either way would be inventing evidence.

## What this arm cost and what it bought

Cost: ~30 minutes of scoring plus the code. Bought: a disqualified substrate, one resolved forecast
against me, a deployment-relevant finding about abstention gates under adversarial input, a Route-B
error-clustering measurement at DEFF 1.69, and a third instance of the coarse-score atom problem.
**It did not buy what it was for.** The b = 35 limitation on the deploy-gate headline is unrepaired,
and the honest options remain: accept the jackknife band [576, 962], or find a pool that is
simultaneously question-clean, article-grouped, and carries an answerability label — which the queue
does not currently contain.

## Reproduction

```
score_squad2.py        # 542s on MPS -> results/d01_scores.parquet, d01_scoring.json
measure.py             # gates, sweep, bootstrap, answerability control -> results/d01_measure.json
jackknife_article.py   # delete-one-article CI  -> results/d01_jackknife.json
measure_toxicchat.py   # the moderation arm     -> results/d02_measure.json
```

`_fastnull.py` carries the vectorised ICC used for permutation nulls only. It is **asserted against
`experiments/_icc.py::icc_oneway` on every input before a single permutation is drawn**, and verified
separately on binary, Gaussian and centred-residual inputs across ragged size profiles. Its first
version used the binary identity Σy² = c_j, which is wrong for the residualised values the
answerability control feeds it; the assertion would have caught that as a crash rather than a wrong
number, and it was generalised instead.

Two defects were caught before they produced results. The span extractor originally filtered
candidates with `offsets is None`, which **never fires** under `padding="max_length"` — the tokeniser
returns `(0, 0)` for special and pad tokens — so question and pad tokens were eligible to win the
best-span and every `null_odds` would have been corrupted. It now masks to context tokens via
`sequence_ids`, with an assertion that every feature has at least one. And the paragraph grouping was
initially keyed on Python's `hash()` of the context string, which is salted per process and therefore
not reproducible across runs; the grouping now comes from the source frame joined on question id,
which also gives a row-count check the scorer cannot fake.
