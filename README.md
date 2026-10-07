# exceedance-design-effect

The Lean proofs, analysis scripts and `neff` estimator for my paper, **"The Exceedance Design Effect: Effective Sample Size for Thresholds under Clustering"** (Adam Noonan, 2026).

A dataset does not have one effective sample size. How much information it contains depends on the question you ask.

In our document experiment, the same 1,000 rows carried about 217 independent observations' worth of information at the median. At the 95th percentile, they carried about 621. Nothing about the dataset changed. We asked it a different question.

That is why a single "quality-adjusted" sample count can mislead. The number of rows is a property of the dataset. The effective sample size belongs to the analysis.

The paper proves the result behind those numbers. Set a cutoff at a percentile of a sample whose observations come in groups. Grouping multiplies the variance of the fraction that falls below the cutoff by `1 + (m − 1)ρ_I(p)`, where `m` is the group size and `ρ_I(p)` measures whether two members of a group land on the same side of the cutoff. That correlation can be positive when the scores themselves are uncorrelated, and it changes with the cutoff.

- **Paper:** [arXiv:2608.21262](https://arxiv.org/abs/2608.21262) (v2, 22 pages).
- **Cite:** concept DOI [10.5281/zenodo.21595640](https://doi.org/10.5281/zenodo.21595640). It always resolves to the newest version, and it is the only DOI worth citing.
- **Current record:** Zenodo v11, [10.5281/zenodo.23083374](https://doi.org/10.5281/zenodo.23083374), 2026-10-01. It holds the paper, an eight-page theorem note and the code archive. arXiv v2 carries the same text.

## The estimator, in one command

`neff` answers one question: how many independent observations is your evaluation worth?

```bash
pip install -e .

neff outcomes results.csv --cluster-col repo --value-col resolved --unit repo
neff scores cal.csv --cluster-col prompt --value-col score --level 0.9 --unit prompt
neff passk --pass-at 1=0.428,2=0.522,3=0.568,4=0.596,5=0.615 --trials 5 --n-items 89
```

Each prints rho, m-tilde, DEFF, n_eff and a reporting line you can paste into a paper.
`pytest` runs the golden suite, which pins the published numbers.

## Checking the proofs

`formalization/` holds 59 Lean source files, a claim inventory and the checker. Lean verifies Theorem 1, both propositions, the finite-sample guarantee, the variance estimator's consistency and both main counterexamples. [`formalization/CLAIM_INVENTORY.md`](formalization/CLAIM_INVENTORY.md) maps each statement in the paper to its Lean declaration and its hypotheses.

```bash
bash formalization/check.sh        # rebuilds every module, then audits each declaration for unapproved axioms and placeholders
bash formalization/test_audit.sh   # shows the audit rejects an incomplete proof and a custom axiom
```

The checker needs elan. It uses Lean 4.32.1 and pins the mathlib commit, which it may download. `audit/v9/` records the completed proof build and the hashes of its sources.

Lean checks the mathematics under explicit assumptions. It does not check the data pipelines, the sampling assumptions or the numerical tables. The scripts below do that.

## Reproducing the paper's numbers

`python run.py --list` lists every script, and `python run.py theory/verify_indicator_icc.py` runs one. The runner puts the topic directories on the import path and keeps the script's exit code. Read a script before you run it: some write files or download data and models.

These are the scripts behind the current text (its Appendix F.2):

| result in the paper | scripts |
|---|---|
| Gaussian dispersion comparison | `theory/verify_indicator_icc.py`, `theory/sim_validation.py` |
| Score-correlation counterexample and dependence checks | `theory/assumption_stress.py` |
| Tail-limit calculations | `tails/verify_tail_limit.py`, `tails/evt_tail_rate.py` |
| Unequal-size and ICC estimation examples | `theory/ragged_and_estimation.py`, `prm/icc_estimators.py` |
| Released proxy measurements and resampling | `prm/prm_measurement.py`, `prm/prm_dispersion.py`, `prm/test_marginal_scope.py` |
| SQuAD score–indicator comparison (§3.3) | `deploy_gate/score_squad2.py`, `deploy_gate/measure.py`, `deploy_gate/results/d01_measure.json` |
| PRM singleton control and Beta comparison (Appendix E.4) | `prm/deployment_reframe.py`, `empirical_core/e1_shape_test.py`, `empirical_core/result_ec01.json` |
| Document-corpus example (§5.3), the source of 217 and 621 | `deploy_gate/score_conll_ner.py`, `conll/conll_levels.py` |
| Unweighted NHANES indicator comparison | `nhanes/one_sided_rho_I.py` |
| Weighted NHANES fixed-threshold comparison | `nhanes/nhanes_fixed_threshold.py`, `nhanes/nhanes_samplics_check.py` |
| Gaussian mean-drift integration | `theory/drift_tables.py` |
| Nested Gaussian comparison | `theory/nested_structure.py` |

A script travels with its committed output (`<script>_RESULTS.txt` or a results JSON), so you can diff your run against ours.

Some analyses need cached inputs this repo does not include. The CoNLL analysis needs `deploy_gate/results/conll_ner_scores.parquet`, which `score_conll_ner.py` creates. For SQuAD, the repo carries the scoring metadata and the measurement results, and not the cached data or model weights. The PRM analysis uses released proxy scores. The NHANES comparison uses public masked survey groups.

The numerical audit ran on Python 3.14, NumPy 2.5.1, SciPy 1.18.0, pandas 3.0.5, mpmath 1.3.0 and Matplotlib 3.11.1.

## How this repo relates to the Zenodo archive

`main` carries every file of the v11 code archive unchanged, with two exceptions: this README, and root `_icc.py`, which here is a shim onto `neff/_icc.py` (the same module, byte for byte). `main` adds the `neff` package, its tests and the packaging files. The archive is unchanged from v9 through v11, which is why its own README and `audit/` say v9.

The tag [`v7-zenodo`](https://github.com/ACNoonan/exceedance-design-effect/tree/v7-zenodo) mirrors the 83-file archive of the v7 and v8 records.

`docs/REPRODUCTION.md` and `docs/CORE-CLAIM-REVIEW.md` record the audit decisions. `calkit/` and `_conformal.py` are the two conformal implementations, and `verdict.py` is the reporting helper.

## Earlier analyses, kept for traceability

The paper was 48 pages through Zenodo v8 and arXiv v1, and it is 22 pages now. The scripts below include analyses the current text no longer claims, among them the generated-beam and WHO sensitivity comparisons. The historical drift and compound-design scripts include scientific checks that failed, and a saved result file may predate a source correction. A script's presence here is not an endorsement of its claim: the current paper decides which claims stand.

The section numbers in these tables refer to the 48-page text.

### theory/

| script | produces |
|---|---|
| `verify_indicator_icc.py` | §4.1, §4.2, §5 — the coverage law, the score-correlation rival, level-dependence |
| `sim_validation.py` | Corollary 1 — copula-family invariance at matched delta(p) |
| `drift_coefficient.py` | §4.3 — the O(1/b) drift coefficient, falsification tests, exchangeable control |
| `prop1_exact.py` | §4.3 — the exact drift table and the measured O(n^-2) remainder |
| `prop1_combinatorial.py` | §4.3 — the same drift by an exact combinatorial identity sharing no code path with `prop1_exact.py` |
| `prop1_edgeworth_probe.py` | §10 — shows Proposition 1's Edgeworth step is inert for the atom mixture: a continuity-corrected normal with no skewness term reaches the coefficient, its own error entering at O(n^-2) |
| `drift_tables.py` | §4.3's two drift tables, regenerated by the exact route with an artifact on disk |
| `residual_check.py` | independent check of the drift-coefficient prediction and its residual — a re-measurement, not a re-derivation |
| `marginal_guarantee_exact.py` | §3, §6.1 — whether clustered calibration breaks the ≥ 1−α marginal guarantee, exactly rather than by simulation |
| `overcoverage_bound.py` | §2.6 — whether clustering can break the over-coverage bound too, with tie-free and matched-sign controls |
| `composition_check.py` | §2.3 — the negative-ρ_I sweep (n_eff > n); ragged sizes and within-family structure composing |
| `nested_structure.py` | §4.4 — the invariance class, with the discriminability check |
| `assumption_stress.py` | §4.2's counterexample; §2.3 across-family dependence |
| `ragged_and_estimation.py` | §2.4 ragged families; §8 estimator bias and spread |
| `edgeworth_terms.py` | which analytic term makes Proposition 1's remainder O(n^-2) |
| `sw12_uniform_nondegeneracy.py` | SW-12 step (1) — uniform non-degeneracy of the cluster-count law over a window of t |
| `sw12_lattice_edgeworth.py` | SW-12 step (2) — the CDF-level lattice Edgeworth expansion and whether it is uniform in the level |
| `sawtooth_integral.py` | attempts [esseen1945]'s lattice term by quadrature; retained because its precondition fails — the value halves with every refinement, which is how we learned the integral is zero |
| `sawtooth_fourier.py` | the sawtooth term is exponentially small, not merely o(1/n) |
| `condition6_check.py` | whether (A1)–(A2) imply Francisco–Fuller Condition 6 |
| `compound_deff.py` | the compound design effect, separated from Kish's naive ρ product |
| `compound_deff_sweep.py` | whether the 3.6-SE residual is a finite-b delta-method artifact or a real bias |

### tails/

| script | produces |
|---|---|
| `verify_tail_limit.py` | Proposition 3 — tail limits of rho_I, and the atom-mixture exact form |
| `evt_tail_rate.py` | the tail approach rate, building on `verify_tail_limit.py` |
| `evt_lambda_u_estimation.py` | §5 — whether a practitioner can estimate their own tail-dependence floor λ_U |

### prm/

| script | produces |
|---|---|
| `prm_measurement.py` | §6.1 — the released PRM calibration set (downloads ~33 MB on first run) |
| `prm_dispersion.py` | §6.1 — MEASURES the dispersion ratio by cluster bootstrap (raw 1.09×, tie-broken 4.4×) against the plug-in 5.55; four preconditions incl. a synthetic ground-truth arm; needs the cache from `prm_measurement.py` |
| `trajectory_index.py` | §6.1 — recovers the trajectory index the release does not carry, by prefix-nesting: 3,961 maximal chains, ρ_I 0.688 and design effect 7.06 at the trajectory level against 0.495 / 30.8 at the question level. Its P3 precondition re-derives §6.1's published question-level numbers from this independent path before the new ones are reported; needs the cache from `prm_measurement.py` |
| `test_marginal_scope.py` | §2.5, §6.1, §10 — the per-question / per-prefix test-marginal gap and its two baselines |
| `icc_estimators.py` | §8 — whether one-way ANOVA is the best ICC estimator on ragged sizes, or just better than the one it replaced |
| `deployment_reframe.py` | §6 — the deployment reframe and its un-clustered negative control |
| `ceiling_rho_response.py` | §6.1's sampling-depth ceiling, recomputed with ρ_I responding to family size |
| `sw52_direct_sim.py` | whether the measured-vs-plug-in gap is the law running high or the bootstrap running low |

### selection/

| script | produces |
|---|---|
| `k1_construction.py` | Theorem 2's construction; prints five preconditions and all five are capable of failing |
| `selection_dose_response.py` | selection-on-score — the dose–response curve in simulation |
| `sw15_epsilon_matched.py` | whether the crossing-as-fraction-of-attainable-correlation is stable or merely ε-dependent |
| `informative_sizes.py` | §2.5 — informative cluster sizes, simulated and measured on the PRM set |
| `jrc_bridge.py` | whether Jin–Ren–Candès (arXiv:2111.12161) applies to Theorem 2's construction |
| `known_pi_repair.py` | whether Theorem 2's tilt is repairable when π is known |
| `unselected_slice.py` | how small an unselected slice beats a large selected calibration sample |
| `weighting_deff.py` | the quantile step and the weighted-calibration design effect — the two items the full-read audit left open |
| `reweighting_cost.py` | what §2.5's size-reweighting repair costs in effective sample size |

### The lane directories

- `empirical_core/` — `e1_shape_test.py`: does the coverage law hold distributionally, or only in variance; `e2_beam_families.py`: generated beam families vs decode config (§6.2); `p5b_cluster_budget.py`: §8's tail-separability budget, with `p5_tail_separability.py` as its precondition module
- `deploy_gate/` — §3's measurement on the PASC CoNLL substrate
- `nhanes/` — §5.2's geographic-clustering check
- `sw02ext/` — §8's clustered training-conditional shift, with its run log
- `figures/` — `build_figures.py` renders all five figures; `figure.py` is the sweep it grew from

