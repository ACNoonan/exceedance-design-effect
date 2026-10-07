# Paper-to-Lean inventory

This inventory concerns the current manuscript in `paper/sections/`.
It does not certify the experiments, numerical tables, or empirical sampling assumptions.
“Checked” means the named declaration proves the stated claim under explicit hypotheses.
A supporting lemma alone does not make a larger claim checked.

## Principal results

| Paper claim | Status | Lean declarations and scope |
|---|---|---|
| Section 2.1: conditional coverage equals F at the fitted cutoff | Checked | `independent_test_conditional_coverage`, under an independent product model |
| Section 2.1: complementary indicators | Checked | `complement_indicator_covariance`; covariance and both variances are unchanged |
| Section 2.1: probability transform and sorted-sample transformation | Checked | `continuous_cdf_transform`, `sampleQuantile_monotone_map`; flat CDF regions are allowed |
| Section 2.1: ceiling ranks and initial infinite cutoffs | Checked | `eventually_valid_ceil_rank`, `clampedCeilRank_eventually`, `ceilingRuleCoverage_eventually_eq` |
| Theorem 1: Gaussian coverage limit | Checked | `iid_continuous_score_ceil_coverage_cdf`; CDF convergence at every continuity point, including zero limiting variance |
| Theorem 1: rescaled variance limit | Checked | `iid_continuous_score_ceil_coverage_variance_limit`, `iid_ceilingRuleCoverage_variance_limit` |
| Theorem 1: indicator design-effect formula | Checked | `clusterCoverageVariance_indicator_formula`, `iid_continuous_score_ceil_design_effect_variance_limit`; common pair probabilities suffice |
| Section 2.3: arbitrary within-cluster dependence | Checked | `thresholdCount_variance_mean_pair` and `ragged_continuous_score_ceil_coverage_certificate` allow unequal pair correlations through their mean. Equal-size iid clusters are a special case. |
| Section 2.4 and B.8: duplicated-pair drift counterexample | Checked | `duplicated_pair_counterexample_certificate`, `pairCounterexample_conditional_coverage`; the construction and expectation formula are proved |
| Proposition 1: lower and upper endpoint limits | Checked | `indicator_correlation_lower_tail`, `indicator_correlation_upper_tail`; the corresponding tail-coefficient limit is the hypothesis |
| Proposition 2: unequal-size distributional and variance limits | Checked | `ragged_continuous_score_ceil_coverage_certificate`; bounded independent arrays, actual original-score pooled cutoff, common mean pair correlation, and zero limiting variance |
| Section 6.2: prescribed corrected rank and probability guarantee | Checked | `correctedCoverage_failure_bound`, `correctedCoverage_success_bound`; arbitrary fixed unequal sizes and the infinite-cutoff case |
| B.9: finite-sample count and quantile tails | Checked | `ragged_count_tails`, `ragged_quantile_tail`, `ragged_continuous_score_coverage_tail` |
| B.9: exact fourth-moment constant | Checked | `gaussian_tail_fourth_moment_integrable_and_bound`, `ragged_quantile_fourth_moment`; integrability and E[Z⁴] ≤ M² are both proved |
| B.9: uniform integrability and equal-size moment limits | Checked | `ragged_coverage_square_uniformIntegrable`, `ragged_continuous_score_coverage_square_uniformIntegrable`, `CoverageMoments.lean` |
| B.10: estimator definition and divisor | Checked | `clusterVarianceEstimator_eq_sample_variance`; b=n+1 and b≥2 |
| B.10: consistency at the sample-dependent cutoff | Checked | `iid_continuous_score_estimator_consistent`, `iid_continuous_score_ceil_estimator_consistent`; actual original scores and actual pooled quantile |
| B.10: absolute and relative variance consistency | Checked | `iid_continuous_score_estimator_variance_comparison`; relative consistency requires a nonzero limiting variance |

## Other mathematical statements

The inventory includes supporting statements, cited formulas, and constructed examples.
Numerical approximations and empirical results remain outside this proof inventory.

| Location and statement | Current coverage |
|---|---|
| Sections 2.3 and B.3: exact Beta laws for independent scores and identical-member clusters | Checked: `iid_continuous_score_beta_law`, `identical_cluster_score_beta_law`; actual pushforward laws and arbitrary positive replication size. |
| B.3: zero indicator correlation at one level does not imply a Beta law | Checked: `zero_indicator_correlation_not_beta`; an explicit exchangeable uniform-marginal pair has zero indicator correlation at 2/3. The prescribed ceiling rank is two, but its maximum differs from Beta(2,1). |
| B.3: moments of the proposed Beta approximation | Checked: `beta_mean`, `beta_second_moment`, `beta_variance`, `beta_approximation_moments` for the actual Beta measure |
| Section 4.1: Gaussian copula correlation formula and small-correlation expansion | Checked: `gaussian_indicator_correlation_formula`, `correlatedGaussian_covariance`, `gaussian_indicator_correlation_small_rho`. The construction has standard normal marginals and score covariance rho. Numerical tables remain separate. |
| Section 4.2: vanishing Gaussian tail coefficients | Checked: `gaussian_copula_tail_coefficients`, `gaussian_indicator_correlation_tail_limits`, for −1 < rho < 1. The proof derives both tails from Gaussian bounds. |
| Sections 4.2 and B.1: arbitrary identical/independent pair mixture | Checked on the uniform scale: `uniformPairMixture_probability`, `uniformPairMixture_marginals`, `uniformPairMixture_indicator_correlation`; arbitrary weights in [0,1] |
| Section 4.3: size-biased mean and design-effect comparison | Checked: `size_biased_mean_cv`, `size_biased_mean_ge_mean`, `size_biased_design_effect_comparison`, with divisor b |
| B.2: 2-Lipschitz copula diagonal and continuity of indicator correlation | Checked: `pair_diagonal_lipschitz`, `pair_indicator_correlation_continuousAt`, `mean_pair_correlation_continuous` |
| B.2: switching the CLT centering from p_n to p_0 | Checked: `ceil_rank_level_error`, `ceil_rank_sqrt_centering`, `iid_continuous_score_fixed_target_cdf`; both centers give the stated Gaussian CDF limit. |
| B.4: cited Bahadur representation | Checked: `independent_cluster_ceil_bahadur`; actual pooled score quantile and empirical CDF. Independent fixed-size clusters, a common CDF, and a positive derivative at the target suffice. No stochastic remainder is assumed. |
| B.5: unequal-size variance identity under a common mean pair correlation | Checked: `thresholdCount_variance_mean_pair`, `RaggedUniformModel.normalized_variance_sum`; independent count CLT uses this exact variance sum |
| B.7: expectation/count integral and formal smooth expansion | Exact integral checked: `sampleQuantile_expectation_count_unit_integral`. The formal smooth expansion is explicitly heuristic; no remainder bound is claimed, and the unrestricted conclusion is false. |
| B.7: vanishing Gaussian Edgeworth skewness integral | Checked: `gaussian_edgeworth_skewness_integral` |
| Appendix A: row-weighted and inclusion-weighted target CDFs | Checked: `iid_row_target_limit`, `row_target_covariance_difference`, `selected_score_cdf`, `tilted_population_cdf`, `tilted_accepted_cdf`, `selection_example_coverage_deficit`. Acceptance uses an independent uniform draw and a specified retention probability. |
| Section 6.3: effective-size allocation comparisons | Checked: `effective_size_fixed_cluster_bound`, `effective_size_diminishing_returns`. These are algebraic comparisons, not a growing-cluster asymptotic theorem. |
| Section 3.1: zero score correlation with positive indicator correlation | Checked: `reflectionMixture_probability`, `reflectionMixture_marginals`, `reflectionMixture_exchangeable`, `reflectionMixture_correlations`, `zero_score_correlation_counterexample`. The actual mixture has design effect 13/9 at p=0.9. |
| B.1: independent continuous jitter removes marginal atoms | Checked: `independent_jitter_no_atoms`, `independent_jitter_continuous_cdf`; arbitrary measurable scores and nonzero uniform-jitter scale |
| Section 4.2: design-effect limit from a positive upper-tail coefficient | Checked: `design_effect_upper_tail`; this asserts a limit, not a finite-level lower bound |
| B.7: algebraic drift-sign condition | Checked: `drift_sign`; this does not assert that the withdrawn drift expansion holds |

## Verification boundary

The inventory has no remaining proof obligations for the mathematical results listed above.
Every theorem states its assumptions. Supporting lemmas do not replace end-to-end claims.
The five priority gaps from the original handoff are closed.
The additional Beta, Gaussian, Bahadur, selection, and correlation-example proofs are checked as well.

The smooth-integral calculation is explicitly heuristic and is not a claimed theorem.
The unrestricted second-order drift conjecture is false; Lean checks its counterexample.
Experiments, numerical tables, empirical sampling assumptions, historical attribution, and recommendations require separate validation.
No uniform accuracy claim for the normal or Beta approximation is proved or made in the manuscript.

The checker compiles 59 modules in dependency order.
The integrated log is `audit/v9/lean-total-coverage-2026-09-21.log`.
The source hashes are in `audit/v9/lean-total-coverage-2026-09-21.sha256`.
The pinned versions are Lean 4.32.1 and mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`.

The checker audits every declaration defined by the listed modules, including private declarations and unused axioms.
It accepts only `propext`, `Classical.choice`, and `Quot.sound`.
`bash formalization/test_audit.sh` checks rejection of an incomplete proof and an unused custom axiom.
