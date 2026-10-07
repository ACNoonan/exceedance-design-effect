# Lean verification

The 59 source files compile with Lean 4.32.1 and mathlib commit
`520045ab14e26149ee970e2e617ca04b09bde5d6`.
The compiler log is `audit/v9/lean-total-coverage-2026-09-21.log`.
The source hashes are in `audit/v9/lean-total-coverage-2026-09-21.sha256`.
The build rejects proof placeholders and custom axioms.
Its final step inspects the dependencies of every local declaration in Lean, including private declarations.
The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

[CLAIM_INVENTORY.md](CLAIM_INVENTORY.md) maps the manuscript's mathematical claims to their proofs.
It includes the main limits, ancillary formulas, constructed counterexamples, and cited Bahadur representation.
Numerical experiments and empirical sampling assumptions require separate validation.
The withdrawn drift conjecture remains false.

| File | What Lean checks |
|---|---|
| `Exceedance.lean` | Design-effect algebra, the tail-rate identity, the drift-sign condition, counterexample arithmetic, and a variance identity conditional on covariance row sums |
| `IndicatorVariance.lean` | Indicator means, variances, and covariances from measurable event probabilities; the exact finite-cluster variance; the fixed-level count CLT; local-increment variance and deviation bounds, their convergence in probability, and stability of a count limit under centered perturbations |
| `CountInversion.lean` | Count inversion for sorted and unsorted samples, measurable sample quantiles, and commutation with nondecreasing transformations |
| `Concentration.lean` | Upper and lower Hoeffding bounds for independent bounded cluster variables, plus both sum-of-squared-sizes specializations |
| `ProbabilityTransform.lean` | The continuous-CDF probability transform, endpoints, interval probabilities, and specialization to the sample's actual marginal law |
| `LimitInversion.lean` | Half-line probability limits, moving cutoffs, Gaussian reflection, and continuity points including zero variance |
| `CoverageLimit.lean` | Exact rank correction, its limit, and transfer of a moving-count CLT to the actual transformed sample quantile's Gaussian CDF |
| `ClusterModel.lean` | Threshold events, signed local increments, and fixed and moving count CLTs derived from iid score vectors |
| `ClusterSample.lean` | Flattening clusters into the actual pooled sample, finite-prefix handling, and the pooled moving-count CLT |
| `ClusterCoverage.lean` | The end-to-end coverage CDF limit, the eventual ceiling-rank rule, and the indicator design-effect variance formula |
| `QuantileConcentration.lean` | The actual pooled quantile's two-sided finite-sample bound, support and boundary cases, and the normalized coverage tail under a continuous common marginal |
| `QuantileMoments.lean` | Expected excess above a cutoff, explicit truncation bounds, bounded second moments, and uniform integrability of squared coverage errors |
| `CoverageMoments.lean` | Absence of quantile atoms, tail integration, first and second moment limits, and the end-to-end rescaled variance limit with ceiling ranks |
| `DuplicatedPairs.lean` | Exact duplicated-sample ranks, permutation invariance, even threshold counts, and duplicated-pair count variance |
| `PairSymmetrization.lean` | Uniform random permutations, an exchangeable probability measure, common marginal distributions, and preservation of the duplicated-pair count law |
| `OrderStatisticRanks.lean` | Exact rank counts, the held-out rank identity, absence of iid ties, and uniform rank probabilities |
| `UniformOrderStatistic.lean` | The expected uniform order statistic r/(n+1), derived by rank symmetry and integration; transfer to arbitrary iid uniform samples |
| `DuplicatedPairModel.lean` | An explicit infinite iid sequence of exchangeable duplicated-pair clusters, its common uniform marginals, and independent latent observations |
| `DuplicatedPairDrift.lean` | The actual pooled sample, its exact expected quantile, ceiling ranks, and positive scaled drift limit |
| `DuplicatedPairMoments.lean` | Actual cluster-count variance, pair probabilities, and indicator correlation 1/3 |
| `ConditionalCoverage.lean` | Conditional coverage equals the true CDF at a measurable cutoff under an independent product model |
| `DuplicatedPairCounterexample.lean` | A single certificate for the model assumptions, actual coverage, and contradictory drift limits; its independent-test interpretation |
| `FinitePrefixCoverage.lean` | The exact ceiling policy, initial infinite cutoffs, eventual rank agreement, and the resulting variance limit |
| `RaggedQuantileConcentration.lean` | Unequal-size sample flattening, threshold counts, support, and finite-sample quantile concentration |
| `RaggedCoverage.lean` | Bounded unequal-size concentration and uniform integrability, including the original continuous-CDF scale |
| `TailLimits.lean` | Both one-sided endpoint limits in Proposition 1, assuming the corresponding tail coefficient exists |
| `FiniteSampleGuarantee.lean` | The prescribed correction and ceiling rank, the infinite cutoff, and failure and success probability bounds |
| `FourthMoment.lean` | Integrability of the fourth power and the exact bound E[Z⁴] ≤ M² for bounded unequal clusters |
| `RandomCutoff.lean` | Consistency of monotone empirical functions at a cutoff fitted on the same sample; continuous arithmetic in probability |
| `EstimatorConsistency.lean` | The sample-variance estimator, its original-score consistency at the actual fitted quantile, ceiling ranks, and absolute and relative variance comparisons |
| `BoundedArrayCLT.lean` | A bounded independent-array CLT proved by characteristic functions, including zero variance |
| `RaggedModel.lean` | R1–R4, common mean-pair variance, derived correlation continuity, and the unequal-size moving-count CLT |
| `RaggedLimit.lean` | Actual unequal-size quantile CDF limit, both moment limits, and rescaled variance limit |
| `RaggedScoreCoverage.lean` | Proposition 2 for original continuous scores and eventual ceiling ranks |
| `FiniteProfile.lean` | Size-biased mean/CV identity, effective-size ceiling, and square-root-scaled rank correction |
| `CopulaContinuity.lean` | The pair diagonal is 2-Lipschitz; indicator correlation is continuous at interior levels |
| `BetaMoments.lean` | Actual Beta means, second moments, variances, and the approximation’s stated moments |
| `GaussianIntegral.lean` | The zero Gaussian Edgeworth skewness integral |
| `PairMixture.lean` | An arbitrary identical/independent uniform-pair mixture, its marginals, and its indicator correlation |
| `CountExpectation.lean` | The exact expected-quantile/count integral on the unit interval |
| `WeightedTargets.lean` | The iid row-weighted CDF limit and its covariance difference from the cluster target |
| `SelectionTarget.lean` | Inclusion-weighted conditional CDF under an explicit independent acceptance draw |
| `UniformCountLaw.lean` | Exact binomial threshold-count probabilities from iid uniform samples |
| `BetaOrderPolynomial.lean` | Bernstein polynomial identity and the integer Beta CDF |
| `UniformBetaLaw.lean` | The exact Beta law of iid uniform order statistics |
| `ExactCoverageLaws.lean` | Exact Beta coverage laws for iid continuous scores and identical-member clusters |
| `SelectionCounterexample.lean` | Two populations with the same accepted law and different population coverage |
| `GaussianTail.lean` | Gaussian upper and lower pair-tail ratios vanish |
| `GaussianCopula.lean` | Actual correlated-normal construction, indicator formula, score covariance, and probability-endpoint limits |
| `GaussianCalculus.lean` | Normal CDF derivatives, density bounds, and the truncated first moment |
| `GaussianExpansion.lean` | Differentiation under the Gaussian conditional integral and the small-correlation limit |
| `BahadurInversion.lean` | Uniform local probability control, count inversion, and tightness without assuming the stochastic remainder |
| `ScoreCountLocal.lean` | Original-score local count variances, means, and convergence in probability |
| `LocalCDFDerivative.lean` | The local CDF expansion derived from a derivative at the target |
| `BahadurRepresentation.lean` | The actual ceiling-rank Bahadur formula with total sample size and empirical CDF |
| `ReflectionMixture.lean` | The exchangeable zero-score-correlation example and its exact indicator design effect |
| `FixedTargetCoverage.lean` | The original-score Gaussian CDF limit centered at the fixed target |
| `ZeroIndicatorCounterexample.lean` | Zero indicator correlation at a single cutoff without the independent-sample Beta law |
| `SupportingClaims.lean` | Continuous jitter, finite mean pair-correlation continuity, and the tail design-effect limit |

## Recheck

Run `bash formalization/check.sh` from the repository or extracted code-bundle root.
The checker builds every module in dependency order and removes prior local objects before each compilation.
Run `bash formalization/test_audit.sh` to test the audit against valid and deliberately unsafe fixtures.
The checker requires elan and may download the pinned mathlib checkout and its dependency cache.
Set `EXCEEDANCE_MATHLIB_DIR` to reuse an existing checkout at the exact pinned commit.
Set `EXCEEDANCE_LEAN_BUILD_DIR` to choose the compiled-output directory.
Use absolute paths for both settings.

The manuscript archive builder includes all Lean sources, this note, the inventory, and the checker.
The checker rejects unlisted source files.
This formalization update does not publish a release or rebuild the paper's PDFs.

## Assumptions and scope

The equal-size coverage theorem starts from iid measurable score vectors and a common continuous marginal CDF.
The unequal-size theorem uses independent bounded arrays and the common mean pair-correlation condition in R1–R4.
Both proofs concern the actual pooled quantile and include zero limiting variance.
They allow flat CDF regions and arbitrary dependence within each cluster.
Neither coverage theorem assumes a density, a moving-count limit, or moment convergence.

The estimator proof uses the actual sample-dependent cutoff and the sample-variance divisor.
Relative variance consistency requires a nonzero limiting variance.
The finite-sample guarantee includes the prescribed ceiling rank and the infinite-cutoff case.
Exceptional initial infinite cutoffs do not change the equal-size asymptotic conclusions.

The separate Bahadur theorem assumes a positive derivative at the target.
It proves the normalized remainder converges to zero in probability.
The Gaussian copula proof covers both probability endpoints and the expansion at zero correlation.
Exact Beta laws and Beta approximation moments are distinct results.
The approximation has no proved uniform error bound.
