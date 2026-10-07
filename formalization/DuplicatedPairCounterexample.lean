import DuplicatedPairDrift
import DuplicatedPairMoments
import QuantileConcentration
import ConditionalCoverage

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

local instance : MeasurableSpace (Equiv.Perm (Fin 4)) := ⊤

lemma unitUniform_cdf_all (t : ℝ) : cdf unitUniform t = max 0 (min t 1) := by
  have he : Iic t ∩ Icc (0:ℝ) 1 = Icc 0 (min t 1) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
    tauto
  rw [cdf_eq_real]
  simp only [measureReal_def, unitUniform, Measure.restrict_apply measurableSet_Iic,
    he, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal', max_comm]

theorem unitUniform_continuous_cdf : Continuous (cdf unitUniform) := by
  have he : (cdf unitUniform : ℝ → ℝ) = fun t ↦ max 0 (min t 1) := funext unitUniform_cdf_all
  rw [he]
  fun_prop

theorem pairCluster_actual_cdf (j : ℕ) (i : Fin 4) (t : ℝ) :
    pairSequenceLaw.real {ω | pairCluster j ω i ≤ t} = cdf unitUniform t := by
  rw [cdf_eq_real, ← pairCluster_marginal j i]
  exact (map_measureReal_apply
    (show Measurable (fun ω ↦ pairCluster j ω i) from (measurable_pi_apply i).comp (measurable_pairCluster j)) measurableSet_Iic).symm

noncomputable def pairCorrelation (p : ℝ) : ℝ :=
  (pairSequenceLaw.real {ω | pairCluster 0 ω 0 ≤ p ∧ pairCluster 0 ω 1 ≤ p} - p^2) /
    (p*(1-p))

lemma pairCorrelation_eq (p : ℝ) (hp : p ∈ Ioo 0 1) : pairCorrelation p = 1/3 :=
  pairCluster_indicator_correlation 0 p hp 0 1 (by decide)

theorem pairCorrelation_derivative (p : ℝ) (hp : p ∈ Ioo 0 1) :
    HasDerivAt pairCorrelation 0 p := by
  apply (hasDerivAt_const p (1/3 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hp.1 hp.2] with q hq
  exact pairCorrelation_eq q hq

/-- Coverage is the true marginal CDF at the actual pooled sample cutoff. -/
noncomputable def pairCounterexampleCoverage (h : ℕ) (ω : PairSequence) : ℝ :=
  cdf unitUniform (pairCounterexampleCutoff h ω)

lemma pairCounterexample_coverage_eq_cutoff (h : ℕ) :
    pairCounterexampleCoverage h =ᵐ[pairSequenceLaw] pairCounterexampleCutoff h := by
  have hs := pooled_quantile_support pairCluster measurable_pairCluster
    (fun j i t ht0 ht1 ↦ pairCluster_cdf j i t ⟨ht0,ht1⟩)
    (10*(h+1)) (pairCounterexampleRank h)
  filter_upwards [hs] with ω hω
  change cdf unitUniform (pairCounterexampleCutoff h ω) = _
  rw [cdf_eq_real]
  exact unitUniform_cdf _ hω.1 hω.2

noncomputable def pairActualScaledDrift (h : ℕ) : ℝ :=
  (10*(h+1 : ℕ) : ℝ)*((∫ ω, pairCounterexampleCoverage h ω ∂pairSequenceLaw) -
    (((pairCounterexampleRank h).val+1 : ℕ) : ℝ)/((((10*(h+1))*4 : ℕ) : ℝ)+1))

theorem pairActualScaledDrift_limit : Tendsto pairActualScaledDrift atTop (nhds (1/40 : ℝ)) := by
  have he : pairActualScaledDrift = fun h : ℕ ↦ (10*(h+1 : ℕ) : ℝ)*
      ((∫ ω, pairCounterexampleCutoff h ω ∂pairSequenceLaw) -
        (36*(h+1 : ℕ)+1 : ℝ)/(40*(h+1 : ℕ)+1)) := by
    funext h
    rw [pairActualScaledDrift, integral_congr_ae (pairCounterexample_coverage_eq_cutoff h)]
    simp only [pairCounterexampleRank, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  rw [he]
  exact pairCounterexample_drift_limit

noncomputable def pairPredictedDrift : ℝ :=
  (3/8 : ℝ)*((1-2*(9/10))*pairCorrelation (9/10) +
    (9/10)*(1-9/10)*deriv pairCorrelation (9/10))

theorem pairPredictedDrift_eq : pairPredictedDrift = -1/10 := by
  unfold pairPredictedDrift
  rw [pairCorrelation_eq _ (by norm_num), (pairCorrelation_derivative _ (by norm_num)).deriv]
  norm_num

/-- The fully constructed model violates the withdrawn drift limit for actual coverage. -/
theorem duplicated_pair_drift_counterexample :
    ¬ Tendsto pairActualScaledDrift atTop (nhds pairPredictedDrift) := by
  intro h
  have he := tendsto_nhds_unique pairActualScaledDrift_limit h
  rw [pairPredictedDrift_eq] at he
  norm_num at he

/-- All principal assumptions and the contradictory limits hold in one explicit model. -/
theorem duplicated_pair_counterexample_certificate :
    iIndepFun pairCluster pairSequenceLaw ∧
    (∀ j, IdentDistrib (pairCluster j) (pairCluster 0) pairSequenceLaw pairSequenceLaw) ∧
    (∀ (j : ℕ) (σ : Equiv.Perm (Fin 4)), (pairSequenceLaw.map (pairCluster j)).map (fun x i ↦ x (σ i)) =
      pairSequenceLaw.map (pairCluster j)) ∧
    Continuous (cdf unitUniform) ∧
    (∀ j i t, pairSequenceLaw.real {ω | pairCluster j ω i ≤ t} = cdf unitUniform t) ∧
    (Var[fun ω ↦ thresholdCount (9/10) (pairCluster 0 ω); pairSequenceLaw] = 18/25) ∧
    (∀ p ∈ Ioo 0 1, pairCorrelation p = 1/3 ∧ HasDerivAt pairCorrelation 0 p) ∧
    (∀ h, (pairCounterexampleRank h).val+1 = ⌈(((10*(h+1))*4 : ℕ)+1 : ℝ)*(9/10)⌉₊) ∧
    Tendsto pairActualScaledDrift atTop (nhds (1/40 : ℝ)) ∧
    pairPredictedDrift = -1/10 ∧
    ¬ Tendsto pairActualScaledDrift atTop (nhds pairPredictedDrift) := by
  refine ⟨pairCluster_independent, pairCluster_identDistrib, pairCluster_exchangeable,
    unitUniform_continuous_cdf, pairCluster_actual_cdf, ?_,
    fun p hp ↦ ⟨pairCorrelation_eq p hp, pairCorrelation_derivative p hp⟩,
    pairCounterexampleRank_ceil, pairActualScaledDrift_limit, pairPredictedDrift_eq,
    duplicated_pair_drift_counterexample⟩
  rw [pairCluster_count_variance 0 (9/10) (by norm_num)]
  norm_num

/-- The same counterexample coverage is the conditional probability for an independent test point. -/
theorem pairCounterexample_conditional_coverage (h : ℕ) :
    (pairSequenceLaw.prod unitUniform)[indicator {z : PairSequence × ℝ |
      z.2 ≤ pairCounterexampleCutoff h z.1} |
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace PairSequence)]
      =ᵐ[pairSequenceLaw.prod unitUniform]
      (fun z : PairSequence × ℝ ↦ pairCounterexampleCoverage h z.1) := by
  apply independent_test_conditional_coverage
  apply measurable_sampleQuantile
  intro i
  exact (measurable_pi_apply (finProdFinEquiv.symm i).2).comp
    (measurable_pairCluster (finProdFinEquiv.symm i).1.val)

end Exceedance
#print axioms Exceedance.duplicated_pair_counterexample_certificate

#print axioms Exceedance.pairCounterexample_conditional_coverage
