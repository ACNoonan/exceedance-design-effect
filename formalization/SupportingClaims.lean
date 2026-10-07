import ReflectionMixture
import CopulaContinuity
import TailLimits
import EstimatorConsistency

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

/-- Independent continuous jitter removes marginal atoms, even if the score has atoms. -/
theorem independent_jitter_no_atoms {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (e : ℝ) (he : e ≠ 0) (t : ℝ) :
    (μ.prod unitUniform) {z | S z.1+e*z.2=t} = 0 := by
  rw [Measure.prod_apply (by measurability)]
  have hzero (ω : Ω) : unitUniform (Prod.mk ω ⁻¹' {z | S z.1+e*z.2=t})=0 := by
    have hh : Prod.mk ω ⁻¹' {z | S z.1+e*z.2=t} = {(t-S ω)/e} := by
      ext x
      simp only [mem_preimage,mem_setOf_eq,mem_singleton_iff]
      constructor
      · intro h; apply (eq_div_iff he).mpr; nlinarith
      · intro h; have hh := (eq_div_iff he).mp h; nlinarith
    rw [hh,measure_singleton]
  simp only [hzero,lintegral_zero]

/-- Atomlessness of the actual augmented score implies continuity of its marginal CDF. -/
theorem independent_jitter_continuous_cdf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (e : ℝ) (he : e ≠ 0) :
    Continuous (fun t ↦ (μ.prod unitUniform).real {z | S z.1+e*z.2 ≤ t}) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let U := fun z : Ω × ℝ ↦ fun _ : Fin 1 ↦ S z.1+e*z.2
  have hh := thresholdCount_moment_continuousAt U (by dsimp [U]; fun_prop) p
    (fun _ ↦ independent_jitter_no_atoms μ S hS e he p) 1
  have hEq t : (∫ z, (thresholdCount t (U z))^1 ∂μ.prod unitUniform) =
      (μ.prod unitUniform).real {z | S z.1+e*z.2 ≤ t} := by
    simp only [thresholdCount,Fin.sum_univ_one,pow_one,U]
    change (∫ z, indicator {z | S z.1+e*z.2 ≤ t} z ∂μ.prod unitUniform) = _
    exact indicator_mean (by measurability)
  simpa only [hEq] using hh

/-- Finite mean pair correlations inherit continuity at interior levels. -/
theorem mean_pair_correlation_continuous {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (U V : ι → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hV : ∀ i, Measurable (V i))
    (hu : ∀ i, ∀ t ∈ Icc (0:ℝ) 1, μ.real {ω | U i ω ≤ t} = t)
    (hv : ∀ i, ∀ t ∈ Icc (0:ℝ) 1, μ.real {ω | V i ω ≤ t} = t)
    (p : ℝ) (hp : p ∈ Ioo 0 1) :
    ContinuousAt (fun t ↦ (∑ i, (μ.real {ω | U i ω ≤ t ∧ V i ω ≤ t}-t^2)/(t*(1-t)))/
      (Fintype.card ι : ℝ)) p := by
  apply ContinuousAt.div_const
  exact tendsto_finsetSum _ (fun i _ ↦ pair_indicator_correlation_continuousAt
    (U i) (V i) (hU i) (hV i) (hu i) (hv i) p hp)

/-- The upper-tail coefficient determines the limit of the design effect. -/
theorem design_effect_upper_tail (d : ℝ → ℝ) (L m : ℝ)
    (h : Tendsto (fun p ↦ (1-2*p+d p)/(1-p)) (nhdsWithin 1 (Ioo 0 1)) (nhds L)) :
    Tendsto (fun p ↦ 1+(m-1)*((d p-p^2)/(p*(1-p)))) (nhdsWithin 1 (Ioo 0 1))
      (nhds (1+(m-1)*L)) :=
  ((indicator_correlation_upper_tail d L h).const_mul (m-1)).const_add 1


/-- Complementing both threshold indicators preserves their covariance and variances. -/
theorem complement_indicator_covariance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    cov[indicator Aᶜ,indicator Bᶜ;μ] = cov[indicator A,indicator B;μ] ∧
    Var[indicator Aᶜ;μ] = Var[indicator A;μ] ∧ Var[indicator Bᶜ;μ] = Var[indicator B;μ] := by
  classical
  have hc (C : Set Ω) : indicator Cᶜ = (fun ω ↦ 1-indicator C ω) := by
    funext ω
    simp only [indicator,Set.indicator,mem_compl_iff]
    split_ifs <;> norm_num
  have hiA := (indicator_memLp (μ := μ) hA).integrable (by norm_num)
  have hiB := (indicator_memLp (μ := μ) hB).integrable (by norm_num)
  rw [hc A,hc B]
  constructor
  · rw [covariance_const_sub_left hiA,covariance_const_sub_right hiB,neg_neg]
  exact ⟨variance_const_sub (indicator_memLp hA).aestronglyMeasurable 1,
    variance_const_sub (indicator_memLp hB).aestronglyMeasurable 1⟩

end Exceedance
#print axioms Exceedance.independent_jitter_continuous_cdf
#print axioms Exceedance.mean_pair_correlation_continuous
#print axioms Exceedance.design_effect_upper_tail

#print axioms Exceedance.complement_indicator_covariance
