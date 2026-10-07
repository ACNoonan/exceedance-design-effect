import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
namespace Exceedance

/-- Hoeffding bound at the independent-cluster level.
    Apply to each cluster's threshold count, with a=0 and b equal to its size.
    The result does not assume independence within a cluster. -/
theorem independent_bounded_sum_upper_tail {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι]
    (X : ι → Ω → ℝ) (a b : ι → ℝ)
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
    (hindep : iIndepFun X μ) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i, (X i ω - (∫ ω, X i ω ∂μ))} ≤
      Real.exp (-ε^2 / (2 * ∑ i, (‖b i-a i‖ / 2)^2)) := by
  classical
  have hi : iIndepFun (fun i ω ↦ X i ω - (∫ ω, X i ω ∂μ)) μ := hindep.comp (fun i x ↦ x-(∫ ω, X i ω ∂μ)) (fun _ ↦ measurable_id.sub_const _)
  have hs (i : ι) : HasSubgaussianMGF (fun ω ↦ X i ω - (∫ ω, X i ω ∂μ))
      ((‖b i-a i‖₊ / 2)^2) μ := hasSubgaussianMGF_of_mem_Icc (hX i) (hb i)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (μ := μ) (X := fun i ω ↦ X i ω-(∫ ω, X i ω ∂μ)) (c := fun i ↦ (‖b i-a i‖₊ / 2)^2) hi (s := Finset.univ) (fun i _ ↦ hs i) hε
  simpa using h

/-- The cluster-count specialization, with the usual sum of squared sizes. -/
theorem cluster_count_upper_tail {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι]
    (X : ι → Ω → ℝ) (m : ι → ℝ)
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 (m i))
    (hindep : iIndepFun X μ) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i, (X i ω - (∫ ω, X i ω ∂μ))} ≤
      Real.exp (-2*ε^2 / (∑ i, (m i)^2)) := by
  classical
  have h := independent_bounded_sum_upper_tail X (fun _ ↦ 0) m hX hb hindep ε hε
  have hd : (2 * ∑ i, (‖m i-0‖ / 2)^2) = (∑ i, (m i)^2)/2 := by
    simp only [sub_zero, div_pow, Real.norm_eq_abs, sq_abs]
    rw [← Finset.sum_div]
    ring
  rw [hd] at h
  convert h using 1; congr 1; ring


/-- Lower-tail counterpart, needed for the upper tail of the sample quantile. -/
theorem independent_bounded_sum_lower_tail {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι]
    (X : ι → Ω → ℝ) (a b : ι → ℝ)
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
    (hindep : iIndepFun X μ) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i, ((∫ ω, X i ω ∂μ) - X i ω)} ≤
      Real.exp (-ε^2 / (2 * ∑ i, (‖b i-a i‖ / 2)^2)) := by
  classical
  have hb' (i : ι) : ∀ᵐ ω ∂μ, -X i ω ∈ Set.Icc (-b i) (-a i) := by
    filter_upwards [hb i] with ω hω
    exact ⟨neg_le_neg hω.2, neg_le_neg hω.1⟩
  have hi : iIndepFun (fun i ω ↦ -X i ω) μ :=
    hindep.comp (fun _ x ↦ -x) (fun _ ↦ measurable_neg)
  have h := independent_bounded_sum_upper_tail (fun i ω ↦ -X i ω)
    (fun i ↦ -b i) (fun i ↦ -a i) (fun i ↦ (hX i).neg) hb' hi ε hε
  simpa only [integral_neg, neg_sub_neg] using h


/-- Lower-tail cluster bound with the same sum of squared cluster sizes. -/
theorem cluster_count_lower_tail {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι]
    (X : ι → Ω → ℝ) (m : ι → ℝ)
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 (m i))
    (hindep : iIndepFun X μ) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i, ((∫ ω, X i ω ∂μ) - X i ω)} ≤
      Real.exp (-2*ε^2 / (∑ i, (m i)^2)) := by
  classical
  have h := independent_bounded_sum_lower_tail X (fun _ ↦ 0) m hX hb hindep ε hε
  have hd : (2 * ∑ i, (‖m i-0‖ / 2)^2) = (∑ i, (m i)^2)/2 := by
    simp only [sub_zero, div_pow, Real.norm_eq_abs, sq_abs]
    rw [← Finset.sum_div]
    ring
  rw [hd] at h
  convert h using 1; congr 1; ring


end Exceedance
#print axioms Exceedance.independent_bounded_sum_upper_tail

#print axioms Exceedance.cluster_count_upper_tail

#print axioms Exceedance.independent_bounded_sum_lower_tail

#print axioms Exceedance.cluster_count_lower_tail
