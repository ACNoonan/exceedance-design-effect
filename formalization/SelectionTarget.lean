import UniformOrderStatistic
import Mathlib.Probability.ConditionalProbability

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An independent uniform draw implements retention probability w at each population observation. -/
theorem selection_joint_probability (w : Ω → ℝ) (hw : Measurable w)
    (hb : ∀ ω, w ω ∈ Icc 0 1) (A : Set Ω) (hA : MeasurableSet A) :
    (μ.prod unitUniform).real {z | z.1 ∈ A ∧ z.2 ≤ w z.1} = ∫ ω in A, w ω ∂μ := by
  let B := {z : Ω × ℝ | z.1 ∈ A ∧ z.2 ≤ w z.1}
  have hB : MeasurableSet B := (measurable_fst hA).inter
    (measurableSet_le measurable_snd (hw.comp measurable_fst))
  have hi : Integrable (indicator B) (μ.prod unitUniform) :=
    (indicator_memLp hB).integrable (by norm_num)
  rw [← indicator_mean hB, integral_prod _ hi, ← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards with ω
  by_cases ha : ω ∈ A
  · have he : (fun u ↦ indicator B (ω,u)) = indicator (Iic (w ω)) := by
      funext u
      simp [indicator, B, ha, Set.indicator]
    rw [he, indicator_mean measurableSet_Iic, unitUniform_cdf _ (hb ω).1 (hb ω).2,
      indicator_of_mem ha]
  · have he : (fun u ↦ indicator B (ω,u)) = (fun _ ↦ (0:ℝ)) := by
      funext u
      simp [indicator, B, ha, Set.indicator]
    rw [he, integral_zero, indicator_of_notMem ha]

/-- Conditioning the retention model gives the inclusion-weighted population law. -/
theorem selection_conditional_probability (w : Ω → ℝ) (hw : Measurable w)
    (hb : ∀ ω, w ω ∈ Icc 0 1) (A : Set Ω) (hA : MeasurableSet A) :
    ((μ.prod unitUniform)[| {z : Ω × ℝ | z.2 ≤ w z.1}]).real
      {z : Ω × ℝ | z.1 ∈ A} = (∫ ω in A, w ω ∂μ)/(∫ ω, w ω ∂μ) := by
  have hB : MeasurableSet {z : Ω × ℝ | z.2 ≤ w z.1} :=
    measurableSet_le measurable_snd (hw.comp measurable_fst)
  have hnum := selection_joint_probability (μ := μ) w hw hb A hA
  have hden := selection_joint_probability (μ := μ) w hw hb univ MeasurableSet.univ
  simp only [mem_univ, true_and, Measure.restrict_univ] at hden
  rw [measureReal_def, cond_apply hB, ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((μ.prod unitUniform).real {z | z.2 ≤ w z.1})⁻¹ *
    (μ.prod unitUniform).real ({z | z.2 ≤ w z.1} ∩ {z | z.1 ∈ A}) = _
  have he : {z : Ω × ℝ | z.2 ≤ w z.1} ∩ {z | z.1 ∈ A} =
      {z | z.1 ∈ A ∧ z.2 ≤ w z.1} := by ext z; simp [and_comm]
  rw [he, hnum, hden]
  ring

/-- The selected score CDF is the normalized inclusion-weighted integral. -/
theorem selected_score_cdf (S : Ω → ℝ) (hS : Measurable S)
    (pi : ℝ → ℝ) (hpi : Measurable pi) (hb : ∀ s, pi s ∈ Icc 0 1) (t : ℝ) :
    ((μ.prod unitUniform)[| {z : Ω × ℝ | z.2 ≤ pi (S z.1)}]).real
      {z : Ω × ℝ | S z.1 ≤ t} =
        (∫ ω in {ω | S ω ≤ t}, pi (S ω) ∂μ)/(∫ ω, pi (S ω) ∂μ) :=
  selection_conditional_probability (fun ω ↦ pi (S ω)) (hpi.comp hS)
    (fun ω ↦ hb (S ω)) _ (measurableSet_le hS measurable_const)

end Exceedance
#print axioms Exceedance.selection_joint_probability
#print axioms Exceedance.selection_conditional_probability
#print axioms Exceedance.selected_score_cdf
