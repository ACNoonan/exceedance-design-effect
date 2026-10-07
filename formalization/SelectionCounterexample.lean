import SelectionTarget
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

noncomputable def tiltedDensity (a x : ℝ) : ℝ := 1+a*(2*x-1)
noncomputable def tiltedUniform (a : ℝ) : Measure ℝ :=
  unitUniform.withDensity (fun x ↦ ENNReal.ofReal (tiltedDensity a x))

lemma tiltedDensity_pos (a : ℝ) (ha : a ∈ Ioo 0 1) (x : ℝ) (hx : x ∈ Icc 0 1) :
    0 < tiltedDensity a x := by dsimp [tiltedDensity]; nlinarith [ha.1,ha.2,hx.1]

lemma tiltedDensity_integral (a p : ℝ) (hp : 0 ≤ p) :
    (∫ x in Icc (0:ℝ) p, tiltedDensity a x) = p-a*p*(1-p) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hp]
  have he : (fun x ↦ tiltedDensity a x) = (fun x ↦ (1-a)+2*a*x) := by funext x; dsimp [tiltedDensity]; ring
  have hi : IntervalIntegrable (fun x : ℝ ↦ 2*a*x) volume 0 p := (continuous_id.intervalIntegrable _ _).const_mul _
  rw [he, intervalIntegral.integral_add intervalIntegrable_const hi,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  ring

lemma tiltedUniform_real (a : ℝ) (ha : a ∈ Ioo 0 1) (A : Set ℝ) (hA : MeasurableSet A) :
    (tiltedUniform a).real A = ∫ x in A, tiltedDensity a x ∂unitUniform := by
  rw [measureReal_def, tiltedUniform, withDensity_apply _ hA]
  symm
  apply integral_eq_lintegral_of_nonneg_ae
  · filter_upwards [ae_restrict_of_ae unitUniform_ae] with x hx
    exact (tiltedDensity_pos a ha x hx).le
  · exact (show Measurable (tiltedDensity a) by unfold tiltedDensity; fun_prop).aestronglyMeasurable

lemma tiltedUniform_probability (a : ℝ) (ha : a ∈ Ioo 0 1) : IsProbabilityMeasure (tiltedUniform a) := by
  have he : (tiltedUniform a).real univ = 1 := by
    rw [tiltedUniform_real a ha univ MeasurableSet.univ, Measure.restrict_univ]
    change (∫ x in Icc (0:ℝ) 1, tiltedDensity a x) = 1
    rw [tiltedDensity_integral a 1 zero_le_one]
    ring
  constructor
  exact (ENNReal.toReal_eq_one_iff _).mp he

/-- The tilted population has the explicitly different coverage in Appendix A. -/
theorem tilted_population_cdf (a : ℝ) (ha : a ∈ Ioo 0 1) (p : ℝ) (hp : p ∈ Icc 0 1) :
    (tiltedUniform a).real (Iic p) = p-a*p*(1-p) := by
  rw [tiltedUniform_real a ha _ measurableSet_Iic]
  have he : Iic p ∩ Icc (0:ℝ) 1 = Icc 0 p := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]; constructor
    · intro h; exact ⟨h.2.1,h.1⟩
    · intro h; exact ⟨h.2,h.1,h.2.trans hp.2⟩
  rw [unitUniform, Measure.restrict_restrict measurableSet_Iic, he]
  exact tiltedDensity_integral a p hp.1

/-- Retention is only relevant on the population support. -/
noncomputable def tiltedRetention (a x : ℝ) : ℝ :=
  if x ∈ Icc (0:ℝ) 1 then (1-a)/tiltedDensity a x else 0

lemma tiltedRetention_measurable (a : ℝ) : Measurable (tiltedRetention a) := by
  unfold tiltedRetention tiltedDensity
  exact Measurable.ite measurableSet_Icc (by fun_prop) measurable_const

lemma tiltedRetention_bounds (a : ℝ) (ha : a ∈ Ioo 0 1) (x : ℝ) :
    tiltedRetention a x ∈ Icc 0 1 := by
  by_cases hx : x ∈ Icc (0:ℝ) 1
  · rw [tiltedRetention, if_pos hx]
    refine ⟨div_nonneg (sub_pos.mpr ha.2).le (tiltedDensity_pos a ha x hx).le, ?_⟩
    apply (div_le_one (tiltedDensity_pos a ha x hx)).mpr
    dsimp [tiltedDensity]
    nlinarith [ha.1,hx.1]
  · simp [tiltedRetention,hx]

lemma tilted_retention_integral (a : ℝ) (ha : a ∈ Ioo 0 1) (A : Set ℝ) (hA : MeasurableSet A) :
    (∫ x in A, tiltedRetention a x ∂tiltedUniform a) = (1-a)*unitUniform.real A := by
  rw [tiltedUniform, setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (show AEMeasurable (fun x ↦ ENNReal.ofReal (tiltedDensity a x)) (unitUniform.restrict A) by unfold tiltedDensity; fun_prop)
    (Eventually.of_forall (fun x ↦ ENNReal.ofReal_lt_top)) _ hA]
  have he : (∫ x in A, (ENNReal.ofReal (tiltedDensity a x)).toReal • tiltedRetention a x ∂unitUniform) =
      ∫ _x in A, (1-a) ∂unitUniform := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae unitUniform_ae] with x hx
    rw [ENNReal.toReal_ofReal (tiltedDensity_pos a ha x hx).le, smul_eq_mul,
      tiltedRetention, if_pos hx, mul_div_cancel₀ _ (tiltedDensity_pos a ha x hx).ne']
  rw [he, setIntegral_const]
  simp [mul_comm]

/-- The accepted-score CDF is uniform despite the different population CDF. -/
theorem tilted_accepted_cdf (a : ℝ) (ha : a ∈ Ioo 0 1) (p : ℝ) (hp : p ∈ Icc 0 1) :
    (((tiltedUniform a).prod unitUniform)[| {z : ℝ × ℝ | z.2 ≤ tiltedRetention a z.1}]).real
      {z : ℝ × ℝ | z.1 ≤ p} = p := by
  letI := tiltedUniform_probability a ha
  have hh : (((tiltedUniform a).prod unitUniform)[| {z : ℝ × ℝ | z.2 ≤ tiltedRetention a z.1}]).real
      {z : ℝ × ℝ | z.1 ≤ p} =
      (∫ x in Iic p, tiltedRetention a x ∂tiltedUniform a)/(∫ x, tiltedRetention a x ∂tiltedUniform a) :=
    selection_conditional_probability (tiltedRetention a) (tiltedRetention_measurable a)
      (tiltedRetention_bounds a ha) (Iic p) measurableSet_Iic
  rw [hh]
  rw [tilted_retention_integral a ha _ measurableSet_Iic]
  have hd := tilted_retention_integral a ha univ MeasurableSet.univ
  simp only [Measure.restrict_univ, probReal_univ, mul_one] at hd
  rw [hd, unitUniform_cdf p hp.1 hp.2]
  have hne : 1-a ≠ 0 := (sub_pos.mpr ha.2).ne'
  field_simp


/-- At the manuscript's numerical example, the population coverage deficit is 0.081. -/
theorem selection_example_coverage_deficit :
    (9/10:ℝ) - (tiltedUniform (9/10)).real (Iic (9/10)) = 81/1000 := by
  rw [tilted_population_cdf (9/10) (by norm_num : (9/10:ℝ) ∈ Ioo 0 1)
    (9/10) (by norm_num : (9/10:ℝ) ∈ Icc 0 1)]
  norm_num

end Exceedance
#print axioms Exceedance.tilted_population_cdf
#print axioms Exceedance.tilted_accepted_cdf

#print axioms Exceedance.selection_example_coverage_deficit
