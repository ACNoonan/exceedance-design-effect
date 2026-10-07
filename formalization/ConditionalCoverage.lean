import IndicatorVariance
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

/-- On the product model, conditioning on calibration data gives the true marginal CDF
    at any measurable data-dependent cutoff. No continuity assumption is needed. -/
theorem independent_test_conditional_coverage
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (q : Ω → ℝ) (hq : Measurable q) :
    (μ.prod ν)[indicator {z : Ω × ℝ | z.2 ≤ q z.1} |
      MeasurableSpace.comap Prod.fst mΩ] =ᵐ[μ.prod ν]
      (fun z : Ω × ℝ ↦ cdf ν (q z.1)) := by
  let m := MeasurableSpace.comap (Prod.fst : Ω × ℝ → Ω) mΩ
  letI : MeasurableSpace (Ω × ℝ) := @Prod.instMeasurableSpace Ω ℝ mΩ inferInstance
  have hm : m ≤ (inferInstance : MeasurableSpace (Ω × ℝ)) := by
    exact (show Measurable (Prod.fst : Ω × ℝ → Ω) from measurable_fst).comap_le
  let f := indicator {z : Ω × ℝ | z.2 ≤ q z.1}
  let g := fun z : Ω × ℝ ↦ cdf ν (q z.1)
  have hA : MeasurableSet {z : Ω × ℝ | z.2 ≤ q z.1} :=
    measurableSet_le measurable_snd (hq.comp measurable_fst)
  have hf : Integrable f (μ.prod ν) := (indicator_memLp hA).integrable (by norm_num)
  have hgm : Measurable[m] g :=
    (monotone_cdf ν).measurable.comp (hq.comp (comap_measurable Prod.fst))
  have hg : Integrable g (μ.prod ν) := by
    apply (integrable_const (1 : ℝ)).mono' (hgm.mono hm le_rfl).aestronglyMeasurable
    exact Eventually.of_forall (fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg ν _)]
      exact cdf_le_one ν _)
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hf
    (fun _ _ _ ↦ hg.integrableOn) _ hgm.stronglyMeasurable.aestronglyMeasurable
  intro s hs _
  obtain ⟨a, ha, rfl⟩ := hs
  have he : (Prod.fst : Ω × ℝ → Ω) ⁻¹' a = a ×ˢ (univ : Set ℝ) := by ext z; simp
  rw [he, setIntegral_prod g hg.integrableOn, setIntegral_prod f hf.integrableOn]
  simp only [Measure.restrict_univ]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x ↦ by
    change (∫ _ : ℝ, cdf ν (q x) ∂ν) = ∫ y, indicator {z : Ω × ℝ | z.2 ≤ q z.1} (x,y) ∂ν
    have hi : (fun y ↦ indicator {z : Ω × ℝ | z.2 ≤ q z.1} (x,y)) = indicator (Iic (q x)) := rfl
    rw [hi, indicator_mean measurableSet_Iic, integral_const]
    simp [cdf_eq_real])

end Exceedance
#print axioms Exceedance.independent_test_conditional_coverage
