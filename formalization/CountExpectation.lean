import CoverageMoments

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Exact count-integral identity. No independence assumption is needed. -/
theorem sampleQuantile_expectation_count_integral {n : ℕ}
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hs : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc 0 1) (k : Fin n) :
    (∫ ω, sampleQuantile (fun i ↦ X i ω) k ∂μ) =
      ∫ t in Ioi (0:ℝ), μ.real {ω | (Finset.univ.filter (fun i ↦ X i ω ≤ t)).card ≤ k.val} := by
  classical
  have hq := measurable_sampleQuantile X hX k
  have hqs : ∀ᵐ ω ∂μ, sampleQuantile (fun i ↦ X i ω) k ∈ Icc 0 1 := by
    filter_upwards [ae_all_iff.mpr hs] with ω hω
    exact hω _
  have hi : Integrable (fun ω ↦ sampleQuantile (fun i ↦ X i ω) k) μ := by
    apply Integrable.of_bound hq.aestronglyMeasurable 1
    filter_upwards [hqs] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
    exact hω.2
  rw [hi.integral_eq_integral_meas_lt (hqs.mono (fun ω hω ↦ hω.1))]
  congr 1
  funext t
  congr 1
  ext ω
  simp only [mem_setOf_eq, ← not_le, sampleQuantile_le_iff]
  omega


/-- The exact integral on the unit interval, as displayed in Appendix B.7. -/
theorem sampleQuantile_expectation_count_unit_integral {n : ℕ}
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hs : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc 0 1) (k : Fin n) :
    (∫ ω, sampleQuantile (fun i ↦ X i ω) k ∂μ) =
      ∫ t in Ioc (0:ℝ) 1, μ.real {ω | (Finset.univ.filter (fun i ↦ X i ω ≤ t)).card ≤ k.val} := by
  classical
  rw [sampleQuantile_expectation_count_integral X hX hs k]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun t ht ↦ ht.1)
  intro t ht
  have ht1 : 1 < t := by
    have hh := ht.2
    simp only [mem_Ioc, not_and] at hh
    exact lt_of_not_ge (hh ht.1)
  apply (measureReal_eq_zero_iff).mpr
  have hz : ∀ᵐ ω ∂μ, ¬ (Finset.univ.filter (fun i ↦ X i ω ≤ t)).card ≤ k.val := by
    filter_upwards [ae_all_iff.mpr hs] with ω hω
    have he : Finset.univ.filter (fun i ↦ X i ω ≤ t) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro i _
      exact (hω i).2.trans ht1.le
    simp only [he, Finset.card_univ, Fintype.card_fin]
    exact not_le.mpr k.isLt
  simpa only [ae_iff, not_not] using hz

end Exceedance
#print axioms Exceedance.sampleQuantile_expectation_count_integral

#print axioms Exceedance.sampleQuantile_expectation_count_unit_integral
