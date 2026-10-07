import RaggedCoverage
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The exact fourth-moment constant in Appendix B.9. -/
theorem gaussian_tail_fourth_moment_integrable_and_bound (Z : Ω → ℝ) (hZ : Measurable Z)
    (M : ℝ) (hM : 0 < M)
    (htail : ∀ y, 0 ≤ y → μ.real {ω | y < |Z ω|} ≤ 2*Real.exp (-2*y^2/M)) :
    Integrable (fun ω ↦ (Z ω)^4) μ ∧ (∫ ω, (Z ω)^4 ∂μ) ≤ M^2 := by
  have hc : 0 < 2/M := by positivity
  have hi : IntegrableOn (fun t : ℝ ↦ 4*(t*Real.exp (-(2/M)*t))) (Ioi 0) := by
    have hh := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := 1) (p := 1) (by norm_num) (by norm_num) hc
    simpa only [IntegrableOn, Real.rpow_one] using hh.const_mul 4
  have hval : (∫ t : ℝ in Ioi 0, 4*(t*Real.exp (-(2/M)*t))) = M^2 := by
    rw [integral_const_mul]
    have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hc
    have hg : Real.Gamma 2 = 1 := by simpa only [Nat.cast_one, one_add_one_eq_two, Nat.factorial_one] using Real.Gamma_nat_eq_factorial 1
    norm_num only [show (2:ℝ)-1 = 1 by norm_num, Real.rpow_one,
      Real.rpow_two, hg, mul_one] at hh
    simp only [neg_mul] at hh ⊢
    rw [hh]
    field_simp
    ring
  have hl := lintegral_comp_eq_lintegral_meas_lt_mul (μ := μ)
    (f := fun ω ↦ (Z ω)^2) (g := fun t : ℝ ↦ 2*t)
    (Eventually.of_forall (fun ω ↦ sq_nonneg _)) (hZ.pow_const 2).aemeasurable
    (fun t _ ↦ (continuous_const.mul continuous_id).intervalIntegrable 0 t)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; have ht0 : 0 ≤ t := le_of_lt ht; positivity)
  have hid (y : ℝ) : (∫ t in (0:ℝ)..y, 2*t) = y^2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  simp_rw [hid, ← pow_mul] at hl
  norm_num only [show 2*2 = 4 by norm_num] at hl
  have hb : (∫⁻ ω, ENNReal.ofReal ((Z ω)^4) ∂μ) ≤ ENNReal.ofReal (M^2) := by
    rw [hl, ← hval, ofReal_integral_eq_lintegral_ofReal hi]
    · apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      have hh := gaussian_tail_square_tail Z M htail t ht0
      have hh' : μ {ω | t < (Z ω)^2} ≤ ENNReal.ofReal (2*Real.exp (-(2/M)*t)) := by
        rw [← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal hh
      calc
        _ ≤ ENNReal.ofReal (2*Real.exp (-(2/M)*t))*ENNReal.ofReal (2*t) :=
          mul_le_mul_left hh' _
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      positivity
  constructor
  · refine ⟨(hZ.pow_const 4).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun ω ↦ by positivity))]
    exact hb.trans_lt ENNReal.ofReal_lt_top
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun ω ↦ by positivity))
    (hZ.pow_const 4).aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal (sq_nonneg M))

/-- The fourth moment is bounded by the exact constant M². -/
theorem gaussian_tail_fourth_moment (Z : Ω → ℝ) (hZ : Measurable Z)
    (M : ℝ) (hM : 0 < M)
    (htail : ∀ y, 0 ≤ y → μ.real {ω | y < |Z ω|} ≤ 2*Real.exp (-2*y^2/M)) :
    (∫ ω, (Z ω)^4 ∂μ) ≤ M^2 :=
  (gaussian_tail_fourth_moment_integrable_and_bound Z hZ M hM htail).2

/-- Bounded unequal-size clusters satisfy the manuscript's fourth-moment bound. -/
theorem ragged_quantile_fourth_moment {b : ℕ} (m : Fin b → ℕ)
    (U : (j : Fin b) → Ω → Fin (m j) → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (M : ℝ) (hM : 0 < M) (hm : ∀ j, (m j : ℝ) ≤ M)
    (k : Fin (raggedSize m)) :
    (∫ ω, (normalizedRaggedQuantile m U k ω)^4 ∂μ) ≤ M^2 :=
  gaussian_tail_fourth_moment _ (measurable_normalizedRaggedQuantile m U hU k) M hM
    (ragged_normalized_quantile_tail m U hU hindep hunif M hM hm k)

end Exceedance
#print axioms Exceedance.gaussian_tail_fourth_moment
#print axioms Exceedance.ragged_quantile_fourth_moment
