import CoverageMoments

open MeasureTheory ProbabilityTheory
namespace Exceedance

/-- The Gaussian Edgeworth skewness term has zero integral. This does not bound an expansion remainder. -/
theorem gaussian_edgeworth_skewness_integral :
    (∫ z : ℝ, gaussianPDFReal 0 1 z*(z^2-1)) = 0 := by
  change (∫ z : ℝ, gaussianPDFReal 0 1 z • (z^2-1)) = 0
  rw [← integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have hsq : (∫ z : ℝ, z^2 ∂gaussianReal 0 1) = 1 := by
    have hh := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := 1)
    rw [variance_eq_integral (X := fun z : ℝ ↦ z) (by fun_prop)] at hh
    simpa only [integral_id_gaussianReal, sub_zero, NNReal.coe_one] using hh
  have hi : Integrable (fun z : ℝ ↦ z^2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' 2 (by norm_num)).integrable_sq
  rw [integral_sub hi (integrable_const 1), hsq]
  simp

end Exceedance
#print axioms Exceedance.gaussian_edgeworth_skewness_integral
