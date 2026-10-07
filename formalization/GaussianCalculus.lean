import GaussianCopula
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

lemma standardGaussian_cdf_integral (t : ℝ) :
    cdf (gaussianReal 0 1) t = ∫ x in Iic t, gaussianPDFReal 0 1 x := by
  rw [cdf_eq_real,measureReal_def,gaussianReal_apply_eq_integral 0 (by norm_num),
    ENNReal.toReal_ofReal (integral_nonneg (fun x ↦ gaussianPDFReal_nonneg _ _ _))]

lemma standardGaussian_cdf_hasDerivAt (t : ℝ) :
    HasDerivAt (fun t ↦ cdf (gaussianReal 0 1) t) (gaussianPDFReal 0 1 t) t := by
  have hc : Continuous (gaussianPDFReal 0 1) := by unfold gaussianPDFReal; fun_prop
  have he (y : ℝ) : cdf (gaussianReal 0 1) y =
      cdf (gaussianReal 0 1) 0 + ∫ x in (0:ℝ)..y, gaussianPDFReal 0 1 x := by
    rw [standardGaussian_cdf_integral,standardGaussian_cdf_integral,
      ← intervalIntegral.integral_Iic_sub_Iic (integrable_gaussianPDFReal 0 1).integrableOn
        (integrable_gaussianPDFReal 0 1).integrableOn]
    ring
  rw [show (fun y ↦ cdf (gaussianReal 0 1) y) =
    (fun y ↦ cdf (gaussianReal 0 1) 0 + ∫ x in (0:ℝ)..y, gaussianPDFReal 0 1 x) from funext he]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _

lemma standardGaussian_pdf_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x := by
  have he : gaussianPDFReal 0 1 = (fun x : ℝ ↦ (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-(x^2)/2)) := by
    funext x; simp [gaussianPDFReal]
  rw [he]
  convert (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul ((Real.sqrt (2*Real.pi))⁻¹) using 1 <;> try rfl
  simp only [Pi.neg_apply,Pi.pow_apply,id_eq]
  ring

lemma standardGaussian_pdf_bound (x : ℝ) :
    |gaussianPDFReal 0 1 x| ≤ (Real.sqrt (2*Real.pi))⁻¹ := by
  rw [abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
  unfold gaussianPDFReal
  simp only [NNReal.coe_one,mul_one,sub_zero,one_div]
  apply mul_le_of_le_one_right (by positivity)
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])

lemma standardGaussian_truncated_mean (z : ℝ) :
    (∫ x in Iic z, -x ∂gaussianReal 0 1) = gaussianPDFReal 0 1 z := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num),
    setIntegral_withDensity_eq_setIntegral_toReal_smul
      (measurable_gaussianPDF _ _) (Eventually.of_forall (fun _ ↦ gaussianPDF_lt_top)) _ measurableSet_Iic]
  simp only [toReal_gaussianPDF,smul_eq_mul]
  have he : (fun x : ℝ ↦ gaussianPDFReal 0 1 x * -x) = (fun x ↦ -x*gaussianPDFReal 0 1 x) := by funext x; ring
  rw [he]
  have hi : Integrable (fun x : ℝ ↦ -x*gaussianPDFReal 0 1 x) := by
    have hh := (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).const_mul (-(Real.sqrt (2*Real.pi))⁻¹)
    convert hh using 1
    funext x
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,one_div]
    rw [show -(2:ℝ)⁻¹*x^2 = -(x^2)/2 by ring]
    ring
  have ht : Tendsto (gaussianPDFReal 0 1) atBot (nhds 0) := by
    have hs : Tendsto (fun x : ℝ ↦ x^2) atBot atTop := by
      have hh := (tendsto_neg_atBot_atTop : Tendsto (fun x : ℝ ↦ -x) atBot atTop).atTop_mul_atTop₀
        tendsto_neg_atBot_atTop
      simpa only [neg_mul_neg,pow_two] using hh
    have hh := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hs.const_mul_atTop (by norm_num : (0:ℝ) < 1/2)))
    have hl := hh.const_mul ((Real.sqrt (2*Real.pi))⁻¹)
    convert hl using 1
    · funext x
      simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,one_div,Function.comp_apply]
      congr 1
      congr 1
      ring
    · simp
  simpa only [sub_zero] using integral_Iic_of_hasDerivAt_of_tendsto'
    (fun x _ ↦ standardGaussian_pdf_hasDerivAt x) hi.integrableOn ht

end Exceedance
#print axioms Exceedance.standardGaussian_cdf_hasDerivAt
#print axioms Exceedance.standardGaussian_truncated_mean
