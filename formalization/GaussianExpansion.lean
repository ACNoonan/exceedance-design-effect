import GaussianCalculus

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

noncomputable def gaussianConditionalArg (r z x : ℝ) : ℝ := (z-r*x)/Real.sqrt (1-r^2)
noncomputable def gaussianConditionalArgDeriv (r z x : ℝ) : ℝ :=
  -x/Real.sqrt (1-r^2)+(z-r*x)*r/(Real.sqrt (1-r^2))^3

lemma gaussianConditionalArg_hasDerivAt (r z x : ℝ) (hr : r ∈ Ioo (-1) 1) :
    HasDerivAt (fun r ↦ gaussianConditionalArg r z x) (gaussianConditionalArgDeriv r z x) r := by
  have hpos : 0 < 1-r^2 := by nlinarith [hr.1,hr.2]
  have hs : Real.sqrt (1-r^2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hd := ((hasDerivAt_const r z).sub ((hasDerivAt_id r).mul_const x)).div
    (((hasDerivAt_const r (1:ℝ)).sub ((hasDerivAt_id r).pow 2)).sqrt hpos.ne') hs
  convert hd using 1 <;> try rfl
  dsimp [gaussianConditionalArgDeriv]
  field_simp
  <;> ring

lemma gaussianConditionalArgDeriv_bound (r z x : ℝ) (hr : r ∈ Ioo (-(1/2)) (1/2)) :
    |gaussianConditionalArgDeriv r z x| ≤ 10*|x|+8*|z| := by
  have ha : |r| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hr.1,hr.2]
  have hpos : 0 < 1-r^2 := by nlinarith [hr.1,hr.2]
  have hs : (1/2:ℝ) ≤ Real.sqrt (1-r^2) := by
    apply (Real.le_sqrt (by norm_num) hpos.le).mpr
    nlinarith [hr.1,hr.2]
  have hspos := Real.sqrt_pos.mpr hpos
  have hs3 : (1/8:ℝ) ≤ (Real.sqrt (1-r^2))^3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hs 3]
  have hab : |z-r*x| ≤ |z|+|x| := by
    calc
      _ ≤ |z|+|r*x| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le z (-(r*x))
      _ ≤ |z|+|x| := by rw [abs_mul]; nlinarith [abs_nonneg x]
  unfold gaussianConditionalArgDeriv
  calc
    _ ≤ |-x/Real.sqrt (1-r^2)|+|(z-r*x)*r/(Real.sqrt (1-r^2))^3| := abs_add_le _ _
    _ = |x|/Real.sqrt (1-r^2)+(|z-r*x| * |r|)/(Real.sqrt (1-r^2))^3 := by
      rw [abs_div,abs_div,abs_neg,abs_mul,abs_of_pos hspos,abs_of_pos (pow_pos hspos 3)]
    _ ≤ 2*|x|+8*(|z|+|x|) := by
      apply add_le_add
      · apply (div_le_iff₀ hspos).mpr
        nlinarith [abs_nonneg x]
      · apply (div_le_iff₀ (pow_pos hspos 3)).mpr
        have hn : |z-r*x| * |r| ≤ |z|+|x| :=
          (mul_le_mul_of_nonneg_left ha (abs_nonneg _)).trans (by simpa using hab)
        nlinarith [abs_nonneg z,abs_nonneg x]
    _ = _ := by ring

/-- The bivariate normal diagonal equals its conditional-normal integral. -/
lemma bivariateNormalCDF_conditional (r z : ℝ) (hr : r ∈ Ioo (-1) 1) :
    bivariateNormalCDF r z z = ∫ x in Iic z, cdf (gaussianReal 0 1) (gaussianConditionalArg r z x)
      ∂gaussianReal 0 1 := by
  let A := {w : ℝ × ℝ | w.1 ≤ z ∧ correlatedGaussian r w ≤ z}
  have hA : MeasurableSet A := (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le (correlatedGaussian_measurable r) measurable_const)
  have hi : Integrable (indicator A) standardGaussianPair := (indicator_memLp hA).integrable (by norm_num)
  change standardGaussianPair.real A = _
  rw [← indicator_mean hA]
  change (∫ w, indicator A w ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) = _
  rw [integral_prod _ hi,← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ≤ z
  · have hs : 0 < Real.sqrt (1-r^2) := Real.sqrt_pos.mpr (by nlinarith [hr.1,hr.2])
    have he : (fun y ↦ indicator A (x,y)) = indicator (Iic (gaussianConditionalArg r z x)) := by
      funext y
      have hh : r*x+Real.sqrt (1-r^2)*y ≤ z ↔ y ≤ (z-r*x)/Real.sqrt (1-r^2) := by
        rw [le_div_iff₀ hs]
        constructor <;> intro h <;> nlinarith
      simp [indicator,A,Set.indicator,hx,correlatedGaussian,gaussianConditionalArg,hh]
    rw [he,indicator_mean measurableSet_Iic,indicator_of_mem (show x ∈ Iic z from hx),cdf_eq_real]
  · have he : (fun y ↦ indicator A (x,y)) = (fun _ ↦ (0:ℝ)) := by
      funext y; simp [indicator,A,Set.indicator,hx]
    rw [he,integral_zero,indicator_of_notMem (show x ∉ Iic z from hx)]


/-- Differentiation under the conditional-normal integral gives the exact slope at independence. -/
theorem bivariateNormalCDF_hasDerivAt_zero (z : ℝ) :
    HasDerivAt (fun r ↦ bivariateNormalCDF r z z) ((gaussianPDFReal 0 1 z)^2) 0 := by
  let F := fun r x ↦ cdf (gaussianReal 0 1) (gaussianConditionalArg r z x)
  let D := fun r x ↦ gaussianPDFReal 0 1 (gaussianConditionalArg r z x)*gaussianConditionalArgDeriv r z x
  let c := (Real.sqrt (2*Real.pi))⁻¹
  let B := fun x : ℝ ↦ c*(10*|x|+8*|z|)
  have hFmeas (r : ℝ) : Measurable (F r) := by
    dsimp [F,gaussianConditionalArg]
    exact standardGaussian_cdf_continuous.measurable.comp (by fun_prop)
  have hDmeas (r : ℝ) : Measurable (D r) := by
    dsimp [D,gaussianConditionalArg,gaussianConditionalArgDeriv,gaussianPDFReal]
    fun_prop
  have hFi : Integrable (F 0) ((gaussianReal 0 1).restrict (Iic z)) := by
    apply Integrable.of_bound (hFmeas 0).aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (cdf_nonneg _ _)]
    exact cdf_le_one _ _
  have hBi : Integrable B ((gaussianReal 0 1).restrict (Iic z)) := by
    have hi : Integrable (fun x : ℝ ↦ |x|) (gaussianReal 0 1) :=
      ((memLp_id_gaussianReal' 2 (by norm_num)).integrable (by norm_num)).abs
    exact ((hi.const_mul 10).add (integrable_const (8*|z|))).const_mul c |>.integrableOn
  have hbound : ∀ᵐ x ∂(gaussianReal 0 1).restrict (Iic z), ∀ r ∈ Ioo (-(1/2:ℝ)) (1/2), ‖D r x‖ ≤ B x := by
    filter_upwards with x r hr
    dsimp [D,B,c]
    rw [abs_mul]
    exact mul_le_mul (standardGaussian_pdf_bound _) (gaussianConditionalArgDeriv_bound r z x hr)
      (abs_nonneg _) (by positivity)
  have hdiff : ∀ᵐ x ∂(gaussianReal 0 1).restrict (Iic z), ∀ r ∈ Ioo (-(1/2:ℝ)) (1/2),
      HasDerivAt (fun r ↦ F r x) (D r x) r := by
    filter_upwards with x r hr
    exact (standardGaussian_cdf_hasDerivAt _).comp r
      (gaussianConditionalArg_hasDerivAt r z x ⟨by linarith [hr.1],by linarith [hr.2]⟩)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by norm_num : -(1/2:ℝ) < 0) (by norm_num : (0:ℝ) < 1/2))
    (Eventually.of_forall (fun r ↦ (hFmeas r).aestronglyMeasurable)) hFi
    (hDmeas 0).aestronglyMeasurable hbound hBi hdiff).2
  have hmean : (∫ x in Iic z, D 0 x ∂gaussianReal 0 1) = (gaussianPDFReal 0 1 z)^2 := by
    simp only [D,gaussianConditionalArg,gaussianConditionalArgDeriv,zero_mul,zero_pow (by norm_num : 2 ≠ 0),
      sub_zero,Real.sqrt_one,div_one,mul_zero,zero_div,add_zero]
    rw [integral_const_mul,standardGaussian_truncated_mean,pow_two]
  rw [hmean] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0) (by norm_num : (0:ℝ) < 1)] with r hr
  exact bivariateNormalCDF_conditional r z hr

lemma bivariateNormalCDF_zero (z : ℝ) : bivariateNormalCDF 0 z z = (cdf (gaussianReal 0 1) z)^2 := by
  rw [bivariateNormalCDF_conditional 0 z (by norm_num : (0:ℝ) ∈ Ioo (-1) 1)]
  simp only [gaussianConditionalArg,zero_mul,zero_pow (by norm_num : 2 ≠ 0),sub_zero,Real.sqrt_one,div_one]
  rw [setIntegral_const,← cdf_eq_real,smul_eq_mul,pow_two]

/-- The small-correlation approximation is the actual derivative at zero correlation. -/
theorem gaussian_indicator_correlation_hasDerivAt_zero (p : ℝ) (hp : p ∈ Ioo 0 1) :
    HasDerivAt (fun rho ↦ (gaussianCopulaDiagonal rho p-p^2)/(p*(1-p)))
      ((gaussianPDFReal 0 1 (standardNormalQuantile p))^2/(p*(1-p))) 0 := by
  exact ((bivariateNormalCDF_hasDerivAt_zero (standardNormalQuantile p)).sub_const (p^2)).div_const _

/-- Independence has zero indicator correlation. -/
theorem gaussian_indicator_correlation_zero (p : ℝ) (hp : p ∈ Ioo 0 1) :
    (gaussianCopulaDiagonal 0 p-p^2)/(p*(1-p)) = 0 := by
  rw [gaussianCopulaDiagonal,bivariateNormalCDF_zero,standardNormalQuantile_cdf p hp,sub_self,zero_div]


/-- Equivalent ratio limit for the paper's small-correlation approximation. -/
theorem gaussian_indicator_correlation_small_rho (p : ℝ) (hp : p ∈ Ioo 0 1) :
    Tendsto (fun rho ↦ ((gaussianCopulaDiagonal rho p-p^2)/(p*(1-p)))/rho)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ))
      (nhds ((gaussianPDFReal 0 1 (standardNormalQuantile p))^2/(p*(1-p)))) := by
  have hh := hasDerivAt_iff_tendsto_slope.mp (gaussian_indicator_correlation_hasDerivAt_zero p hp)
  simpa only [slope_fun_def_field,gaussian_indicator_correlation_zero p hp,sub_zero] using hh

end Exceedance
#print axioms Exceedance.bivariateNormalCDF_conditional

#print axioms Exceedance.gaussian_indicator_correlation_hasDerivAt_zero
#print axioms Exceedance.gaussian_indicator_correlation_zero

#print axioms Exceedance.gaussian_indicator_correlation_small_rho
