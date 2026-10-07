import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

lemma betaPDFReal_nonneg (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    0 ≤ betaPDFReal a b x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact (betaPDFReal_pos hx.1 hx.2 ha hb).le
  · simp [betaPDFReal, hx]

lemma integral_betaPDFReal (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x, betaPDFReal a b x) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (betaPDFReal_nonneg a b ha hb))
    (measurable_betaPDFReal a b).aestronglyMeasurable]
  change (∫⁻ x, betaPDF a b x).toReal = 1
  rw [lintegral_betaPDF_eq_one ha hb, ENNReal.toReal_one]

lemma beta_add_one_left (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    beta (a+1) b = a/(a+b)*beta a b := by
  unfold beta
  rw [Real.Gamma_add_one ha.ne', show a+1+b = (a+b)+1 by ring,
    Real.Gamma_add_one (ne_of_gt (add_pos ha hb))]
  field_simp

lemma betaPDFReal_mul_id (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    betaPDFReal a b x*x = (a/(a+b))*betaPDFReal (a+1) b x := by
  by_cases hx : 0 < x ∧ x < 1
  · simp only [betaPDFReal, if_pos hx]
    rw [show a+1-1 = (a-1)+1 by ring, Real.rpow_add hx.1, Real.rpow_one,
      beta_add_one_left a b ha hb]
    have hB := (beta_pos ha hb).ne'
    have hab := (add_pos ha hb).ne'
    field_simp
  · simp [betaPDFReal, hx]

lemma integral_beta_eq_density (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (f : ℝ → ℝ) :
    (∫ x, f x ∂betaMeasure a b) = ∫ x, betaPDFReal a b x*f x := by
  change (∫ x, f x ∂volume.withDensity (fun x ↦ ENNReal.ofReal (betaPDFReal a b x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_betaPDFReal a b).ennreal_ofReal)
    (Eventually.of_forall (fun x ↦ ENNReal.ofReal_lt_top))]
  simp only [betaPDF, ENNReal.toReal_ofReal (betaPDFReal_nonneg a b ha hb _), smul_eq_mul]

/-- The Beta law's mean, for all positive real shape parameters. -/
theorem beta_mean (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x, x ∂betaMeasure a b) = a/(a+b) := by
  rw [integral_beta_eq_density a b ha hb]
  simp_rw [betaPDFReal_mul_id a b ha hb]
  rw [integral_const_mul, integral_betaPDFReal (a+1) b (by linarith) hb, mul_one]

/-- The Beta law's second moment. -/
theorem beta_second_moment (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x, x^2 ∂betaMeasure a b) = a*(a+1)/((a+b)*(a+b+1)) := by
  rw [integral_beta_eq_density a b ha hb]
  have he (x : ℝ) : betaPDFReal a b x*x^2 =
      (a/(a+b))*((a+1)/(a+1+b))*betaPDFReal (a+1+1) b x := by
    calc
      _ = (betaPDFReal a b x*x)*x := by ring
      _ = (a/(a+b))*(betaPDFReal (a+1) b x*x) := by rw [betaPDFReal_mul_id a b ha hb]; ring
      _ = _ := by rw [betaPDFReal_mul_id (a+1) b (by linarith) hb]; ring
  simp_rw [he]
  rw [integral_const_mul, integral_betaPDFReal (a+1+1) b (by linarith) hb, mul_one]
  rw [show a+1+b = a+b+1 by ring]
  field_simp

/-- The Beta law's variance, for positive real shape parameters. -/
theorem beta_variance (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Var[fun x : ℝ ↦ x; betaMeasure a b] = a*b/((a+b)^2*(a+b+1)) := by
  letI := isProbabilityMeasureBeta ha hb
  have hLp : MemLp (fun x : ℝ ↦ x) 2 (betaMeasure a b) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (.of_integral_ne_zero (by
      rw [beta_second_moment a b ha hb]
      positivity))
  rw [variance_eq_sub hLp]
  change (∫ x, x^2 ∂betaMeasure a b) - (∫ x, x ∂betaMeasure a b)^2 = _
  rw [beta_second_moment a b ha hb, beta_mean a b ha hb]
  have hab : a+b ≠ 0 := by positivity
  have hab1 : a+b+1 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- The manuscript's Beta approximation has exactly the displayed moments. -/
theorem beta_approximation_moments (p neff : ℝ) (hp : p ∈ Ioo 0 1) (hn : 1 < neff) :
    (∫ x, x ∂betaMeasure (p*(neff-1)) ((1-p)*(neff-1))) = p ∧
    Var[fun x : ℝ ↦ x; betaMeasure (p*(neff-1)) ((1-p)*(neff-1))] = p*(1-p)/neff := by
  have ha : 0 < p*(neff-1) := mul_pos hp.1 (sub_pos.mpr hn)
  have hb : 0 < (1-p)*(neff-1) := mul_pos (sub_pos.mpr hp.2) (sub_pos.mpr hn)
  have he : p*(neff-1)+(1-p)*(neff-1) = neff-1 := by ring
  rw [beta_mean _ _ ha hb, beta_variance _ _ ha hb, he]
  have hne : neff-1 ≠ 0 := by linarith
  have hn0 : neff ≠ 0 := by linarith
  rw [sub_add_cancel]
  constructor <;> field_simp <;> ring

end Exceedance
#print axioms Exceedance.beta_mean
#print axioms Exceedance.beta_second_moment

#print axioms Exceedance.beta_variance
#print axioms Exceedance.beta_approximation_moments
