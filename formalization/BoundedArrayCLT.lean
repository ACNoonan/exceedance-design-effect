import IndicatorVariance
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

set_option backward.isDefEq.respectTransparency false

/-- Products of complex contractions differ by at most the sum of their factor errors. -/
lemma norm_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i-g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have hgprod : ‖∏ j ∈ s, g j‖ ≤ 1 :=
      (Finset.norm_prod_le s g).trans (Finset.prod_le_one (fun _ _ ↦ norm_nonneg _) (fun j _ ↦ hg j))
    calc
      _ = ‖f i*((∏ j ∈ s, f j)-(∏ j ∈ s, g j)) + (f i-g i)*(∏ j ∈ s, g j)‖ := by congr 1; ring
      _ ≤ ‖f i‖*‖(∏ j ∈ s, f j)-(∏ j ∈ s, g j)‖ + ‖f i-g i‖*‖∏ j ∈ s, g j‖ := by
        simpa only [norm_mul] using norm_add_le (f i*((∏ j ∈ s, f j)-(∏ j ∈ s, g j))) ((f i-g i)*(∏ j ∈ s, g j))
      _ ≤ 1*‖(∏ j ∈ s, f j)-(∏ j ∈ s, g j)‖ + ‖f i-g i‖*1 :=
        add_le_add (mul_le_mul_of_nonneg_right (hf i) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hgprod (norm_nonneg _))
      _ ≤ _ := by simp only [one_mul, mul_one]; linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A uniform bound supplies the cubic characteristic-function remainder. -/
theorem bounded_charFun_taylor (X : Ω → ℝ) (hX : Measurable X)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ ω ∂μ, |X ω| ≤ B)
    (hmean : (∫ ω, X ω ∂μ) = 0) (t : ℝ) :
    ‖charFun (μ.map X) t - (1 - (∫ ω, (X ω)^2 ∂μ : ℝ)*(t:ℂ)^2/2)‖ ≤
      (|t| *B)^3 * Real.exp (|t| *B) := by
  have hi : Integrable X μ := Integrable.of_bound hX.aestronglyMeasurable B (by simpa only [Real.norm_eq_abs] using hb)
  have hi2 : Integrable (fun ω ↦ (X ω)^2) μ := by
    apply Integrable.of_bound (hX.pow_const 2).aestronglyMeasurable (B^2)
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hω _
  have hi2c : Integrable (fun ω ↦ (X ω : ℂ)^2) μ := by
    convert (hi2.ofReal : Integrable (fun ω ↦ (((X ω)^2 : ℝ) : ℂ)) μ) using 1
    ext ω
    exact (Complex.ofReal_pow (X ω) 2).symm
  have hiC : Integrable (fun ω ↦ (X ω : ℂ)) μ := hi.ofReal
  have hc : Integrable (fun ω ↦ Complex.exp ((t:ℂ)*(X ω)*Complex.I)) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with ω
    simp [Complex.norm_exp]
  have hp : Integrable (fun ω ↦ (1:ℂ)+(t:ℂ)*(X ω)*Complex.I - (X ω : ℂ)^2*(t:ℂ)^2/2) μ := by
    exact ((integrable_const (1:ℂ)).fun_add ((hiC.const_mul (t:ℂ)).mul_const Complex.I)).sub
      ((hi2c.mul_const ((t:ℂ)^2)).div_const 2)
  have hipow : (∫ ω, (X ω : ℂ)^2 ∂μ) = ((∫ ω, (X ω)^2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall (fun ω ↦ (Complex.ofReal_pow (X ω) 2).symm))
  have he : (∫ ω, ((1:ℂ)+(t:ℂ)*(X ω)*Complex.I - (X ω : ℂ)^2*(t:ℂ)^2/2) ∂μ) =
      1 - (∫ ω, (X ω)^2 ∂μ : ℝ)*(t:ℂ)^2/2 := by
    rw [integral_sub ((integrable_const (1:ℂ)).fun_add ((hiC.const_mul (t:ℂ)).mul_const Complex.I))
      ((hi2c.mul_const ((t:ℂ)^2)).div_const 2), integral_add (integrable_const (1:ℂ)) ((hiC.const_mul (t:ℂ)).mul_const Complex.I)]
    simp only [integral_const, probReal_univ, one_smul, integral_div, integral_mul_const,
      integral_const_mul, integral_complex_ofReal, hmean, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
    rw [hipow]
  rw [charFun_apply_real, integral_map hX.aemeasurable (by fun_prop), ← he, ← integral_sub hc hp]
  apply le_trans (norm_integral_le_of_norm_le_const (C := (|t| *B)^3 * Real.exp (|t| *B)) ?_) (by simp)
  filter_upwards [hb] with ω hω
  have hz : ‖(t:ℂ)*(X ω)*Complex.I‖ ≤ |t| *B := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    exact mul_le_mul_of_nonneg_left hω (abs_nonneg _)
  have ht := Complex.norm_exp_sub_sum_le_norm_mul_exp ((t:ℂ)*(X ω)*Complex.I) 3
  have hpoly : (∑ j ∈ Finset.range 3, ((t:ℂ)*(X ω)*Complex.I)^j/(j.factorial:ℂ)) =
      1+(t:ℂ)*(X ω)*Complex.I-(X ω : ℂ)^2*(t:ℂ)^2/2 := by
    norm_num [Finset.sum_range_succ, pow_two, Complex.I_sq]
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [hpoly] at ht
  exact ht.trans (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz _)
    (Real.exp_le_exp.mpr hz) (Real.exp_pos _).le (by positivity))

lemma bounded_second_moment (X : Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ B) :
    0 ≤ (∫ ω, (X ω)^2 ∂μ) ∧ (∫ ω, (X ω)^2 ∂μ) ≤ B^2 := by
  constructor
  · exact integral_nonneg (fun _ ↦ sq_nonneg _)
  · have hh := integral_mono_of_nonneg (Eventually.of_forall (fun ω ↦ sq_nonneg (X ω)))
      (integrable_const (B^2)) (show (fun ω ↦ (X ω)^2) ≤ᵐ[μ] (fun _ ↦ B^2) from ?_)
    · simpa using hh
    · filter_upwards [hb] with ω hω
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hω _

/-- A bounded centered variable has a uniformly controlled Gaussian approximation in Fourier space. -/
theorem bounded_charFun_gaussian_error (X : Ω → ℝ) (hX : Measurable X)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ ω ∂μ, |X ω| ≤ B)
    (hmean : (∫ ω, X ω ∂μ) = 0) (t : ℝ) :
    ‖charFun (μ.map X) t - Complex.exp (-((∫ ω, (X ω)^2 ∂μ : ℝ)*(t:ℂ)^2/2))‖ ≤
      (|t| *B)^3 * Real.exp (|t| *B) + (B^2*t^2/2)^2 * Real.exp (B^2*t^2/2) := by
  let v : ℝ := ∫ ω, (X ω)^2 ∂μ
  have hv := bounded_second_moment X B hB hb
  have hz : ‖-((v:ℂ)*(t:ℂ)^2/2)‖ = v*t^2/2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_ofNat,
      ← Complex.ofReal_div, ← Complex.ofReal_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_neg, abs_of_nonneg (by dsimp [v]; positivity)]
  have hle : v*t^2/2 ≤ B^2*t^2/2 := by dsimp [v]; gcongr; exact hv.2
  have he := Complex.norm_exp_sub_sum_le_norm_mul_exp (-((v:ℂ)*(t:ℂ)^2/2)) 2
  have hp : (∑ j ∈ Finset.range 2, (-((v:ℂ)*(t:ℂ)^2/2))^j/(j.factorial:ℂ)) =
      1-(v:ℂ)*(t:ℂ)^2/2 := by simp [Finset.sum_range_succ]; ring
  rw [hp, hz] at he
  have he' : ‖(1-(v:ℂ)*(t:ℂ)^2/2)-Complex.exp (-((v:ℂ)*(t:ℂ)^2/2))‖ ≤
      (B^2*t^2/2)^2 * Real.exp (B^2*t^2/2) := by
    rw [norm_sub_rev]
    apply he.trans
    exact mul_le_mul (pow_le_pow_left₀ (by dsimp [v]; positivity) hle _)
      (Real.exp_le_exp.mpr hle) (Real.exp_pos _).le (by positivity)
  exact (norm_sub_le_norm_sub_add_norm_sub _ (1-(v:ℂ)*(t:ℂ)^2/2) _).trans
    (add_le_add (bounded_charFun_taylor X hX B hB hb hmean t) he')

/-- CLT for centered independent arrays with a vanishing bound and cubic row error.
The rows need not share a distribution, or be independent of one another. -/
theorem bounded_array_clt
    (b : ℕ → ℕ) (X : (n : ℕ) → Fin (b n) → Ω → ℝ)
    (hX : ∀ n j, Measurable (X n j)) (hindep : ∀ n, iIndepFun (X n) μ)
    (hmean : ∀ n j, (∫ ω, X n j ω ∂μ) = 0)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hbound : ∀ n j, ∀ᵐ ω ∂μ, |X n j ω| ≤ B n)
    (hB0 : Tendsto B atTop (nhds 0))
    (hthird : Tendsto (fun n ↦ (b n : ℝ)*(B n)^3) atTop (nhds 0))
    (v : NNReal)
    (hvar : Tendsto (fun n ↦ ∑ j, ∫ ω, (X n j ω)^2 ∂μ) atTop (nhds (v:ℝ))) :
    TendstoInDistribution (fun n ω ↦ ∑ j, X n j ω) atTop (id : ℝ → ℝ)
      (fun _ ↦ μ) (gaussianReal 0 v) where
  forall_aemeasurable n := (Finset.measurable_sum _ (fun j _ ↦ hX n j)).aemeasurable
  tendsto := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
    intro t
    let V := fun n ↦ ∑ j, ∫ ω, (X n j ω)^2 ∂μ
    let G := fun n ↦ Complex.exp (-((V n : ℂ)*(t:ℂ)^2/2))
    have hg : Tendsto G atTop (nhds (charFun (gaussianReal 0 v) t)) := by
      have hh := Complex.continuous_exp.continuousAt.tendsto.comp
        (((Complex.continuous_ofReal.tendsto _).comp hvar).mul_const ((t:ℂ)^2) |>.div_const 2 |>.neg)
      simpa [G, V, charFun_gaussianReal, Function.comp_def] using hh
    have hr : Tendsto (fun n ↦ (b n : ℝ)*((|t| *B n)^3*Real.exp (|t| *B n) +
        ((B n)^2*t^2/2)^2*Real.exp ((B n)^2*t^2/2))) atTop (nhds 0) := by
      have hc : Continuous (fun x : ℝ ↦ |t|^3*Real.exp (|t| *x) + x*t^4/4*Real.exp (x^2*t^2/2)) := by fun_prop
      have hh := hthird.mul ((hc.tendsto 0).comp hB0)
      simp only [zero_mul, Function.comp_def] at hh
      convert hh using 1 <;> ext n <;> ring
    have herr : Tendsto (fun n ↦ charFun (μ.map (fun ω ↦ ∑ j, X n j ω)) t-G n) atTop (nhds 0) := by
      apply squeeze_zero_norm (fun n ↦ ?_) hr
      have he : G n = ∏ j : Fin (b n), Complex.exp (-((∫ ω, (X n j ω)^2 ∂μ : ℝ)*(t:ℂ)^2/2)) := by
        rw [← Complex.exp_sum]
        congr 1
        simp only [G, V, Complex.ofReal_sum, Finset.sum_neg_distrib, Finset.sum_div, Finset.sum_mul]
      rw [he, (hindep n).charFun_map_fun_sum_eq_prod (fun j ↦ (hX n j).aemeasurable), Finset.prod_apply]
      apply (norm_prod_sub_prod_le_sum Finset.univ _ _ (fun j ↦ ?_) (fun j ↦ ?_)).trans
      · calc
          _ ≤ ∑ _j : Fin (b n), ((|t| *B n)^3*Real.exp (|t| *B n) +
              ((B n)^2*t^2/2)^2*Real.exp ((B n)^2*t^2/2)) :=
            Finset.sum_le_sum (fun j _ ↦ bounded_charFun_gaussian_error (X n j) (hX n j)
              (B n) (hB n) (hbound n j) (hmean n j) t)
          _ = _ := by simp; ring
      · haveI : IsProbabilityMeasure (μ.map (X n j)) := Measure.isProbabilityMeasure_map (hX n j).aemeasurable
        exact norm_charFun_le_one t
      · rw [Complex.norm_exp]
        have hv := (bounded_second_moment (X n j) (B n) (hB n) (hbound n j)).1
        apply Real.exp_le_one_iff.mpr
        have hearg : -((∫ ω, (X n j ω)^2 ∂μ : ℝ)*(t:ℂ)^2/2) =
            ((-((∫ ω, (X n j ω)^2 ∂μ)*t^2/2) : ℝ) : ℂ) := by push_cast; rfl
        rw [hearg, Complex.ofReal_re]
        exact neg_nonpos.mpr (by positivity)
    have hh := herr.add hg
    simpa only [sub_add_cancel, zero_add, ProbabilityMeasure.coe_mk, Measure.map_id] using hh

/-- The bounded-array CLT on the total-observation scale. -/
theorem bounded_array_sqrt_clt
    (b : ℕ → ℕ) (A : (n : ℕ) → Fin (b n) → Ω → ℝ)
    (hA : ∀ n j, Measurable (A n j)) (hindep : ∀ n, iIndepFun (A n) μ)
    (hmean : ∀ n j, (∫ ω, A n j ω ∂μ) = 0)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ n j, ∀ᵐ ω ∂μ, |A n j ω| ≤ M)
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n) (hbN : ∀ n, (b n : ℝ) ≤ N n)
    (hNt : Tendsto N atTop atTop) (v : NNReal)
    (hvar : Tendsto (fun n ↦ (∑ j, Var[A n j; μ])/N n) atTop (nhds (v:ℝ))) :
    TendstoInDistribution (fun n ω ↦ (∑ j, A n j ω)/Real.sqrt (N n)) atTop
      (id : ℝ → ℝ) (fun _ ↦ μ) (gaussianReal 0 v) := by
  let B := fun n ↦ M/Real.sqrt (N n)
  have hs (n : ℕ) : 0 < Real.sqrt (N n) := Real.sqrt_pos.mpr (hN n)
  have hi : Tendsto (fun n ↦ (Real.sqrt (N n))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hNt)
  have hB0 : Tendsto B atTop (nhds 0) := by simpa [B, div_eq_mul_inv] using hi.const_mul M
  have hthird : Tendsto (fun n ↦ (b n : ℝ)*(B n)^3) atTop (nhds 0) := by
    have ht : Tendsto (fun n ↦ M^3/Real.sqrt (N n)) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using hi.const_mul (M^3)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    · intro n; dsimp [B]; positivity
    · intro n
      calc
        _ ≤ N n*(M/Real.sqrt (N n))^3 := mul_le_mul_of_nonneg_right (hbN n) (by positivity)
        _ = M^3/Real.sqrt (N n) := by
          rw [div_pow, show (Real.sqrt (N n))^3 = N n*Real.sqrt (N n) by rw [pow_succ, Real.sq_sqrt (hN n).le]]
          field_simp [ne_of_gt (hN n), ne_of_gt (hs n)]
  have hv : Tendsto (fun n ↦ ∑ j, ∫ ω, (A n j ω/Real.sqrt (N n))^2 ∂μ) atTop (nhds (v:ℝ)) := by
    convert hvar using 1
    ext n
    simp only [div_pow, Real.sq_sqrt (hN n).le, integral_div, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [variance_eq_integral (hA n j).aemeasurable, hmean n j]
    simp
  have hh := bounded_array_clt b (fun n j ω ↦ A n j ω/Real.sqrt (N n))
    (fun n j ↦ (hA n j).div_const _)
    (fun n ↦ (hindep n).comp (fun _ x ↦ x/Real.sqrt (N n)) (fun _ ↦ measurable_id.div_const _))
    (fun n j ↦ by rw [integral_div, hmean n j, zero_div])
    B (fun n ↦ by dsimp [B]; positivity)
    (fun n j ↦ by
      filter_upwards [hbound n j] with ω hω
      rw [abs_div, abs_of_pos (hs n)]
      exact div_le_div_of_nonneg_right hω (hs n).le)
    hB0 hthird v hv
  simpa only [← Finset.sum_div] using hh

end Exceedance
#print axioms Exceedance.bounded_charFun_taylor

#print axioms Exceedance.bounded_charFun_gaussian_error

#print axioms Exceedance.bounded_array_clt

#print axioms Exceedance.bounded_array_sqrt_clt
