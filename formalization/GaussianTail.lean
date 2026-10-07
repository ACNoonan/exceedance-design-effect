import IndicatorVariance
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

lemma gaussianReal_subgaussian {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (v : NNReal) (hX : μ.map X = gaussianReal 0 v) :
    HasSubgaussianMGF X v μ where
  integrable_exp_mul t := by
    rw [← mgf_pos_iff, mgf_gaussianReal hX]
    exact Real.exp_pos _
  mgf_le t := by simp [mgf_gaussianReal hX]

/-- A positive lower bound for a standard-normal tail, from an interval of length one. -/
lemma standard_gaussian_tail_lower (t : ℝ) (ht : 0 ≤ t) :
    gaussianPDFReal 0 1 (t+1) ≤ (gaussianReal 0 1).real (Ioi t) := by
  have hi := (integrable_gaussianPDFReal 0 1).integrableOn (s := Ioc t (t+1))
  have hb : ∀ x ∈ Ioc t (t+1), gaussianPDFReal 0 1 (t+1) ≤ gaussianPDFReal 0 1 x := by
    intro x hx
    unfold gaussianPDFReal
    simp only [NNReal.coe_one, mul_one, sub_zero]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [hx.1,hx.2]
  have hmono := setIntegral_mono_on (integrableOn_const (by simp) (by simp)) hi measurableSet_Ioc hb
  have he : (gaussianReal 0 1).real (Ioc t (t+1)) = ∫ x in Ioc t (t+1), gaussianPDFReal 0 1 x := by
    rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num),
      ENNReal.toReal_ofReal (integral_nonneg (fun x ↦ gaussianPDFReal_nonneg _ _ _))]
  have hc : (∫ _x in Ioc t (t+1), gaussianPDFReal 0 1 (t+1)) = gaussianPDFReal 0 1 (t+1) := by
    simp
  rw [hc, ← he] at hmono
  exact hmono.trans (measureReal_mono Ioc_subset_Ioi_self)

/-- Joint Gaussian upper tails are asymptotically independent when the sum variance is less than four.
A standard bivariate normal pair with correlation rho has sum variance 2(1+rho). -/
theorem gaussian_pair_upper_tail_ratio {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hx : μ.map X = gaussianReal 0 1)
    (v : NNReal) (hv0 : 0 < v) (hv4 : (v:ℝ) < 4)
    (hsum : μ.map (fun ω ↦ X ω+Y ω) = gaussianReal 0 v) :
    Tendsto (fun t ↦ μ.real {ω | t < X ω ∧ t < Y ω}/μ.real {ω | t < X ω}) atTop (nhds 0) := by
  let c : ℝ := Real.sqrt (2*Real.pi)
  let d : ℝ := 2/(v:ℝ)-1/2
  have hv : 0 < (v:ℝ) := hv0
  have hd : 0 < d := by dsimp [d]; apply sub_pos.mpr; apply (lt_div_iff₀ hv).mpr; linarith
  have hcp : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hlim : Tendsto (fun t : ℝ ↦ c*Real.exp (-t+1/2)) atTop (nhds 0) := by
    have hh := Real.tendsto_exp_atBot.comp (tendsto_atBot_add_const_right _ (1/2) tendsto_neg_atTop_atBot)
    simpa only [mul_zero, Function.comp_apply] using hh.const_mul c
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Eventually.of_forall (fun t ↦ div_nonneg measureReal_nonneg measureReal_nonneg)
  · filter_upwards [eventually_ge_atTop (max 0 (2/d))] with t ht
    have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
    have hdt : 2 ≤ d*t := by have hh := (le_max_right 0 (2/d)).trans ht; exact (div_le_iff₀ hd).mp hh |>.trans_eq (mul_comm _ _)
    have hl := standard_gaussian_tail_lower t ht0
    have hm : μ.real {ω | t < X ω} = (gaussianReal 0 1).real (Ioi t) := by
      rw [← hx, map_measureReal_apply hX measurableSet_Ioi]; rfl
    rw [← hm] at hl
    have hpdf := gaussianPDFReal_pos 0 1 (t+1) (by norm_num)
    have hu : μ.real {ω | t < X ω ∧ t < Y ω} ≤ Real.exp (-(2*t)^2/(2*(v:ℝ))) := by
      apply (measureReal_mono (μ := μ) (show {ω | t < X ω ∧ t < Y ω} ⊆ {ω | 2*t ≤ X ω+Y ω} from
        fun ω h ↦ by dsimp only [mem_setOf_eq] at *; linarith)).trans
      exact (gaussianReal_subgaussian _ v hsum).measure_ge_le (by positivity)
    calc
      _ ≤ Real.exp (-(2*t)^2/(2*(v:ℝ)))/gaussianPDFReal 0 1 (t+1) :=
        div_le_div₀ (Real.exp_pos _).le hu hpdf hl
      _ = c*Real.exp (-(2*t)^2/(2*(v:ℝ))+(t+1)^2/2) := by
        unfold gaussianPDFReal
        simp only [NNReal.coe_one, mul_one, sub_zero]
        rw [show -(t+1)^2/2 = -((t+1)^2/2) by ring, Real.exp_neg, Real.exp_add]
        dsimp [c]
        field_simp

      _ ≤ c*Real.exp (-t+1/2) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hcp.le
        have hh : 2*t ≤ d*t^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hdt) ht0]
        dsimp [d] at hh
        have he : -(2*t)^2/(2*(v:ℝ))+(t+1)^2/2 = -(2/(v:ℝ)-1/2)*t^2+t+1/2 := by ring
        rw [he]
        linarith


/-- The matching lower-tail ratio follows by Gaussian reflection. -/
theorem gaussian_pair_lower_tail_ratio {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hx : μ.map X = gaussianReal 0 1)
    (v : NNReal) (hv0 : 0 < v) (hv4 : (v:ℝ) < 4)
    (hsum : μ.map (fun ω ↦ X ω+Y ω) = gaussianReal 0 v) :
    Tendsto (fun t ↦ μ.real {ω | X ω < t ∧ Y ω < t}/μ.real {ω | X ω < t}) atBot (nhds 0) := by
  have hnx : μ.map (fun ω ↦ -X ω) = gaussianReal 0 1 := by
    have hh := (gaussianReal_neg (show HasLaw X (gaussianReal 0 1) μ from ⟨hX.aemeasurable,hx⟩)).map_eq
    rw [show -X = (fun ω ↦ -X ω) from rfl, neg_zero] at hh
    exact hh
  have hns : μ.map (fun ω ↦ -X ω + -Y ω) = gaussianReal 0 v := by
    have hh := (gaussianReal_neg (show HasLaw (fun ω ↦ X ω+Y ω) (gaussianReal 0 v) μ from
      ⟨(hX.add hY).aemeasurable,hsum⟩)).map_eq
    rw [show -(fun ω ↦ X ω+Y ω) = (fun ω ↦ -X ω + -Y ω) by funext ω; simp only [Pi.neg_apply]; ring, neg_zero] at hh
    exact hh
  have hh := (gaussian_pair_upper_tail_ratio (fun ω ↦ -X ω) (fun ω ↦ -Y ω)
    hX.neg hY.neg hnx v hv0 hv4 hns).comp tendsto_neg_atBot_atTop
  convert hh using 1
  funext t
  simp only [Function.comp_apply, neg_lt_neg_iff]

end Exceedance
#print axioms Exceedance.gaussian_pair_upper_tail_ratio

#print axioms Exceedance.gaussian_pair_lower_tail_ratio
