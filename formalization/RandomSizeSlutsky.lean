import LimitInversion
import Mathlib.Topology.Order.LeftRightLim

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

/-- A CDF is continuous at every point that carries no mass. -/
theorem cdf_continuousAt_of_no_atom (ν : Measure ℝ) [IsProbabilityMeasure ν] (y : ℝ)
    (hy : ν {y} = 0) : ContinuousAt (cdf ν) y := by
  have hmono := monotone_cdf ν
  have hleft : Function.leftLim (cdf ν) y = cdf ν y := by
    have h := (cdf ν).measure_singleton y
    rw [measure_cdf, hy] at h
    have h2 := ENNReal.ofReal_eq_zero.mp h.symm
    have h3 := hmono.leftLim_le (le_refl y)
    linarith
  rw [continuousAt_iff_continuous_left'_right']
  exact ⟨hmono.continuousWithinAt_Iio_iff_leftLim_eq.mpr hleft,
    ((cdf ν).right_continuous y).mono Ioi_subset_Ici_self⟩

/-- The centered Gaussian CDF is continuous away from the zero-variance jump. -/
theorem centered_gaussian_cdf_continuousAt (v : NNReal) (y : ℝ) (hy : v ≠ 0 ∨ y ≠ 0) :
    ContinuousAt (cdf (gaussianReal 0 v)) y := by
  apply cdf_continuousAt_of_no_atom
  have hh := centered_gaussian_no_atom_at_continuity (μ := gaussianReal 0 v) id v HasLaw.id (-y)
    (hy.imp_right neg_ne_zero.mpr)
  simpa only [id_eq, neg_neg, setOf_eq_eq_singleton] using hh

/-- Rescaling a centered Gaussian CDF. -/
theorem centered_gaussian_cdf_scale (v w : NNReal) (a : ℝ) (ha : 0 < a)
    (hw : (w:ℝ) = a^2 * v) (x : ℝ) :
    cdf (gaussianReal 0 v) (x/a) = cdf (gaussianReal 0 w) x := by
  have hwe : w = .mk (a^2) (sq_nonneg _) * v := by
    apply NNReal.eq
    rw [hw]
    rfl
  have hm := gaussianReal_map_const_mul (μ := 0) (v := v) a
  rw [mul_zero, ← hwe] at hm
  rw [cdf_eq_real, cdf_eq_real, ← hm, map_measureReal_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext z
  simp only [mem_Iic, mem_preimage]
  rw [le_div_iff₀ ha, mul_comm]

/-- Slutsky's lemma at the level of distribution functions, for `W = A T - r` with
    `A → a > 0` in probability and a vanishing nonnegative shift `r`.
    No measurability is needed because the comparison uses set inclusions only. -/
theorem cdf_limit_scaled_shifted {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T A r W : ℕ → Ω → ℝ) (Φ : ℝ → ℝ) (a : ℝ) (ha : 0 < a) (x : ℝ)
    (hΦ : ContinuousAt Φ (x/a))
    (hT : ∀ᶠ y in nhds (x/a), Tendsto (fun b ↦ μ.real {ω | T b ω ≤ y}) atTop (nhds (Φ y)))
    (hA : ∀ δ, 0 < δ → Tendsto (fun b ↦ μ.real {ω | δ < |A b ω - a|}) atTop (nhds 0))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0))
    (hr : ∀ᶠ b in atTop, ∀ ω, 0 ≤ r b ω ∧ r b ω ≤ ε b)
    (hW : ∀ᶠ b in atTop, ∀ ω, W b ω = A b ω * T b ω - r b ω) :
    Tendsto (fun b ↦ μ.real {ω | W b ω ≤ x}) atTop (nhds (Φ (x/a))) := by
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨η1, hη1, hc⟩ := Metric.continuousAt_iff.mp hΦ (e/3) (by positivity)
  obtain ⟨η2, hη2, ht⟩ := Metric.eventually_nhds_iff.mp hT
  let η := min η1 η2
  have hη : 0 < η := lt_min hη1 hη2
  let y1 := x/a - η/2
  let y2 := x/a + η/2
  have hy1 : dist y1 (x/a) < η := by
    rw [Real.dist_eq]; dsimp [y1]
    rw [show x/a - η/2 - x/a = -(η/2) by ring, abs_neg, abs_of_pos (by positivity)]
    linarith
  have hy2 : dist y2 (x/a) < η := by
    rw [Real.dist_eq]; dsimp [y2]
    rw [show x/a + η/2 - x/a = η/2 by ring, abs_of_pos (by positivity)]
    linarith
  have hΦ1 := hc (lt_of_lt_of_le hy1 (min_le_left _ _))
  have hΦ2 := hc (lt_of_lt_of_le hy2 (min_le_left _ _))
  have hT1 := ht (lt_of_lt_of_le hy1 (min_le_right _ _))
  have hT2 := ht (lt_of_lt_of_le hy2 (min_le_right _ _))
  rw [Real.dist_eq] at hΦ1 hΦ2
  have hx1 : (0:ℝ) < |x|+1 := by positivity
  let δ := min (a/2) (η*a^2/(8*(|x|+1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδa : δ ≤ a/2 := min_le_left _ _
  have hδx : |x| * δ ≤ η*a^2/8 := by
    have h1 : δ ≤ η*a^2/(8*(|x|+1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg x]
  have hεb : ∀ᶠ b in atTop, ε b < η*a/8 := hε.eventually (Iio_mem_nhds (by positivity))
  have hE := (hA δ hδ).eventually (Iio_mem_nhds (show (0:ℝ) < e/3 by positivity))
  have hP1 := (Metric.tendsto_atTop.mp hT1 (e/3) (by positivity))
  have hP2 := (Metric.tendsto_atTop.mp hT2 (e/3) (by positivity))
  obtain ⟨N1, hN1⟩ := hP1
  obtain ⟨N2, hN2⟩ := hP2
  filter_upwards [hεb, hE, hr, hW, eventually_ge_atTop N1, eventually_ge_atTop N2]
    with b hεb hE hr hW hb1 hb2
  have hQ1 := hN1 b hb1
  have hQ2 := hN2 b hb2
  rw [Real.dist_eq] at hQ1 hQ2
  have hkey : ∀ ω, |A b ω - a| ≤ δ →
      0 < A b ω ∧ |(x + r b ω)/A b ω - x/a| ≤ η/2 := by
    intro ω hω
    have hab := abs_le.mp hω
    have hA2 : a/2 ≤ A b ω := by linarith
    have hApos : 0 < A b ω := by linarith
    refine ⟨hApos, ?_⟩
    have hrr := hr ω
    have he : (x + r b ω)/A b ω - x/a = (a * r b ω + x*(a - A b ω))/(A b ω * a) := by
      field_simp
      ring
    rw [he, abs_div, abs_of_pos (mul_pos hApos ha), div_le_iff₀ (mul_pos hApos ha)]
    have hn1 : |a * r b ω + x*(a - A b ω)| ≤ a * r b ω + |x| * δ := by
      apply (abs_add_le _ _).trans
      rw [abs_of_nonneg (mul_nonneg ha.le hrr.1), abs_mul]
      have : |a - A b ω| ≤ δ := by rw [abs_sub_comm]; exact hω
      nlinarith [abs_nonneg x]
    have hn2 : a * r b ω ≤ η*a^2/8 := by nlinarith [hrr.2]
    have hd : η*a^2/4 ≤ η/2 * (A b ω * a) := by nlinarith [mul_le_mul_of_nonneg_right hA2 ha.le]
    linarith
  have hsub1 : {ω | T b ω ≤ y1} ⊆ {ω | W b ω ≤ x} ∪ {ω | δ < |A b ω - a|} := by
    intro ω hω
    by_cases hd : δ < |A b ω - a|
    · exact Or.inr hd
    · left
      obtain ⟨hApos, hq⟩ := hkey ω (not_lt.mp hd)
      have hq' := (abs_le.mp hq).1
      have hle : T b ω ≤ (x + r b ω)/A b ω := by
        have : T b ω ≤ x/a - η/2 := hω
        linarith
      rw [le_div_iff₀ hApos] at hle
      change W b ω ≤ x
      rw [hW ω]
      linarith
  have hsub2 : {ω | W b ω ≤ x} ⊆ {ω | T b ω ≤ y2} ∪ {ω | δ < |A b ω - a|} := by
    intro ω hω
    by_cases hd : δ < |A b ω - a|
    · exact Or.inr hd
    · left
      obtain ⟨hApos, hq⟩ := hkey ω (not_lt.mp hd)
      have hq' := (abs_le.mp hq).2
      have hw : W b ω ≤ x := hω
      rw [hW ω] at hw
      have hle : T b ω ≤ (x + r b ω)/A b ω := by
        rw [le_div_iff₀ hApos]
        linarith
      change T b ω ≤ x/a + η/2
      linarith
  have hm1 := (measureReal_mono (μ := μ) hsub1).trans (measureReal_union_le _ _)
  have hm2 := (measureReal_mono (μ := μ) hsub2).trans (measureReal_union_le _ _)
  have hE' : μ.real {ω | δ < |A b ω - a|} < e/3 := hE
  rw [Real.dist_eq, abs_lt]
  have a1 := abs_lt.mp hΦ1
  have a2 := abs_lt.mp hΦ2
  have a3 := abs_lt.mp hQ1
  have a4 := abs_lt.mp hQ2
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]

end Exceedance

#print axioms Exceedance.cdf_continuousAt_of_no_atom
#print axioms Exceedance.centered_gaussian_cdf_scale
#print axioms Exceedance.cdf_limit_scaled_shifted
