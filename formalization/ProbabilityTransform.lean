import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.CDF
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

/-- A continuous CDF reaches every interior probability, including when it has flat regions. -/
theorem continuous_cdf_hits_interior (F : ℝ → ℝ) (hF : Continuous F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : ∃ x, F x = t := by
  exact intermediate_value_univ₂_eventually₂ hF continuous_const
    (h0.eventually_le_const ht0) (h1.eventually_const_le ht1)

/-- Probability-integral transform at interior levels.
    The hypotheses specify the actual marginal CDF, not a fitted estimate.
    Strict monotonicity and positive density are not required. -/
theorem continuous_cdf_transform_interior {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ x, μ.real {ω | X ω ≤ x} = F x)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    μ.real {ω | F (X ω) ≤ t} = t := by
  let r := μ.real {ω | F (X ω) ≤ t}
  have hr0 : 0 ≤ r := measureReal_nonneg
  have hr1 : r ≤ 1 := measureReal_le_one
  apply le_antisymm
  · by_contra hle
    have htr : t < r := lt_of_not_ge hle
    let u := (t+r)/2
    have hu0 : 0 < u := by dsimp [u]; linarith
    have hu1 : u < 1 := by dsimp [u]; linarith
    obtain ⟨x, hx⟩ := continuous_cdf_hits_interior F hF h0 h1 u hu0 hu1
    have hsub : {ω | F (X ω) ≤ t} ⊆ {ω | X ω ≤ x} := by
      intro ω hω
      by_contra hn
      have hh := hmono (le_of_lt (lt_of_not_ge hn))
      dsimp only [mem_setOf_eq] at hω ⊢
      rw [hx] at hh
      dsimp [u] at hh
      linarith
    have hh := measureReal_mono (μ := μ) hsub
    rw [hCDF, hx] at hh
    change r ≤ u at hh
    dsimp [u] at hh
    linarith
  · by_contra hle
    have hrt : r < t := lt_of_not_ge hle
    let u := (t+r)/2
    have hu0 : 0 < u := by dsimp [u]; linarith
    have hu1 : u < 1 := by dsimp [u]; linarith
    obtain ⟨x, hx⟩ := continuous_cdf_hits_interior F hF h0 h1 u hu0 hu1
    have hsub : {ω | X ω ≤ x} ⊆ {ω | F (X ω) ≤ t} := by
      intro ω hω
      have hh := hmono hω
      rw [hx] at hh
      dsimp only [mem_setOf_eq]
      dsimp [u] at hh
      linarith
    have hh := measureReal_mono (μ := μ) hsub
    rw [hCDF, hx] at hh
    change u ≤ r at hh
    dsimp [u] at hh
    linarith


/-- The transform has the uniform CDF throughout the closed unit interval. -/
theorem continuous_cdf_transform {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ x, μ.real {ω | X ω ≤ x} = F x)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    μ.real {ω | F (X ω) ≤ t} = t := by
  by_cases ht : t = 0
  · subst t
    apply le_antisymm _ measureReal_nonneg
    by_contra hn
    let r := μ.real {ω | F (X ω) ≤ 0}
    have hr0 : 0 < r := lt_of_not_ge hn
    have hr1 : r ≤ 1 := measureReal_le_one
    have hu := continuous_cdf_transform_interior X F hF hmono h0 h1 hCDF
      (r/2) (by positivity) (by linarith)
    have hs : {ω | F (X ω) ≤ 0} ⊆ {ω | F (X ω) ≤ r/2} := by
      intro ω hω
      change F (X ω) ≤ 0 at hω
      change F (X ω) ≤ r/2
      linarith
    have hh := measureReal_mono (μ := μ) hs
    rw [hu] at hh
    change r ≤ r/2 at hh
    linarith
  · by_cases ht' : t = 1
    · subst t
      have hf1 (x : ℝ) : F x ≤ 1 := by rw [← hCDF]; exact measureReal_le_one
      have he : {ω | F (X ω) ≤ 1} = univ := by ext ω; simp [hf1]
      rw [he]
      simp
    · exact continuous_cdf_transform_interior X F hF hmono h0 h1 hCDF t
        (lt_of_le_of_ne ht0 (Ne.symm ht)) (lt_of_le_of_ne ht1 ht')


/-- Exact interval probabilities for the transformed sample.
    This supplies the rare-event probability used in the local-increment bound. -/
theorem continuous_cdf_transform_interval {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (F : ℝ → ℝ)
    (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ x, μ.real {ω | X ω ≤ x} = F x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    μ.real {ω | a < F (X ω) ∧ F (X ω) ≤ b} = b-a := by
  have he : {ω | a < F (X ω) ∧ F (X ω) ≤ b} =
      {ω | F (X ω) ≤ b} \ {ω | F (X ω) ≤ a} := by
    ext ω
    simp only [mem_setOf_eq, Set.mem_sdiff, not_le]
    exact and_comm
  have hsub : {ω | F (X ω) ≤ a} ⊆ {ω | F (X ω) ≤ b} := by
    intro ω hω
    exact le_trans hω hab
  have hmeas : MeasurableSet {ω | F (X ω) ≤ a} :=
    measurableSet_le (hF.measurable.comp hX) measurable_const
  rw [he, measureReal_sdiff (μ := μ) hsub hmeas]
  rw [continuous_cdf_transform X F hF hmono h0 h1 hCDF b (ha.trans hab) hb,
    continuous_cdf_transform X F hF hmono h0 h1 hCDF a ha (hab.trans hb)]


/-- Probability-integral transform for the actual marginal law of a measurable sample. -/
theorem marginal_cdf_transform {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X)
    (hcont : Continuous (cdf (μ.map X)))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    μ.real {ω | cdf (μ.map X) (X ω) ≤ t} = t := by
  letI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  apply continuous_cdf_transform X (cdf (μ.map X)) hcont (monotone_cdf _)
    (tendsto_cdf_atBot _) (tendsto_cdf_atTop _) _ t ht0 ht1
  intro x
  rw [cdf_eq_real, map_measureReal_apply hX measurableSet_Iic]
  rfl

end Exceedance
#print axioms Exceedance.continuous_cdf_transform_interior

#print axioms Exceedance.continuous_cdf_transform

#print axioms Exceedance.continuous_cdf_transform_interval

#print axioms Exceedance.marginal_cdf_transform
