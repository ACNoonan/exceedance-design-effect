import IndicatorVariance

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Any pair with uniform marginals has a 2-Lipschitz diagonal. -/
theorem pair_diagonal_lipschitz (U V : Ω → ℝ) (hU : Measurable U) (hV : Measurable V)
    (hu : ∀ t ∈ Icc (0:ℝ) 1, μ.real {ω | U ω ≤ t} = t)
    (hv : ∀ t ∈ Icc (0:ℝ) 1, μ.real {ω | V ω ≤ t} = t)
    (s t : ℝ) (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    |μ.real {ω | U ω ≤ t ∧ V ω ≤ t}-μ.real {ω | U ω ≤ s ∧ V ω ≤ s}| ≤ 2*|t-s| := by
  have bound (a b : ℝ) (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hab : a ≤ b) :
      0 ≤ μ.real {ω | U ω ≤ b ∧ V ω ≤ b}-μ.real {ω | U ω ≤ a ∧ V ω ≤ a} ∧
      μ.real {ω | U ω ≤ b ∧ V ω ≤ b}-μ.real {ω | U ω ≤ a ∧ V ω ≤ a} ≤ 2*(b-a) := by
    have hsub : {ω | U ω ≤ a ∧ V ω ≤ a} ⊆ {ω | U ω ≤ b ∧ V ω ≤ b} :=
      fun ω h ↦ ⟨h.1.trans hab, h.2.trans hab⟩
    refine ⟨sub_nonneg.mpr (measureReal_mono hsub), ?_⟩
    rw [← measureReal_sdiff hsub ((measurableSet_le hU measurable_const).inter
      (measurableSet_le hV measurable_const))]
    have hcover : {ω | U ω ≤ b ∧ V ω ≤ b} \ {ω | U ω ≤ a ∧ V ω ≤ a} ⊆
        ({ω | U ω ≤ b} \ {ω | U ω ≤ a}) ∪ ({ω | V ω ≤ b} \ {ω | V ω ≤ a}) := by
      intro ω h
      simp only [Set.mem_sdiff, mem_setOf_eq, mem_union] at *
      tauto
    calc
      _ ≤ μ.real (({ω | U ω ≤ b} \ {ω | U ω ≤ a}) ∪
          ({ω | V ω ≤ b} \ {ω | V ω ≤ a})) := measureReal_mono hcover
      _ ≤ μ.real ({ω | U ω ≤ b} \ {ω | U ω ≤ a}) +
          μ.real ({ω | V ω ≤ b} \ {ω | V ω ≤ a}) := measureReal_union_le _ _
      _ = 2*(b-a) := by
        rw [measureReal_sdiff (μ := μ) (s₁ := {ω | U ω ≤ b}) (s₂ := {ω | U ω ≤ a}) (fun ω h ↦ h.trans hab) (measurableSet_le hU measurable_const),
          measureReal_sdiff (μ := μ) (s₁ := {ω | V ω ≤ b}) (s₂ := {ω | V ω ≤ a}) (fun ω h ↦ h.trans hab) (measurableSet_le hV measurable_const),
          hu b hb, hu a ha, hv b hb, hv a ha]
        ring
  rcases le_total s t with h | h
  · have hh := bound s t hs ht h
    simpa only [abs_of_nonneg hh.1, abs_of_nonneg (sub_nonneg.mpr h)] using hh.2
  · have hh := bound t s ht hs h
    rw [abs_sub_comm, abs_of_nonneg hh.1, abs_sub_comm t s, abs_of_nonneg (sub_nonneg.mpr h)]
    exact hh.2

/-- The indicator correlation is continuous at every interior level. -/
theorem pair_indicator_correlation_continuousAt (U V : Ω → ℝ) (hU : Measurable U) (hV : Measurable V)
    (hu : ∀ t ∈ Icc (0:ℝ) 1, μ.real {ω | U ω ≤ t} = t)
    (hv : ∀ t ∈ Icc (0:ℝ) 1, μ.real {ω | V ω ≤ t} = t)
    (p : ℝ) (hp : p ∈ Ioo 0 1) :
    ContinuousAt (fun t ↦ (μ.real {ω | U ω ≤ t ∧ V ω ≤ t}-t^2)/(t*(1-t))) p := by
  have hd : ContinuousAt (fun t ↦ μ.real {ω | U ω ≤ t ∧ V ω ≤ t}) p := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨min (min p (1-p)) (ε/3), lt_min (lt_min hp.1 (sub_pos.mpr hp.2)) (by positivity), ?_⟩
    intro t ht
    rw [Real.dist_eq] at ht ⊢
    have ha := (abs_lt.mp (lt_of_lt_of_le ht (min_le_left _ _)))
    have ht0 : 0 ≤ t := by have := min_le_left p (1-p); linarith [ha.1]
    have ht1 : t ≤ 1 := by have := min_le_right p (1-p); linarith [ha.2]
    have hh := pair_diagonal_lipschitz U V hU hV hu hv p t ⟨hp.1.le,hp.2.le⟩ ⟨ht0,ht1⟩
    have he := lt_of_lt_of_le ht (min_le_right (min p (1-p)) (ε/3))
    linarith
  exact (hd.sub (continuousAt_id.pow 2)).div
    (continuousAt_id.mul (continuousAt_const.sub continuousAt_id)) (by nlinarith [hp.1, hp.2])

end Exceedance
#print axioms Exceedance.pair_diagonal_lipschitz
#print axioms Exceedance.pair_indicator_correlation_continuousAt
