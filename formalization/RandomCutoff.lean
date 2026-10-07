import QuantileConcentration

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Monotone empirical functions remain consistent at a cutoff fitted on the same sample. -/
theorem monotone_random_cutoff_consistency
    (A : ℕ → ℝ → Ω → ℝ) (C : ℕ → Ω → ℝ) (g : ℝ → ℝ) (p : ℝ)
    (hmono : ∀ n ω, Monotone (fun t ↦ A n t ω))
    (hg : ContinuousAt g p)
    (hA : ∀ t, TendstoInMeasure μ (fun n ω ↦ A n t ω) atTop (fun _ ↦ g t))
    (hC : TendstoInMeasure μ C atTop (fun _ ↦ p)) :
    TendstoInMeasure μ (fun n ω ↦ A n (C n ω) ω) atTop (fun _ ↦ g p) := by
  simp only [tendstoInMeasure_iff_measureReal_norm] at hA hC ⊢
  intro e he
  obtain ⟨d, hd, hgd⟩ := Metric.continuousAt_iff.mp hg (e/2) (by positivity)
  let l := p-d/2
  let u := p+d/2
  have hl : |g l-g p| < e/2 := by
    apply hgd
    dsimp [l]
    rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity : 0 < d/2)]
    linarith
  have hu : |g u-g p| < e/2 := by
    apply hgd
    dsimp [u]
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity : 0 < d/2)]
    linarith
  have hlim := ((hC (d/2) (by positivity)).add
    (hA l (e/2) (by positivity))).add (hA u (e/2) (by positivity))
  simp only [zero_add] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
  · intro n; exact measureReal_nonneg
  · intro n
    have hs : {ω | e ≤ ‖A n (C n ω) ω - g p‖} ⊆
        ({ω | d/2 ≤ ‖C n ω-p‖} ∪ {ω | e/2 ≤ ‖A n l ω-g l‖}) ∪
          {ω | e/2 ≤ ‖A n u ω-g u‖} := by
      intro ω hω
      by_contra hn
      simp only [mem_union, mem_setOf_eq, not_or, not_le, Real.norm_eq_abs] at hn
      have hc := abs_lt.mp hn.1.1
      have hal := abs_lt.mp hn.1.2
      have hau := abs_lt.mp hn.2
      have hgl := abs_lt.mp hl
      have hgu := abs_lt.mp hu
      have hlow := hmono n ω (show l ≤ C n ω by dsimp [l]; linarith [hc.1])
      have hupp := hmono n ω (show C n ω ≤ u by dsimp [u]; linarith [hc.2])
      have hh : |A n (C n ω) ω-g p| < e := abs_lt.mpr ⟨by linarith, by linarith⟩
      exact (not_le_of_gt hh) hω
    exact (measureReal_mono (μ := μ) hs).trans
      ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))

/-- Continuous arithmetic preserves convergence in probability to constants. -/
theorem continuous_pair_tendstoInMeasure (X Y : ℕ → Ω → ℝ) (a b : ℝ)
    (hX : TendstoInMeasure μ X atTop (fun _ ↦ a))
    (hY : TendstoInMeasure μ Y atTop (fun _ ↦ b))
    (f : ℝ × ℝ → ℝ) (hf : ContinuousAt f (a,b)) :
    TendstoInMeasure μ (fun n ω ↦ f (X n ω, Y n ω)) atTop (fun _ ↦ f (a,b)) := by
  simp only [tendstoInMeasure_iff_measureReal_norm] at hX hY ⊢
  intro e he
  obtain ⟨d, hd, hfd⟩ := Metric.continuousAt_iff.mp hf e he
  have hl := (hX d hd).add (hY d hd)
  simp only [zero_add] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
  · intro n; exact measureReal_nonneg
  · intro n
    apply (measureReal_mono (μ := μ) (show {ω | e ≤ ‖f (X n ω,Y n ω)-f (a,b)‖} ⊆
        {ω | d ≤ ‖X n ω-a‖} ∪ {ω | d ≤ ‖Y n ω-b‖} from ?_)).trans (measureReal_union_le _ _)
    intro ω hω
    by_contra hn
    simp only [mem_union, mem_setOf_eq, not_or, not_le] at hn
    have hh := hfd (show dist (X n ω,Y n ω) (a,b) < d by
      simpa only [Prod.dist_eq, Real.dist_eq, Real.norm_eq_abs, max_lt_iff] using hn)
    exact (not_le_of_gt hh) hω

end Exceedance
#print axioms Exceedance.monotone_random_cutoff_consistency

#print axioms Exceedance.continuous_pair_tendstoInMeasure
