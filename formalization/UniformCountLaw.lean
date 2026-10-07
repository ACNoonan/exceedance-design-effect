import UniformOrderStatistic

open MeasureTheory ProbabilityTheory Set
namespace Exceedance

/-- A specified subset of independent uniforms lies below a threshold with the product probability. -/
lemma uniform_threshold_pattern {n : ℕ} (s : Finset (Fin n)) (p : ℝ) (hp : p ∈ Icc 0 1) :
    (Measure.pi (fun _ : Fin n ↦ unitUniform)).real
      {x | ∀ i, (x i ≤ p ↔ i ∈ s)} = p^s.card*(1-p)^(n-s.card) := by
  classical
  have he : {x : Fin n → ℝ | ∀ i, (x i ≤ p ↔ i ∈ s)} =
      univ.pi (fun i ↦ if i ∈ s then Iic p else Ioi p) := by
    ext x
    simp only [mem_setOf_eq, mem_pi, mem_univ, true_implies]
    apply forall_congr'
    intro i
    by_cases hi : i ∈ s <;> simp [hi]
  rw [he, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  have hi : unitUniform.real (Ioi p) = 1-p := by
    rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ,
      unitUniform_cdf p hp.1 hp.2]
  change (∏ i : Fin n, unitUniform.real (if i ∈ s then Iic p else Ioi p)) = _
  simp_rw [apply_ite, unitUniform_cdf p hp.1 hp.2, hi]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hf : Finset.univ.filter (fun i : Fin n ↦ i ∈ s) = s := by ext i; simp
  have hn : (Finset.univ.filter (fun i : Fin n ↦ i ∉ s)).card = n-s.card := by
    rw [show Finset.univ.filter (fun i : Fin n ↦ i ∉ s) = Finset.univ \ s by ext i; simp,
      Finset.card_sdiff_of_subset (Finset.subset_univ s)]
    simp
  rw [hf,hn]

/-- The exact finite threshold-count law, obtained without assuming a binomial law. -/
theorem uniform_threshold_count_probability {n : ℕ} (k : ℕ) (p : ℝ) (hp : p ∈ Icc 0 1) :
    (Measure.pi (fun _ : Fin n ↦ unitUniform)).real
      {x | (Finset.univ.filter (fun i ↦ x i ≤ p)).card = k} =
        (n.choose k : ℝ)*p^k*(1-p)^(n-k) := by
  classical
  let A := fun s : Finset (Fin n) ↦ {x : Fin n → ℝ | ∀ i, (x i ≤ p ↔ i ∈ s)}
  let C := Finset.powersetCard k (Finset.univ : Finset (Fin n))
  have hA (s : Finset (Fin n)) : MeasurableSet (A s) := by
    dsimp [A]
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i ∈ s
    · simpa [A,hi] using measurableSet_le (show Measurable (fun x : Fin n → ℝ ↦ x i) from measurable_pi_apply i) (measurable_const (a := p))
    · simpa [A,hi] using measurableSet_lt (measurable_const (a := p)) (show Measurable (fun x : Fin n → ℝ ↦ x i) from measurable_pi_apply i)
  have hdis : Set.PairwiseDisjoint (C : Set (Finset (Fin n))) A := by
    intro s _ t _ hst
    apply disjoint_left.mpr
    intro x hs ht
    apply hst
    ext i
    exact (hs i).symm.trans (ht i)
  have he : {x : Fin n → ℝ | (Finset.univ.filter (fun i ↦ x i ≤ p)).card = k} =
      ⋃ s ∈ C, A s := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · intro hx
      refine ⟨Finset.univ.filter (fun i ↦ x i ≤ p), ?_, ?_⟩
      · exact Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, hx⟩
      · intro i; simp
    · rintro ⟨s,hs,hx⟩
      have hf : Finset.univ.filter (fun i ↦ x i ≤ p) = s := by
        ext i; simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx i
      rw [hf]
      exact (Finset.mem_powersetCard.mp hs).2
  rw [he, measureReal_biUnion_finset hdis (fun s _ ↦ hA s)]
  have hv (s : Finset (Fin n)) (hs : s ∈ C) :
      (Measure.pi (fun _ : Fin n ↦ unitUniform)).real (A s) = p^k*(1-p)^(n-k) := by
    rw [uniform_threshold_pattern s p hp, (Finset.mem_powersetCard.mp hs).2]
  rw [Finset.sum_congr rfl hv, Finset.sum_const]
  simp only [C, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring


/-- The exact survival probability of a uniform order statistic. -/
theorem uniform_orderStatistic_survival {n : ℕ} (k : Fin n) (p : ℝ) (hp : p ∈ Icc 0 1) :
    (Measure.pi (fun _ : Fin n ↦ unitUniform)).real {x | p < sampleQuantile x k} =
      ∑ i ∈ Finset.range (k.val+1), (n.choose i : ℝ)*p^i*(1-p)^(n-i) := by
  classical
  let C := fun x : Fin n → ℝ ↦ (Finset.univ.filter (fun i ↦ x i ≤ p)).card
  have hm : Measurable C := by
    simp only [C, Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.measurable_sum
    intro i _
    exact Measurable.ite (measurableSet_le (measurable_pi_apply i) measurable_const)
      measurable_const measurable_const
  have he : {x : Fin n → ℝ | p < sampleQuantile x k} =
      ⋃ i ∈ Finset.range (k.val+1), {x | C x = i} := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion, Finset.mem_range, ← not_le, sampleQuantile_le_iff]
    simp only [exists_prop]
    constructor
    · intro h
      exact ⟨C x,h,rfl⟩
    · rintro ⟨i,hi,hxi⟩
      change ¬ k.val+1 ≤ C x
      rwa [hxi]
  have hd : Set.PairwiseDisjoint (↑(Finset.range (k.val+1)) : Set ℕ) (fun i ↦ {x | C x = i}) := by
    intro i _ j _ hij
    apply disjoint_left.mpr
    intro x hxi hxj
    exact hij (hxi.symm.trans hxj)
  rw [he, measureReal_biUnion_finset hd (fun i _ ↦ measurableSet_eq_fun hm measurable_const)]
  apply Finset.sum_congr rfl
  intro i _
  exact uniform_threshold_count_probability i p hp

end Exceedance
#print axioms Exceedance.uniform_threshold_count_probability

#print axioms Exceedance.uniform_orderStatistic_survival
