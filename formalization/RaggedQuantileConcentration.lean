import QuantileConcentration

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

abbrev RaggedIndex {b : ℕ} (m : Fin b → ℕ) := (j : Fin b) × Fin (m j)
def raggedSize {b : ℕ} (m : Fin b → ℕ) : ℕ := Fintype.card (RaggedIndex m)

lemma raggedSize_eq_sum {b : ℕ} (m : Fin b → ℕ) : raggedSize m = ∑ j, m j := by
  simp [raggedSize, RaggedIndex, Fintype.card_sigma]

noncomputable def raggedSample {Ω : Type*} {b : ℕ} (m : Fin b → ℕ)
    (U : (j : Fin b) → Ω → Fin (m j) → ℝ) (ω : Ω) (i : Fin (raggedSize m)) : ℝ :=
  let a := (Fintype.equivFin (RaggedIndex m)).symm i
  U a.1 ω a.2

lemma raggedSample_count {Ω : Type*} {b : ℕ} (m : Fin b → ℕ)
    (U : (j : Fin b) → Ω → Fin (m j) → ℝ) (ω : Ω) (t : ℝ) :
    ((Finset.univ.filter (fun i ↦ raggedSample m U ω i ≤ t)).card : ℝ) =
      ∑ j, thresholdCount t (U j ω) := by
  classical
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, apply_ite, Nat.cast_one, Nat.cast_zero]
  change (∑ i : Fin (raggedSize m), if raggedSample m U ω i ≤ t then (1 : ℝ) else 0) = _
  have he := Equiv.sum_comp (Fintype.equivFin (RaggedIndex m))
    (fun i ↦ if raggedSample m U ω i ≤ t then (1 : ℝ) else 0)
  have hpoint (a : RaggedIndex m) :
      raggedSample m U ω (Fintype.equivFin (RaggedIndex m) a) = U a.1 ω a.2 := by
    exact congrArg (fun a : RaggedIndex m ↦ U a.1 ω a.2)
      ((Fintype.equivFin (RaggedIndex m)).symm_apply_apply a)
  calc
    _ = ∑ a : RaggedIndex m, if raggedSample m U ω (Fintype.equivFin (RaggedIndex m) a) ≤ t then (1 : ℝ) else 0 := he.symm
    _ = _ := by
      simp_rw [hpoint]
      rw [Fintype.sum_sigma]
      rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma ragged_quantile_support {b : ℕ} (m : Fin b → ℕ)
    (U : (j : Fin b) → Ω → Fin (m j) → ℝ) (hU : ∀ j, Measurable (U j))
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (k : Fin (raggedSize m)) :
    ∀ᵐ ω ∂μ, sampleQuantile (raggedSample m U ω) k ∈ Icc 0 1 := by
  have hall : ∀ᵐ ω ∂μ, ∀ j i, U j ω i ∈ Icc 0 1 := by
    simp only [ae_all_iff]
    intro j i
    exact uniform_marginal_support _ ((measurable_pi_apply i).comp (hU j)) (hunif j i)
  filter_upwards [hall] with ω hω
  exact hω _ _

lemma ragged_count_tails {b : ℕ} (m : Fin b → ℕ)
    (U : (j : Fin b) → Ω → Fin (m j) → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (t : ℝ) (ht : t ∈ Icc 0 1) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ (∑ j, thresholdCount t (U j ω)) - (raggedSize m : ℝ)*t} ≤
      Real.exp (-2*ε^2/(∑ j, (m j : ℝ)^2)) ∧
    μ.real {ω | ε ≤ (raggedSize m : ℝ)*t - (∑ j, thresholdCount t (U j ω))} ≤
      Real.exp (-2*ε^2/(∑ j, (m j : ℝ)^2)) := by
  let X := fun j ω ↦ thresholdCount t (U j ω)
  have hX (j : Fin b) : Measurable (X j) := (measurable_thresholdCount t).comp (hU j)
  have hi : iIndepFun X μ := hindep.comp (fun _ ↦ thresholdCount t) (fun _ ↦ measurable_thresholdCount t)
  have hb (j : Fin b) : ∀ᵐ ω ∂μ, X j ω ∈ Icc 0 (m j : ℝ) :=
    Eventually.of_forall (fun ω ↦ by simpa using thresholdCount_bounds (U j ω) t)
  have hmean (j : Fin b) : (∫ ω, X j ω ∂μ) = (m j : ℝ)*t := by
    simpa [X] using thresholdCount_mean (U j) (hU j) t (fun i ↦ hunif j i t ht.1 ht.2)
  have hu := cluster_count_upper_tail X (fun j ↦ (m j : ℝ)) (fun j ↦ (hX j).aemeasurable) hb hi ε hε
  have hl := cluster_count_lower_tail X (fun j ↦ (m j : ℝ)) (fun j ↦ (hX j).aemeasurable) hb hi ε hε
  simp only [hmean, Finset.sum_sub_distrib, ← Finset.sum_mul, X] at hu hl
  simpa only [raggedSize_eq_sum, Nat.cast_sum] using And.intro hu hl

/-- Finite-sample coverage concentration with arbitrary fixed unequal cluster sizes. -/
theorem ragged_quantile_tail {b : ℕ} (m : Fin b → ℕ)
    (U : (j : Fin b) → Ω → Fin (m j) → ℝ)
    (hU : ∀ j, Measurable (U j)) (hindep : iIndepFun U μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (k : Fin (raggedSize m)) (x : ℝ) (hx : 0 ≤ x) :
    μ.real {ω | x < |sampleQuantile (raggedSample m U ω) k -
      ((k.val+1 : ℕ) : ℝ)/((raggedSize m : ℕ)+1)|} ≤
      2 * Real.exp (-2*((raggedSize m : ℕ) : ℝ)^2*x^2/(∑ j, (m j : ℝ)^2)) := by
  classical
  let N : ℝ := (raggedSize m : ℕ)
  let p : ℝ := ((k.val+1 : ℕ) : ℝ)/(N+1)
  let C : Ω → ℝ := fun ω ↦ sampleQuantile (raggedSample m U ω) k
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  have hkp : ((k.val+1 : ℕ) : ℝ) = (N+1)*p := by
    dsimp [p]; field_simp
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    apply (div_le_one (by positivity : 0 < N+1)).mpr
    have hk : k.val+1 ≤ raggedSize m := k.isLt
    have hk' : ((k.val+1 : ℕ) : ℝ) ≤ N := by dsimp [N]; exact_mod_cast hk
    linarith
  let R : ℝ := Real.exp (-2*N^2*x^2/(∑ j, (m j : ℝ)^2))
  have hR : 0 ≤ R := (Real.exp_pos _).le
  have hs := ragged_quantile_support m U hU hunif k
  have hlo : μ.real {ω | C ω < p-x} ≤ R := by
    by_cases ht : 0 ≤ p-x
    · have ht1 : p-x ≤ 1 := by linarith
      have hu := (ragged_count_tails m U hU hindep hunif (p-x) ⟨ht, ht1⟩
        (N*x) (mul_nonneg hN.le hx)).1
      have hsub : {ω | C ω < p-x} ⊆
          {ω | N*x ≤ (∑ j, thresholdCount (p-x) (U j ω)) -
            (raggedSize m : ℝ)*(p-x)} := by
        intro ω hω
        have hc := (sampleQuantile_le_iff (raggedSample m U ω) k (p-x)).mp hω.le
        have hc' : ((k.val+1 : ℕ) : ℝ) ≤
            ((Finset.univ.filter (fun i ↦ raggedSample m U ω i ≤ p-x)).card : ℝ) := by
          exact_mod_cast hc
        rw [raggedSample_count] at hc'
        have hn : (raggedSize m : ℝ) = N := rfl
        dsimp only [mem_setOf_eq]
        rw [hn]
        nlinarith
      have hh := (measureReal_mono (μ := μ) hsub).trans hu
      dsimp [R]
      convert hh using 1 <;> congr 1
      ring
    · have hz : μ {ω | C ω < p-x} = 0 := by
        have he : ∀ᵐ ω ∂μ, ¬ C ω < p-x := by
          filter_upwards [hs] with ω hω
          change C ω ∈ Icc 0 1 at hω
          linarith [hω.1]
        simpa only [not_not] using (ae_iff.mp he)
      rw [measureReal_def, hz, ENNReal.toReal_zero]
      exact hR
  have hhi : μ.real {ω | p+x < C ω} ≤ R := by
    by_cases ht : p+x ≤ 1
    · have ht0 : 0 ≤ p+x := by linarith
      have hl := (ragged_count_tails m U hU hindep hunif (p+x) ⟨ht0, ht⟩
        (N*x) (mul_nonneg hN.le hx)).2
      have hsub : {ω | p+x < C ω} ⊆
          {ω | N*x ≤ (raggedSize m : ℝ)*(p+x) -
            (∑ j, thresholdCount (p+x) (U j ω))} := by
        intro ω hω
        have hc := (sampleQuantile_gt_iff (raggedSample m U ω) k (p+x)).mp hω
        have hc' : ((Finset.univ.filter (fun i ↦ raggedSample m U ω i ≤ p+x)).card : ℝ) ≤
            (k.val : ℝ) := by exact_mod_cast hc
        rw [raggedSample_count] at hc'
        have hn : (raggedSize m : ℝ) = N := rfl
        have hkcast : ((k.val+1 : ℕ) : ℝ) = (k.val : ℝ)+1 := by simp
        dsimp only [mem_setOf_eq]
        rw [hn]
        nlinarith
      have hh := (measureReal_mono (μ := μ) hsub).trans hl
      dsimp [R]
      convert hh using 1 <;> congr 1
      ring
    · have hz : μ {ω | p+x < C ω} = 0 := by
        have he : ∀ᵐ ω ∂μ, ¬ p+x < C ω := by
          filter_upwards [hs] with ω hω
          change C ω ∈ Icc 0 1 at hω
          linarith [hω.2]
        simpa only [not_not] using (ae_iff.mp he)
      rw [measureReal_def, hz, ENNReal.toReal_zero]
      exact hR
  have he : {ω | x < |C ω-p|} = {ω | C ω < p-x} ∪ {ω | p+x < C ω} := by
    ext ω
    simp only [mem_setOf_eq, mem_union, lt_abs]
    constructor <;> intro h <;> rcases h with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  change μ.real {ω | x < |C ω-p|} ≤ 2*R
  rw [he]
  exact (measureReal_union_le _ _).trans (by linarith)


end Exceedance
#print axioms Exceedance.ragged_quantile_tail
