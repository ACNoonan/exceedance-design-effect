import CountInversion
import ClusterModel
import Exceedance

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

/-- Replace each observation by two identical copies. -/
def duplicatedSample {n : ℕ} (x : Fin n → ℝ) (i : Fin (n*2)) : ℝ :=
  x (finProdFinEquiv.symm i).1

/-- A permutation does not change the number of observations below any threshold. -/
lemma threshold_card_permutation {n : ℕ} (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (t : ℝ) :
    (Finset.univ.filter (fun i ↦ x (σ i) ≤ t)).card =
      (Finset.univ.filter (fun i ↦ x i ≤ t)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Equiv.sum_comp σ (fun i ↦ if x i ≤ t then (1 : ℕ) else 0)

/-- A sample quantile is invariant under arbitrary reordering, including with ties. -/
lemma sampleQuantile_permutation {n : ℕ} (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    sampleQuantile (fun i ↦ x (σ i)) k = sampleQuantile x k := by
  have he (t : ℝ) : sampleQuantile (fun i ↦ x (σ i)) k ≤ t ↔ sampleQuantile x k ≤ t := by
    rw [sampleQuantile_le_iff, sampleQuantile_le_iff, threshold_card_permutation]
  exact le_antisymm ((he _).mpr le_rfl) ((he _).mp le_rfl)

/-- Duplication doubles every threshold count exactly. -/
lemma duplicatedSample_count {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    (Finset.univ.filter (fun i ↦ duplicatedSample x i ≤ t)).card =
      2 * (Finset.univ.filter (fun i ↦ x i ≤ t)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  have he := Equiv.sum_comp (finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n*2))
    (fun i ↦ if duplicatedSample x i ≤ t then (1 : ℕ) else 0)
  rw [← he, Fintype.sum_prod_type]
  simp only [duplicatedSample, Equiv.symm_apply_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The zero-based rank k in a duplicated sample selects rank floor(k/2) in the base sample. -/
theorem duplicatedSample_quantile {n : ℕ} (x : Fin n → ℝ) (k : Fin (n*2)) :
    sampleQuantile (duplicatedSample x) k =
      sampleQuantile x ⟨k.val/2, by have hk := k.isLt; omega⟩ := by
  have he (t : ℝ) : sampleQuantile (duplicatedSample x) k ≤ t ↔
      sampleQuantile x ⟨k.val/2, by have hk := k.isLt; omega⟩ ≤ t := by
    rw [sampleQuantile_le_iff, sampleQuantile_le_iff, duplicatedSample_count]
    change k.val+1 ≤ 2*(Finset.univ.filter (fun i ↦ x i ≤ t)).card ↔
      k.val/2+1 ≤ (Finset.univ.filter (fun i ↦ x i ≤ t)).card
    omega
  exact le_antisymm ((he _).mpr le_rfl) ((he _).mp le_rfl)

/-- The duplicated-rank identity survives any permutation, deterministic or random. -/
theorem permuted_duplicatedSample_quantile {n : ℕ} (x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin (n*2))) (k : Fin (n*2)) :
    sampleQuantile (fun i ↦ duplicatedSample x (σ i)) k =
      sampleQuantile x ⟨k.val/2, by have hk := k.isLt; omega⟩ := by
  rw [sampleQuantile_permutation, duplicatedSample_quantile]

/-- Pair duplication makes every threshold count even, regardless of random reordering. -/
theorem permuted_duplicatedSample_even_count {n : ℕ} (x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin (n*2))) (t : ℝ) :
    Even (Finset.univ.filter (fun i ↦ duplicatedSample x (σ i) ≤ t)).card := by
  rw [threshold_card_permutation, duplicatedSample_count]
  exact even_two_mul _

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The exact duplicated-rank relation also holds inside the actual expectation operator. -/
theorem permuted_duplicatedSample_expectation {n : ℕ} (X : Ω → Fin n → ℝ)
    (σ : Ω → Equiv.Perm (Fin (n*2))) (k : Fin (n*2)) :
    (∫ ω, sampleQuantile (fun i ↦ duplicatedSample (X ω) (σ ω i)) k ∂μ) =
      ∫ ω, sampleQuantile (X ω) ⟨k.val/2, by have hk := k.isLt; omega⟩ ∂μ := by
  apply integral_congr_ae
  exact Eventually.of_forall (fun ω ↦ permuted_duplicatedSample_quantile (X ω) (σ ω) k)

/-- The cluster (U,U,V,V), with arbitrary reordering, has twice the two-point threshold count. -/
lemma duplicated_pair_count (u v t : ℝ) (σ : Equiv.Perm (Fin 4)) :
    thresholdCount t (fun i : Fin 4 ↦ ![u,u,v,v] (σ i)) =
      2*((if u ≤ t then 1 else 0)+(if v ≤ t then 1 else 0)) := by
  classical
  unfold thresholdCount
  have he := Equiv.sum_comp σ (fun i : Fin 4 ↦ indicator {w : Fin 4 → ℝ | w i ≤ t} ![u,u,v,v])
  simp only [indicator, Set.indicator, mem_setOf_eq] at he ⊢
  rw [he]
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero]
  ring_nf

/-- Independent U and V give cluster-count variance 8p(1-p).
    Random coordinate permutations do not change this result. -/
theorem duplicated_pair_count_variance (U V : Ω → ℝ) (hU : Measurable U) (hV : Measurable V)
    (hindep : IndepFun U V μ) (t p : ℝ)
    (hpU : μ.real {ω | U ω ≤ t} = p) (hpV : μ.real {ω | V ω ≤ t} = p)
    (σ : Ω → Equiv.Perm (Fin 4)) :
    Var[fun ω ↦ thresholdCount t (fun i : Fin 4 ↦ ![U ω,U ω,V ω,V ω] (σ ω i)); μ] =
      8*p*(1-p) := by
  have hA := measurableSet_le hU (measurable_const : Measurable (fun _ : Ω ↦ t))
  have hB := measurableSet_le hV (measurable_const : Measurable (fun _ : Ω ↦ t))
  have he : (fun ω ↦ thresholdCount t (fun i : Fin 4 ↦ ![U ω,U ω,V ω,V ω] (σ ω i))) =
      (fun ω ↦ 2*(indicator {ω | U ω ≤ t} ω+indicator {ω | V ω ≤ t} ω)) := by
    funext ω
    rw [duplicated_pair_count]
    rfl
  have hi : IndepFun (indicator {ω | U ω ≤ t}) (indicator {ω | V ω ≤ t}) μ := by
    have hf : Measurable (fun x : ℝ ↦ if x ≤ t then (1 : ℝ) else 0) :=
      Measurable.ite measurableSet_Iic measurable_const measurable_const
    have heU : indicator {ω | U ω ≤ t} = (fun x : ℝ ↦ if x ≤ t then (1 : ℝ) else 0) ∘ U := by
      funext ω; rfl
    have heV : indicator {ω | V ω ≤ t} = (fun x : ℝ ↦ if x ≤ t then (1 : ℝ) else 0) ∘ V := by
      funext ω; rfl
    rw [heU, heV]
    exact hindep.comp hf hf
  rw [he, variance_const_mul, hi.variance_fun_add (indicator_memLp hA) (indicator_memLp hB),
    indicator_variance hA, indicator_variance hB, hpU, hpV]
  ring

end Exceedance
#print axioms Exceedance.permuted_duplicatedSample_quantile
#print axioms Exceedance.permuted_duplicatedSample_even_count
#print axioms Exceedance.permuted_duplicatedSample_expectation
#print axioms Exceedance.duplicated_pair_count_variance
