import Mathlib.Tactic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

namespace Exceedance

/-- Exact count inversion for an ordered finite sample, including ties.
    `k` is zero-based, so the corresponding one-based rank is `k.val + 1`.
    Sorting a random sample and proving its measurability are separate steps. -/
theorem ordered_count_iff {n : ℕ} (x : Fin n → ℝ) (hx : Monotone x)
    (k : Fin n) (t : ℝ) :
    x k ≤ t ↔ k.val + 1 ≤ (Finset.univ.filter (fun i ↦ x i ≤ t)).card := by
  classical
  constructor
  · intro h
    have hs : Finset.Iic k ⊆ Finset.univ.filter (fun i ↦ x i ≤ t) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (hx (Finset.mem_Iic.mp hi)).trans h⟩
    have hc := Finset.card_le_card hs
    simpa only [Fin.card_Iic] using hc
  · intro h
    by_contra hn
    have hs : Finset.univ.filter (fun i ↦ x i ≤ t) ⊆ Finset.Iio k := by
      intro i hi
      apply Finset.mem_Iio.mpr
      by_contra hki
      have hle : k ≤ i := le_of_not_gt hki
      exact hn ((hx hle).trans (Finset.mem_filter.mp hi).2)
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iio] at hc
    omega

/-- Complementary event used to integrate the order statistic's survival function. -/
theorem ordered_survival_iff {n : ℕ} (x : Fin n → ℝ) (hx : Monotone x)
    (k : Fin n) (t : ℝ) :
    t < x k ↔ (Finset.univ.filter (fun i ↦ x i ≤ t)).card ≤ k.val := by
  classical
  rw [← not_le, ordered_count_iff x hx k t]
  omega

noncomputable def sampleQuantile {n : ℕ} (x : Fin n → ℝ) (k : Fin n) : ℝ :=
  x (Tuple.sort x k)

/-- Count inversion for the actual sorted sample, with no assumption that inputs are ordered. -/
theorem sampleQuantile_le_iff {n : ℕ} (x : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    sampleQuantile x k ≤ t ↔ k.val + 1 ≤ (Finset.univ.filter (fun i ↦ x i ≤ t)).card := by
  classical
  have hc : (Finset.univ.filter (fun i ↦ x (Tuple.sort x i) ≤ t)).card =
      (Finset.univ.filter (fun i ↦ x i ≤ t)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Equiv.sum_comp (Tuple.sort x) (fun i ↦ if x i ≤ t then (1 : ℕ) else 0)
  have ho := ordered_count_iff (x ∘ Tuple.sort x) (Tuple.monotone_sort x) k t
  simpa only [Function.comp_apply, hc, sampleQuantile] using ho

/-- A finite sample quantile is measurable whenever each sampled value is measurable. -/
theorem measurable_sampleQuantile {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (k : Fin n) :
    Measurable (fun ω ↦ sampleQuantile (fun i ↦ X i ω) k) := by
  classical
  apply measurable_of_Iic
  intro t
  have hm : Measurable (fun ω ↦ ∑ i : Fin n, if X i ω ≤ t then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro i _
    exact Measurable.ite (measurableSet_le (hX i) measurable_const) measurable_const measurable_const
  have he : (fun ω ↦ sampleQuantile (fun i ↦ X i ω) k) ⁻¹' Set.Iic t =
      {ω | k.val+1 ≤ ∑ i : Fin n, if X i ω ≤ t then (1 : ℕ) else 0} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq, sampleQuantile_le_iff,
      Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [he]
  exact measurableSet_le measurable_const hm


/-- Any nondecreasing transformation commutes with the sample quantile.
    This includes a continuous CDF with flat regions; strict monotonicity is unnecessary. -/
theorem sampleQuantile_monotone_map {n : ℕ} (x : Fin n → ℝ) (k : Fin n)
    (F : ℝ → ℝ) (hF : Monotone F) :
    sampleQuantile (F ∘ x) k = F (sampleQuantile x k) := by
  have h := Tuple.unique_monotone (f := F ∘ x) (σ := Tuple.sort x)
    (τ := Tuple.sort (F ∘ x)) (hF.comp (Tuple.monotone_sort x)) (Tuple.monotone_sort (F ∘ x))
  exact (congrFun h k).symm


end Exceedance
#print axioms Exceedance.ordered_count_iff
#print axioms Exceedance.ordered_survival_iff

#print axioms Exceedance.measurable_sampleQuantile

#print axioms Exceedance.sampleQuantile_monotone_map
