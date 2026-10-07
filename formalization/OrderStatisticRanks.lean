import DuplicatedPairs
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

lemma sampleQuantile_lt_iff {n : ℕ} (x : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    sampleQuantile x k < t ↔ k.val+1 ≤ (Finset.univ.filter (fun i ↦ x i < t)).card := by
  classical
  have hc : (Finset.univ.filter (fun i ↦ x (Tuple.sort x i) < t)).card =
      (Finset.univ.filter (fun i ↦ x i < t)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Equiv.sum_comp (Tuple.sort x) (fun i ↦ if x i < t then (1 : ℕ) else 0)
  rw [← hc]
  constructor
  · intro h
    have hs : Finset.Iic k ⊆ Finset.univ.filter (fun i ↦ x (Tuple.sort x i) < t) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        ((Tuple.monotone_sort x) (Finset.mem_Iic.mp hi)).trans_lt h⟩
    simpa only [Fin.card_Iic] using Finset.card_le_card hs
  · intro h
    by_contra hn
    have hs : Finset.univ.filter (fun i ↦ x (Tuple.sort x i) < t) ⊆ Finset.Iio k := by
      intro i hi
      apply Finset.mem_Iio.mpr
      by_contra hki
      have hh := (Tuple.monotone_sort x) (le_of_not_gt hki)
      exact hn (hh.trans_lt (Finset.mem_filter.mp hi).2)
    have hh := Finset.card_le_card hs
    rw [Fin.card_Iio] at hh
    omega

lemma count_at_sampleQuantile {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (k : Fin n) :
    (Finset.univ.filter (fun i ↦ x i ≤ sampleQuantile x k)).card = k.val+1 := by
  classical
  rw [← threshold_card_permutation x (Tuple.sort x)]
  have hstrict : StrictMono (x ∘ Tuple.sort x) :=
    (Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Tuple.sort x).injective)
  have he : Finset.univ.filter (fun i ↦ x (Tuple.sort x i) ≤ sampleQuantile x k) =
      Finset.Iic k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    exact hstrict.le_iff_le
  rw [he, Fin.card_Iic]

lemma heldout_rank_identity {n : ℕ} (x : Fin (n+1) → ℝ) (k : Fin n) :
    x 0 ≤ sampleQuantile (fun i ↦ x i.succ) k ↔
      x 0 ≤ sampleQuantile x k.castSucc := by
  classical
  rw [← not_lt, ← not_lt, sampleQuantile_lt_iff, sampleQuantile_lt_iff]
  have he : (Finset.univ.filter (fun i : Fin (n+1) ↦ x i < x 0)).card =
      (Finset.univ.filter (fun i : Fin n ↦ x i.succ < x 0)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_succ]
    simp
  rw [he]
  rfl

lemma iid_vector_permutation {n : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun x : Fin n → ℝ ↦ fun i ↦ x (σ i))
      (Measure.pi (fun _ : Fin n ↦ ν)) (Measure.pi (fun _ : Fin n ↦ ν)) := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin n ↦ ν) σ.symm
  convert h using 1
  ext x i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

lemma iid_vector_ae_injective {n : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n ↦ ν), Function.Injective x := by
  classical
  let P := Measure.pi (fun _ : Fin n ↦ ν)
  have hm (i : Fin n) : P.map (fun x ↦ x i) = ν := by
    simpa [P, Function.eval] using Measure.pi_map_eval (fun _ : Fin n ↦ ν) i
  have hi : iIndepFun (fun i : Fin n ↦ fun x : Fin n → ℝ ↦ x i) P :=
    iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)
  have hne (i j : Fin n) (hij : i ≠ j) : ∀ᵐ x ∂P, x i ≠ x j := by
    have hmap := (hi.indepFun hij).map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
    rw [hm, hm] at hmap
    have hzero : (ν.prod ν) {z : ℝ × ℝ | z.1 = z.2} = 0 := by
      rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
      have he (a : ℝ) : {b : ℝ | a = b} = {a} := by ext b; simp [eq_comm]
      simp only [Set.preimage_setOf_eq, he, measure_singleton, lintegral_zero]
    have hz : P {x | x i = x j} = 0 := by
      rw [← hmap, Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
        (measurableSet_eq_fun measurable_fst measurable_snd)] at hzero
      exact hzero
    simpa only [ae_iff, not_not] using hz
  have hall : ∀ᵐ x ∂P, ∀ i j, i ≠ j → x i ≠ x j := by
    simp only [ae_all_iff]
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · simpa [hij] using hne i j hij
  filter_upwards [hall] with x hx
  exact fun i j he ↦ by_contra (fun hij ↦ hx i j hij he)

/-- Each coordinate of an iid atomless sample occupies each rank with equal probability. -/
theorem iid_rank_probability {n : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (k : Fin n) (i : Fin n) :
    (Measure.pi (fun _ : Fin n ↦ ν)).real {x | x i ≤ sampleQuantile x k} =
      (k.val+1 : ℝ)/n := by
  classical
  let P := Measure.pi (fun _ : Fin n ↦ ν)
  let A := fun j : Fin n ↦ {x : Fin n → ℝ | x j ≤ sampleQuantile x k}
  have hA (j : Fin n) : MeasurableSet (A j) :=
    measurableSet_le (measurable_pi_apply j) (measurable_sampleQuantile _ measurable_pi_apply k)
  have he (j : Fin n) : P.real (A j) = P.real (A i) := by
    let σ := Equiv.swap i j
    have hp := iid_vector_permutation ν σ
    have hs : (fun x : Fin n → ℝ ↦ fun l ↦ x (σ l)) ⁻¹' A i = A j := by
      ext x
      simp [A, σ, sampleQuantile_permutation]
    rw [← hs]
    exact hp.measureReal_preimage (hA i).nullMeasurableSet
  have hsum : ∑ j : Fin n, P.real (A j) = (k.val+1 : ℝ) := by
    calc
      _ = ∫ x, ∑ j : Fin n, indicator (A j) x ∂P := by
        rw [integral_finsetSum _ (fun j _ ↦ (indicator_memLp (hA j)).integrable (by norm_num))]
        simp_rw [indicator_mean (hA _)]
      _ = ∫ _ : Fin n → ℝ, (k.val+1 : ℝ) ∂P := by
        apply integral_congr_ae
        filter_upwards [iid_vector_ae_injective ν] with x hx
        have hh := count_at_sampleQuantile x hx k
        simp only [indicator, Set.indicator, A, Set.mem_setOf_eq]
        exact_mod_cast (show (∑ j : Fin n, if x j ≤ sampleQuantile x k then (1:ℕ) else 0) = k.val+1 by
          simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using hh)
      _ = _ := by simp
  simp_rw [he] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  change P.real (A i) = _
  apply (eq_div_iff (show (n:ℝ) ≠ 0 by exact_mod_cast (Nat.ne_zero_of_lt k.isLt))).mpr
  linarith

end Exceedance
#print axioms Exceedance.iid_rank_probability
