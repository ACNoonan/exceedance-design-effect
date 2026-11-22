import CoverageLimit
import BoundedArrayCLT
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.BigOperators.Fin

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

/-- A cluster with at most `M` row slots: its size and its slot values.
    Row `r` is active when `r.val < size`; the other slots carry no information. -/
abbrev SizedCluster (M : ℕ) := ℕ × (Fin M → ℝ)

/-- The observed cluster `(M_j, S_{j,1}, …, S_{j,M_j})`: inactive slots are erased. -/
def activeCluster {M : ℕ} (z : SizedCluster M) : SizedCluster M :=
  (z.1, fun r ↦ if r.val < z.1 then z.2 r else 0)

/-- The number of active rows whose transformed score is at most `t`. -/
noncomputable def sizedCount {M : ℕ} (G : ℝ → ℝ) (t : ℝ) (z : SizedCluster M) : ℝ :=
  ∑ r : Fin M, if r.val < z.1 ∧ G (z.2 r) ≤ t then (1:ℝ) else 0

/-- The paper's `Y_j(t) = X_j(t) - p₀ M_j`. At `t = p₀` it is the residual `R_j(p₀)`. -/
noncomputable def sizedResidual {M : ℕ} (G : ℝ → ℝ) (p0 t : ℝ) (z : SizedCluster M) : ℝ :=
  sizedCount G t z - p0 * (z.1 : ℝ)

lemma sizedCount_activeCluster {M : ℕ} (G : ℝ → ℝ) (t : ℝ) (z : SizedCluster M) :
    sizedCount G t (activeCluster z) = sizedCount G t z := by
  unfold sizedCount activeCluster
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : r.val < z.1 <;> simp [h]

lemma sizedResidual_activeCluster {M : ℕ} (G : ℝ → ℝ) (p0 t : ℝ) (z : SizedCluster M) :
    sizedResidual G p0 t (activeCluster z) = sizedResidual G p0 t z := by
  unfold sizedResidual
  rw [sizedCount_activeCluster]
  rfl

lemma measurable_sizedCount {M : ℕ} (G : ℝ → ℝ) (hG : Measurable G) (t : ℝ) :
    Measurable (sizedCount (M := M) G t) := by
  unfold sizedCount
  apply Finset.measurable_sum
  intro r _
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le (hG.comp ((measurable_pi_apply r).comp measurable_snd)) measurable_const)

lemma measurable_sizedResidual {M : ℕ} (G : ℝ → ℝ) (hG : Measurable G) (p0 t : ℝ) :
    Measurable (sizedResidual (M := M) G p0 t) :=
  (measurable_sizedCount G hG t).sub
    (measurable_const.mul (measurable_from_nat.comp measurable_fst))

lemma sizedCount_nonneg {M : ℕ} (G : ℝ → ℝ) (t : ℝ) (z : SizedCluster M) :
    0 ≤ sizedCount G t z :=
  Finset.sum_nonneg (fun r _ ↦ by split_ifs <;> norm_num)

/-- A cluster of size `m ≤ M` has exactly `m` active slots. -/
lemma slotCount_eq {M m : ℕ} (hm : m ≤ M) :
    (∑ r : Fin M, if r.val < m then (1:ℝ) else 0) = m := by
  have hf : (Finset.range M).filter (fun i ↦ i < m) = Finset.range m := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ if i < m then (1:ℝ) else 0) M, Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one, hf, Finset.card_range]

lemma sizedCount_le_size {M : ℕ} (G : ℝ → ℝ) (t : ℝ) (z : SizedCluster M) (hz : z.1 ≤ M) :
    sizedCount G t z ≤ z.1 := by
  rw [← slotCount_eq hz]
  apply Finset.sum_le_sum
  intro r _
  by_cases h1 : r.val < z.1 <;> by_cases h2 : G (z.2 r) ≤ t <;> simp [h1, h2]

/-- Counts are ordered whenever the threshold events are nested. -/
lemma sizedCount_mono {M : ℕ} (G1 G2 : ℝ → ℝ) (t1 t2 : ℝ)
    (himp : ∀ s, G1 s ≤ t1 → G2 s ≤ t2) (z : SizedCluster M) :
    sizedCount G1 t1 z ≤ sizedCount G2 t2 z := by
  apply Finset.sum_le_sum
  intro r _
  by_cases h : r.val < z.1 ∧ G1 (z.2 r) ≤ t1
  · rw [if_pos h, if_pos ⟨h.1, himp _ h.2⟩]
  · rw [if_neg h]
    split_ifs <;> norm_num

lemma sizedResidual_abs_le {M : ℕ} (G : ℝ → ℝ) (p0 t : ℝ) (hp : p0 ∈ Icc 0 1)
    (z : SizedCluster M) (hz : z.1 ≤ M) : |sizedResidual G p0 t z| ≤ M := by
  have h0 := sizedCount_nonneg G t z
  have h1 := sizedCount_le_size G t z hz
  have hzM : (z.1 : ℝ) ≤ M := by exact_mod_cast hz
  have hz0 : (0:ℝ) ≤ z.1 := Nat.cast_nonneg _
  have hm0 : 0 ≤ p0 * (z.1 : ℝ) := mul_nonneg hp.1 hz0
  have hm1 : p0 * (z.1 : ℝ) ≤ z.1 := by nlinarith [hp.2]
  unfold sizedResidual
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ### The pooled sample of random length -/

/-- The scores of all active rows of the first `b` clusters, as a multiset.
    Its cardinality is the random sample size. -/
noncomputable def pooledActive {M : ℕ} (z : ℕ → SizedCluster M) (b : ℕ) : Multiset ℝ :=
  ((Finset.range b ×ˢ (Finset.univ : Finset (Fin M))).filter
    (fun jr ↦ jr.2.val < (z jr.1).1)).val.map (fun jr ↦ (z jr.1).2 jr.2)

/-- The total number of rows `n = Σ_j M_j`. -/
def pooledSize {M : ℕ} (z : ℕ → SizedCluster M) (b : ℕ) : ℕ := ∑ j ∈ Finset.range b, (z j).1

/-- The one-based ceiling rank `k = ⌈(n+1)p₀⌉`. -/
noncomputable def pooledRank {M : ℕ} (p0 : ℝ) (z : ℕ → SizedCluster M) (b : ℕ) : ℕ :=
  Nat.ceil (((pooledSize z b : ℝ)+1)*p0)

/-- The `k`-th smallest pooled active score. It is `none`, the infinite cutoff,
    when the rank exceeds the number of active rows. -/
noncomputable def pooledCutoff {M : ℕ} (p0 : ℝ) (z : ℕ → SizedCluster M) (b : ℕ) : Option ℝ :=
  ((pooledActive z b).sort (· ≤ ·))[pooledRank p0 z b - 1]?

/-- Conditional coverage `C = F(q̂)`, equal to one at the infinite cutoff. -/
noncomputable def pooledCoverage {M : ℕ} (F : ℝ → ℝ) (p0 : ℝ) (z : ℕ → SizedCluster M)
    (b : ℕ) : ℝ :=
  (pooledCutoff p0 z b).elim 1 F

lemma list_boole_sum_le_length (l : List ℝ) (p : ℝ → Prop) [DecidablePred p] :
    (l.map (fun s ↦ if p s then (1:ℕ) else 0)).sum ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    split_ifs <;> omega

/-- Count inversion for a sorted list after a nondecreasing transformation.
    Past the end of the list the cutoff is infinite and the transformed value is `c`. -/
theorem sorted_getElem?_le_iff (l : List ℝ) (hl : l.Pairwise (· ≤ ·)) (G : ℝ → ℝ)
    (hG : Monotone G) (i : ℕ) (t c : ℝ) (hc : t < c) :
    (l[i]?).elim c G ≤ t ↔ i+1 ≤ (l.map (fun s ↦ if G s ≤ t then (1:ℕ) else 0)).sum := by
  by_cases hi : i < l.length
  · rw [List.getElem?_eq_getElem hi, Option.elim_some]
    have hm : Monotone (fun j : Fin l.length ↦ G (l.get j)) := hG.comp hl.sortedLE.monotone_get
    have ho := ordered_count_iff _ hm ⟨i, hi⟩ t
    have hs : (Finset.univ.filter (fun j : Fin l.length ↦ G (l.get j) ≤ t)).card =
        (l.map (fun s ↦ if G s ≤ t then (1:ℕ) else 0)).sum := by
      conv_rhs => rw [← List.ofFn_get l, List.map_ofFn, List.sum_ofFn]
      rw [Finset.card_filter]
      rfl
    rw [hs] at ho
    simpa only [List.get_eq_getElem] using ho
  · rw [List.getElem?_eq_none (not_lt.mp hi), Option.elim_none]
    have hh := list_boole_sum_le_length l (fun s ↦ G s ≤ t)
    constructor
    · intro h; linarith
    · intro h; omega

/-- The pooled threshold count is the sum of the cluster counts. -/
lemma pooled_boole_sum {M : ℕ} (z : ℕ → SizedCluster M) (b : ℕ) (G : ℝ → ℝ) (t : ℝ) :
    ((((pooledActive z b).sort (· ≤ ·)).map (fun s ↦ if G s ≤ t then (1:ℕ) else 0)).sum : ℝ) =
      ∑ j ∈ Finset.range b, sizedCount G t (z j) := by
  have h1 : (((pooledActive z b).sort (· ≤ ·)).map (fun s ↦ if G s ≤ t then (1:ℕ) else 0)).sum =
      ((pooledActive z b).map (fun s ↦ if G s ≤ t then (1:ℕ) else 0)).sum := by
    conv_rhs => rw [← Multiset.sort_eq (pooledActive z b) (· ≤ ·)]
    rw [Multiset.map_coe, Multiset.sum_coe]
  rw [h1, pooledActive, Multiset.map_map, ← Finset.sum_eq_multiset_sum, Finset.sum_filter,
    Finset.sum_product]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  unfold sizedCount
  apply Finset.sum_congr rfl
  intro r _
  by_cases h1 : r.val < (z j).1 <;> by_cases h2 : G ((z j).2 r) ≤ t <;> simp [h1, h2]

/-- With sizes at most `M`, the pooled sample has exactly `n = Σ_j M_j` rows. -/
lemma pooledActive_card {M : ℕ} (z : ℕ → SizedCluster M) (hz : ∀ j, (z j).1 ≤ M) (b : ℕ) :
    ((pooledActive z b).sort (· ≤ ·)).length = pooledSize z b := by
  have hc : (((pooledActive z b).sort (· ≤ ·)).length : ℝ) = (pooledSize z b : ℝ) := by
    have hh := pooled_boole_sum z b (fun _ ↦ 0) 0
    simp only [le_refl, if_true, List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at hh
    rw [hh]
    unfold pooledSize
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    unfold sizedCount
    simp only [le_refl, and_true]
    exact slotCount_eq (hz j)
  exact_mod_cast hc

/-- The cutoff is infinite exactly when the ceiling rank is `n+1`. -/
lemma pooledCutoff_eq_none_iff {M : ℕ} (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (z : ℕ → SizedCluster M)
    (hz : ∀ j, (z j).1 ≤ M) (b : ℕ) :
    pooledCutoff p0 z b = none ↔ pooledRank p0 z b = pooledSize z b + 1 := by
  have hk : 0 < pooledRank p0 z b :=
    Nat.ceil_pos.mpr (mul_pos (by positivity) hp.1)
  have hle : pooledRank p0 z b ≤ pooledSize z b + 1 := by
    apply Nat.ceil_le.mpr
    have hn : (0:ℝ) ≤ (pooledSize z b : ℝ)+1 := by positivity
    push_cast
    nlinarith [hp.2]
  unfold pooledCutoff
  rw [List.getElem?_eq_none_iff, pooledActive_card z hz b]
  omega

/-- The count identity of Appendix B.11 for the actual pooled order statistic:
    for `t < 1`, `{C ≤ t} = {Σ_j [X_j(t) - p₀ M_j] ≥ p₀}`, including the infinite cutoff. -/
theorem pooledCoverage_le_iff {M : ℕ} (F : ℝ → ℝ) (hF : Monotone F) (p0 : ℝ)
    (hp : p0 ∈ Ioo 0 1) (z : ℕ → SizedCluster M) (b : ℕ) (t : ℝ) (ht : t < 1) :
    pooledCoverage F p0 z b ≤ t ↔ p0 ≤ ∑ j ∈ Finset.range b, sizedResidual F p0 t (z j) := by
  have hk : 0 < pooledRank p0 z b :=
    Nat.ceil_pos.mpr (mul_pos (by positivity) hp.1)
  unfold pooledCoverage pooledCutoff
  rw [sorted_getElem?_le_iff _ (Multiset.pairwise_sort _ _) F hF _ t 1 ht, Nat.sub_add_cancel hk]
  unfold pooledRank
  rw [Nat.ceil_le, pooled_boole_sum]
  unfold sizedResidual
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold pooledSize
  push_cast
  constructor <;> intro h <;> linarith

end Exceedance

#print axioms Exceedance.sorted_getElem?_le_iff
#print axioms Exceedance.pooledActive_card
#print axioms Exceedance.pooledCutoff_eq_none_iff
#print axioms Exceedance.pooledCoverage_le_iff
