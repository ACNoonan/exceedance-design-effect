import DuplicatedPairModel

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

lemma pair_pooled_count (b : ℕ) (ω : PairSequence) (t : ℝ) :
    (Finset.univ.filter (fun i ↦ pooledSample pairCluster b ω i ≤ t)).card =
      2*(Finset.univ.filter (fun i ↦ pairBaseSample b ω i ≤ t)).card := by
  classical
  have he : ((Finset.univ.filter (fun i ↦ pooledSample pairCluster b ω i ≤ t)).card : ℝ) =
      2*((Finset.univ.filter (fun i ↦ pairBaseSample b ω i ≤ t)).card : ℝ) := by
    rw [pooledSample_count]
    change (∑ j ∈ Finset.range b, thresholdCount t (pairCluster j ω)) =
      2*((Finset.univ.filter (fun i ↦ pooledSample (fun j ω ↦ (ω j).2) b ω i ≤ t)).card : ℝ)
    rw [pooledSample_count, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change thresholdCount t (fun i ↦ ![(ω j).2 0,(ω j).2 0,(ω j).2 1,(ω j).2 1] ((ω j).1 i)) = _
    rw [duplicated_pair_count]
    simp only [thresholdCount, indicator, Set.indicator, mem_setOf_eq, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  exact_mod_cast he

/-- The actual pooled iid cluster sample reduces to its independent latent sample. -/
theorem pair_pooled_quantile (b : ℕ) (ω : PairSequence) (k : Fin (b*4)) :
    sampleQuantile (pooledSample pairCluster b ω) k =
      sampleQuantile (pairBaseSample b ω) ⟨k.val/2, by have hk := k.isLt; omega⟩ := by
  have he (t : ℝ) : sampleQuantile (pooledSample pairCluster b ω) k ≤ t ↔
      sampleQuantile (pairBaseSample b ω) ⟨k.val/2, by have hk := k.isLt; omega⟩ ≤ t := by
    rw [sampleQuantile_le_iff, sampleQuantile_le_iff, pair_pooled_count]
    change k.val+1 ≤ 2*(Finset.univ.filter (fun i ↦ pairBaseSample b ω i ≤ t)).card ↔
      k.val/2+1 ≤ (Finset.univ.filter (fun i ↦ pairBaseSample b ω i ≤ t)).card
    omega
  exact le_antisymm ((he _).mpr le_rfl) ((he _).mp le_rfl)

/-- Exact expectation under the constructed infinite iid cluster probability measure. -/
theorem pair_pooled_expectation (b : ℕ) (k : Fin (b*4)) :
    (∫ ω, sampleQuantile (pooledSample pairCluster b ω) k ∂pairSequenceLaw) =
      ((k.val/2 : ℕ)+1 : ℝ)/(b*2+1) := by
  simp_rw [pair_pooled_quantile]
  exact pairBaseSample_expectation b _

def pairCounterexampleRank (h : ℕ) : Fin ((10*(h+1))*4) :=
  ⟨36*(h+1), by omega⟩

/-- The actual ranks follow the paper's ceiling rule at target p=9/10. -/
theorem pairCounterexampleRank_ceil (h : ℕ) :
    (pairCounterexampleRank h).val+1 =
      ⌈(((10*(h+1))*4 : ℕ)+1 : ℝ)*(9/10)⌉₊ := by
  symm
  apply (Nat.ceil_eq_iff (by simp [pairCounterexampleRank])).mpr
  simp only [pairCounterexampleRank, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) h]

noncomputable def pairCounterexampleCutoff (h : ℕ) (ω : PairSequence) : ℝ :=
  sampleQuantile (pooledSample pairCluster (10*(h+1)) ω) (pairCounterexampleRank h)

/-- The mean is derived from the actual sample, not assumed as a formula. -/
theorem pairCounterexample_expectation (h : ℕ) :
    (∫ ω, pairCounterexampleCutoff h ω ∂pairSequenceLaw) =
      (18*(h+1 : ℕ)+1 : ℝ)/(20*(h+1 : ℕ)+1) := by
  unfold pairCounterexampleCutoff
  rw [pair_pooled_expectation]
  have hr : 36*(h+1)/2 = 18*(h+1) := by omega
  simp only [pairCounterexampleRank, hr, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem pairCounterexample_scaled_drift (h : ℕ) :
    (10*(h+1 : ℕ) : ℝ)*((∫ ω, pairCounterexampleCutoff h ω ∂pairSequenceLaw) -
      (36*(h+1 : ℕ)+1 : ℝ)/(40*(h+1 : ℕ)+1)) =
      20*(h+1 : ℕ)^2 / ((20*(h+1 : ℕ)+1 : ℝ)*(40*(h+1 : ℕ)+1)) := by
  rw [pairCounterexample_expectation]
  exact duplicated_pair_scaled_drift (h+1 : ℕ) (by positivity)

/-- The actual scaled drift converges to +1/40 along b=10(h+1). -/
theorem pairCounterexample_drift_limit :
    Tendsto (fun h : ℕ ↦ (10*(h+1 : ℕ) : ℝ)*
      ((∫ ω, pairCounterexampleCutoff h ω ∂pairSequenceLaw) -
        (36*(h+1 : ℕ)+1 : ℝ)/(40*(h+1 : ℕ)+1))) atTop (nhds (1/40 : ℝ)) := by
  simp_rw [pairCounterexample_scaled_drift]
  have ht : Tendsto (fun h : ℕ ↦ ((h+1 : ℕ) : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hh := (tendsto_const_nhds (x := (20:ℝ))).div
    (((tendsto_const_nhds (x := (20:ℝ))).add ht).mul
      ((tendsto_const_nhds (x := (40:ℝ))).add ht)) (by norm_num)
  convert hh using 1
  · ext h
    have hn : ((h+1 : ℕ) : ℝ) ≠ 0 := by positivity
    change 20*((h+1 : ℕ) : ℝ)^2 / ((20*(h+1 : ℕ)+1 : ℝ)*(40*(h+1 : ℕ)+1)) =
      20/((20+((h+1 : ℕ) : ℝ)⁻¹)*(40+((h+1 : ℕ) : ℝ)⁻¹))
    field_simp
  · norm_num

end Exceedance
#print axioms Exceedance.pair_pooled_expectation
#print axioms Exceedance.pairCounterexampleRank_ceil
#print axioms Exceedance.pairCounterexample_drift_limit
