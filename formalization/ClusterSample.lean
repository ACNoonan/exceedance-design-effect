import ClusterModel
import CoverageLimit
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

noncomputable def pooledSample {Ω : Type*} {m : ℕ}
    (U : ℕ → Ω → Fin m → ℝ) (b : ℕ) (ω : Ω) (i : Fin (b*m)) : ℝ :=
  U (finProdFinEquiv.symm i).1.val ω (finProdFinEquiv.symm i).2

/-- Flattening the cluster array preserves the exact threshold count. -/
theorem pooledSample_count {Ω : Type*} {m : ℕ}
    (U : ℕ → Ω → Fin m → ℝ) (b : ℕ) (ω : Ω) (t : ℝ) :
    ((Finset.univ.filter (fun i ↦ pooledSample U b ω i ≤ t)).card : ℝ) =
      ∑ j ∈ Finset.range b, thresholdCount t (U j ω) := by
  classical
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, apply_ite, Nat.cast_one, Nat.cast_zero]
  have he := Equiv.sum_comp (finProdFinEquiv : Fin b × Fin m ≃ Fin (b*m))
    (fun i ↦ if pooledSample U b ω i ≤ t then (1 : ℝ) else 0)
  rw [← he, Fintype.sum_prod_type]
  simp only [pooledSample, Equiv.symm_apply_apply]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [thresholdCount, indicator, Set.indicator, mem_setOf_eq]

/-- A finite initial segment does not change a distributional limit. -/
theorem distribution_limit_eventually_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (X Y : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (hX : TendstoInDistribution X atTop Z (fun _ ↦ μ) ν)
    (hY : ∀ n, AEMeasurable (Y n) μ)
    (he : ∀ᶠ n in atTop, X n = Y n) :
    TendstoInDistribution Y atTop Z (fun _ ↦ μ) ν := by
  refine ⟨hY, hX.aemeasurable_limit, ?_⟩
  apply hX.tendsto.congr'
  filter_upwards [he] with n hn
  simp only [hn]

/-- Reindexing from b clusters to b+1 avoids an empty pooled sample. -/
theorem distribution_limit_succ
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (hX : TendstoInDistribution X atTop Z (fun _ ↦ μ) ν) :
    TendstoInDistribution (fun n ↦ X (n+1)) atTop Z (fun _ ↦ μ) ν := by
  refine ⟨fun n ↦ hX.forall_aemeasurable (n+1), hX.aemeasurable_limit, ?_⟩
  exact hX.tendsto.comp (tendsto_add_atTop_nat 1)

/-- Interior limits allow arbitrary thresholds for finitely many initial sample sizes. -/
theorem iid_vector_moving_count_interior_clt
    {ι Ω Ω' : Type*} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (U : ℕ → Ω → ι → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ) (hident : ∀ j, IdentDistrib (U j) (U 0) μ μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (p : ℝ) (hp : p ∈ Ioo 0 1) (t : ℕ → ℝ) (htp : Tendsto t atTop (nhds p))
    (Z : Ω' → ℝ)
    (hZ : HasLaw Z (gaussianReal 0 Var[fun ω ↦ thresholdCount p (U 0 ω); μ].toNNReal) ν) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√((n : ℝ)*Fintype.card ι))⁻¹ *
      ((∑ j ∈ Finset.range n, thresholdCount (t n) (U j ω))-
        ((n : ℝ)*Fintype.card ι)*t n)) atTop
      (fun ω ↦ (√(Fintype.card ι : ℝ))⁻¹*Z ω) (fun _ ↦ μ) ν := by
  classical
  let t' : ℕ → ℝ := fun n ↦ if t n ∈ Icc 0 1 then t n else p
  have hte : ∀ᶠ n in atTop, t n ∈ Icc 0 1 := by
    filter_upwards [htp.eventually (Ioo_mem_nhds hp.1 hp.2)] with n hn
    exact ⟨hn.1.le, hn.2.le⟩
  have he : ∀ᶠ n in atTop, t' n = t n := by
    filter_upwards [hte] with n hn
    exact if_pos hn
  have ht' (n : ℕ) : t' n ∈ Icc 0 1 := by
    dsimp [t']
    split_ifs with hn
    · exact hn
    · exact ⟨hp.1.le, hp.2.le⟩
  have hc := iid_vector_moving_count_total_scale_clt U hU hindep hident hunif p
    ⟨hp.1.le, hp.2.le⟩ t' ht' (htp.congr' (he.mono (fun _ h ↦ h.symm))) Z hZ
  apply distribution_limit_eventually_eq _ _ _ hc
  · intro n
    exact (((memLp_finsetSum _ (fun j _ ↦ thresholdCount_memLp (U j) (hU j) (t n))).sub
      (memLp_const _)).const_mul _).aemeasurable
  · filter_upwards [he] with n hn
    rw [hn]

/-- The pooled sample's moving-count CLT, with all finite indexing made explicit. -/
theorem iid_pooled_moving_count_clt
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {m : ℕ}
    (U : ℕ → Ω → Fin m → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ) (hident : ∀ j, IdentDistrib (U j) (U 0) μ μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (p : ℝ) (hp : p ∈ Ioo 0 1) (t : ℕ → ℝ) (htp : Tendsto t atTop (nhds p))
    (Z : Ω' → ℝ)
    (hZ : HasLaw Z (gaussianReal 0 Var[fun ω ↦ thresholdCount p (U 0 ω); μ].toNNReal) ν) :
    TendstoInDistribution (fun (n : ℕ) ω ↦
      (((Finset.univ.filter (fun i ↦ pooledSample U (n+1) ω i ≤ t n)).card : ℝ) -
        (((n+1)*m : ℕ) : ℝ)*t n)/√(((n+1)*m : ℕ) : ℝ)) atTop
      (fun ω ↦ (√(m : ℝ))⁻¹*Z ω) (fun _ ↦ μ) ν := by
  have hc := iid_vector_moving_count_interior_clt U hU hindep hident hunif p hp
    (fun n ↦ t (n-1)) (htp.comp (tendsto_sub_atTop_nat 1)) Z hZ
  have hr := distribution_limit_succ _ _ hc
  simpa only [Nat.add_sub_cancel, Fintype.card_fin, pooledSample_count, Nat.cast_mul,
    div_eq_mul_inv, mul_comm] using hr

end Exceedance
#print axioms Exceedance.pooledSample_count
#print axioms Exceedance.distribution_limit_eventually_eq
#print axioms Exceedance.distribution_limit_succ

#print axioms Exceedance.iid_vector_moving_count_interior_clt
#print axioms Exceedance.iid_pooled_moving_count_clt
