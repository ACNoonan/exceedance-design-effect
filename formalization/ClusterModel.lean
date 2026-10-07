import IndicatorVariance
import ProbabilityTransform
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def thresholdCount (t : ℝ) (u : ι → ℝ) : ℝ :=
  ∑ i, indicator {v : ι → ℝ | v i ≤ t} u

omit [MeasurableSpace Ω] in
lemma thresholdCount_comp (U : Ω → ι → ℝ) (t : ℝ) :
    (fun ω ↦ thresholdCount t (U ω)) =
      (fun ω ↦ ∑ i, indicator {ω | U ω i ≤ t} ω) := by
  classical
  funext ω
  simp only [thresholdCount, indicator, Set.indicator, mem_setOf_eq]

lemma measurable_thresholdCount (t : ℝ) : Measurable (thresholdCount (ι := ι) t) := by
  classical
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.indicator (measurableSet_le (measurable_pi_apply i) measurable_const)

lemma thresholdCount_memLp (U : Ω → ι → ℝ) (hU : Measurable U) (t : ℝ) :
    MemLp (fun ω ↦ thresholdCount t (U ω)) 2 μ := by
  rw [thresholdCount_comp]
  exact memLp_finsetSum _ (fun i _ ↦ indicator_memLp
    (measurableSet_le ((measurable_pi_apply i).comp hU) measurable_const))

lemma thresholdCount_mean (U : Ω → ι → ℝ) (hU : Measurable U) (t : ℝ)
    (hmarg : ∀ i, μ.real {ω | U ω i ≤ t} = t) :
    (∫ ω, thresholdCount t (U ω) ∂μ) = (Fintype.card ι : ℝ)*t := by
  rw [thresholdCount_comp]
  have hA (i : ι) : MeasurableSet {ω | U ω i ≤ t} :=
    measurableSet_le ((measurable_pi_apply i).comp hU) measurable_const
  rw [integral_finsetSum _ (fun i _ ↦ (indicator_memLp (hA i)).integrable (by norm_num))]
  simp only [indicator_mean (hA _), hmarg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [MeasurableSpace Ω] in
/-- Nested threshold counts differ by the count in the intervening interval. -/
lemma thresholdCount_sub_of_le (U : Ω → ι → ℝ) (a b : ℝ) (hab : a ≤ b) :
    (fun ω ↦ thresholdCount b (U ω)-thresholdCount a (U ω)) =
      (fun ω ↦ ∑ i, indicator {ω | a < U ω i ∧ U ω i ≤ b} ω) := by
  classical
  funext ω
  simp only [thresholdCount, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [indicator, Set.indicator, mem_setOf_eq]
  split_ifs <;> simp_all <;> linarith

omit [Fintype ι] in
lemma uniform_interval_probability (U : Ω → ι → ℝ) (hU : Measurable U)
    (hunif : ∀ i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U ω i ≤ t} = t)
    (i : ι) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    μ.real {ω | a < U ω i ∧ U ω i ≤ b} = b-a := by
  have he : {ω | a < U ω i ∧ U ω i ≤ b} =
      {ω | U ω i ≤ b} \ {ω | U ω i ≤ a} := by
    ext ω
    simp only [Set.mem_sdiff, mem_setOf_eq, not_le]
    exact and_comm
  have hsub : {ω | U ω i ≤ a} ⊆ {ω | U ω i ≤ b} := fun _ h ↦ le_trans h hab
  have hm : MeasurableSet {ω | U ω i ≤ a} :=
    measurableSet_le ((measurable_pi_apply i).comp hU) measurable_const
  rw [he, measureReal_sdiff (μ := μ) hsub hm, hunif i b (ha.trans hab) hb,
    hunif i a ha (hab.trans hb)]

/-- Both signs of a moving threshold have the same local variance bound. -/
theorem thresholdCount_increment_variance (U : Ω → ι → ℝ) (hU : Measurable U)
    (hunif : ∀ i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U ω i ≤ t} = t)
    (a b : ℝ) (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    Var[fun ω ↦ thresholdCount b (U ω)-thresholdCount a (U ω); μ] ≤
      (Fintype.card ι : ℝ)^2 * |b-a| := by
  have hpos (c d : ℝ) (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
      Var[fun ω ↦ thresholdCount d (U ω)-thresholdCount c (U ω); μ] ≤
        (Fintype.card ι : ℝ)^2*(d-c) := by
    rw [thresholdCount_sub_of_le U c d hcd]
    apply cluster_increment_variance_bound
    · intro i
      exact (measurableSet_lt measurable_const ((measurable_pi_apply i).comp hU)).inter
        (measurableSet_le ((measurable_pi_apply i).comp hU) measurable_const)
    · intro i
      exact uniform_interval_probability U hU hunif i c d hc hcd hd
  by_cases hab : a ≤ b
  · rw [abs_of_nonneg (sub_nonneg.2 hab)]
    exact hpos a b ha.1 hab hb.2
  · have hba : b ≤ a := le_of_not_ge hab
    have he : (fun ω ↦ thresholdCount b (U ω)-thresholdCount a (U ω)) =
        (fun ω ↦ -(thresholdCount a (U ω)-thresholdCount b (U ω))) := by
      funext ω
      ring
    rw [he, variance_fun_neg, abs_of_nonpos (sub_nonpos.2 hba), neg_sub]
    exact hpos b a hb.1 hba ha.2

/-- Independence of score vectors gives independence of their count increments. -/
theorem independent_threshold_increment_variance
    (U : ℕ → Ω → ι → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (n : ℕ) (a b : ℝ) (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    Var[fun ω ↦ ∑ j ∈ Finset.range n,
      (thresholdCount b (U j ω)-thresholdCount a (U j ω)); μ] ≤
      (n : ℝ)*(Fintype.card ι : ℝ)^2*|b-a| := by
  classical
  have hi : iIndepFun (fun j ω ↦ thresholdCount b (U j ω)-thresholdCount a (U j ω)) μ :=
    hindep.comp (fun _ u ↦ thresholdCount b u-thresholdCount a u)
      (fun _ ↦ (measurable_thresholdCount b).sub (measurable_thresholdCount a))
  have hl (j : ℕ) : MemLp (fun ω ↦ thresholdCount b (U j ω)-thresholdCount a (U j ω)) 2 μ :=
    (thresholdCount_memLp (U j) (hU j) b).sub (thresholdCount_memLp (U j) (hU j) a)
  have he : (fun ω ↦ ∑ j ∈ Finset.range n,
      (thresholdCount b (U j ω)-thresholdCount a (U j ω))) =
      ∑ j ∈ Finset.range n, (fun ω ↦ thresholdCount b (U j ω)-thresholdCount a (U j ω)) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [he, IndepFun.variance_sum (fun j _ ↦ hl j) (fun j _ k _ hjk ↦ hi.indepFun hjk)]
  calc
    _ ≤ ∑ _j ∈ Finset.range n, (Fintype.card ι : ℝ)^2*|b-a| := by
      exact Finset.sum_le_sum (fun j _ ↦ thresholdCount_increment_variance
        (U j) (hU j) (hunif j) a b ha hb)
    _ = _ := by simp; ring

/-- Count CLT derived from iid score vectors on the same probability space. -/
theorem iid_vector_fixed_count_clt
    {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (U : ℕ → Ω → ι → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ) (hident : ∀ j, IdentDistrib (U j) (U 0) μ μ)
    (p : ℝ) (hunif : ∀ i, μ.real {ω | U 0 ω i ≤ p} = p)
    (Z : Ω' → ℝ)
    (hZ : HasLaw Z (gaussianReal 0 Var[fun ω ↦ thresholdCount p (U 0 ω); μ].toNNReal) ν) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ *
      ((∑ j ∈ Finset.range n, thresholdCount p (U j ω))-
        n*((Fintype.card ι : ℝ)*p))) atTop Z (fun _ ↦ μ) ν := by
  have hi : iIndepFun (fun j ω ↦ thresholdCount p (U j ω)) μ :=
    hindep.comp (fun _ ↦ thresholdCount p) (fun _ ↦ measurable_thresholdCount p)
  have hid (j : ℕ) : IdentDistrib (fun ω ↦ thresholdCount p (U j ω))
      (fun ω ↦ thresholdCount p (U 0 ω)) μ μ :=
    (hident j).comp (measurable_thresholdCount p)
  have ht := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun j ω ↦ thresholdCount p (U j ω)) (P := μ) (P' := ν) (Y := Z)
    hZ (thresholdCount_memLp (U 0) (hU 0) p) hi hid
  rw [thresholdCount_mean (U 0) (hU 0) p hunif] at ht
  exact ht

noncomputable def normalizedCount (U : ℕ → Ω → ι → ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  (√n)⁻¹ * ∑ j ∈ Finset.range n, thresholdCount t (U j ω)

lemma normalizedCount_memLp (U : ℕ → Ω → ι → ℝ) (hU : ∀ j, Measurable (U j))
    (n : ℕ) (t : ℝ) : MemLp (normalizedCount U n t) 2 μ := by
  exact (memLp_finsetSum _ (fun j _ ↦ thresholdCount_memLp (U j) (hU j) t)).const_mul _

lemma normalizedCount_mean (U : ℕ → Ω → ι → ℝ) (hU : ∀ j, Measurable (U j))
    (n : ℕ) (t : ℝ) (hunif : ∀ j i, μ.real {ω | U j ω i ≤ t} = t) :
    (∫ ω, normalizedCount U n t ω ∂μ) = (√n)⁻¹ * n * (Fintype.card ι : ℝ)*t := by
  unfold normalizedCount
  rw [integral_const_mul, integral_finsetSum _
    (fun j _ ↦ (thresholdCount_memLp (U j) (hU j) t).integrable (by norm_num))]
  simp_rw [thresholdCount_mean _ (hU _) t (hunif _)]
  simp
  ring

/-- The normalized difference of actual threshold counts has vanishing variance. -/
theorem normalizedCount_increment_variance
    (U : ℕ → Ω → ι → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (n : ℕ) (a b : ℝ) (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    Var[fun ω ↦ normalizedCount U n b ω-normalizedCount U n a ω; μ] ≤
      (Fintype.card ι : ℝ)^2*|b-a| := by
  have he : (fun ω ↦ normalizedCount U n b ω-normalizedCount U n a ω) =
      (fun ω ↦ (√n)⁻¹ * ∑ j ∈ Finset.range n,
        (thresholdCount b (U j ω)-thresholdCount a (U j ω))) := by
    funext ω
    simp only [normalizedCount, Finset.sum_sub_distrib, mul_sub]
  rw [he, variance_const_mul]
  have hv := independent_threshold_increment_variance U hU hindep hunif n a b ha hb
  by_cases hn : n = 0
  · subst n
    simp
    positivity
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    calc
      _ ≤ (√n)⁻¹ ^ 2 * ((n : ℝ)*(Fintype.card ι : ℝ)^2*|b-a|) :=
        mul_le_mul_of_nonneg_left hv (sq_nonneg _)
      _ = _ := by
        rw [inv_pow, Real.sq_sqrt (by positivity)]
        field_simp

/-- The moving-threshold count CLT, derived from iid uniform-marginal score vectors.
    No moving-count limit is assumed. Within-cluster dependence is unrestricted. -/
theorem iid_vector_moving_count_clt
    {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (U : ℕ → Ω → ι → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ) (hident : ∀ j, IdentDistrib (U j) (U 0) μ μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (p : ℝ) (hp : p ∈ Icc 0 1) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ Icc 0 1) (htp : Tendsto t atTop (nhds p))
    (Z : Ω' → ℝ)
    (hZ : HasLaw Z (gaussianReal 0 Var[fun ω ↦ thresholdCount p (U 0 ω); μ].toNNReal) ν) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ *
      ((∑ j ∈ Finset.range n, thresholdCount (t n) (U j ω))-
        n*((Fintype.card ι : ℝ)*t n))) atTop Z (fun _ ↦ μ) ν := by
  let X : ℕ → Ω → ℝ := fun n ω ↦ (√n)⁻¹ *
    ((∑ j ∈ Finset.range n, thresholdCount p (U j ω))-n*((Fintype.card ι : ℝ)*p))
  let Y : ℕ → Ω → ℝ := fun n ω ↦ (√n)⁻¹ *
    ((∑ j ∈ Finset.range n, thresholdCount (t n) (U j ω))-n*((Fintype.card ι : ℝ)*t n))
  let G : ℕ → Ω → ℝ := fun n ω ↦ normalizedCount U n (t n) ω-normalizedCount U n p ω
  have hLp (n : ℕ) : MemLp (G n) 2 μ :=
    (normalizedCount_memLp U hU n (t n)).sub (normalizedCount_memLp U hU n p)
  have hv (n : ℕ) : Var[G n; μ] ≤ (Fintype.card ι : ℝ)^2*|t n-p| :=
    normalizedCount_increment_variance U hU hindep hunif n p (t n) hp (ht n)
  have hv0 : Tendsto (fun n ↦ (Fintype.card ι : ℝ)^2*|t n-p|) atTop (nhds 0) := by
    simpa using ((htp.sub_const p).abs).const_mul ((Fintype.card ι : ℝ)^2)
  have hg := centered_tendstoInMeasure_of_variance_bound G hLp _ hv hv0
  have hmean (n : ℕ) : (∫ ω, G n ω ∂μ) =
      (√n)⁻¹*n*(Fintype.card ι : ℝ)*t n-(√n)⁻¹*n*(Fintype.card ι : ℝ)*p := by
    dsimp [G]
    rw [integral_sub ((normalizedCount_memLp U hU n (t n)).integrable (by norm_num))
      ((normalizedCount_memLp U hU n p).integrable (by norm_num)),
      normalizedCount_mean U hU n (t n) (fun j i ↦ hunif j i (t n) (ht n).1 (ht n).2),
      normalizedCount_mean U hU n p (fun j i ↦ hunif j i p hp.1 hp.2)]
  have he : (fun n ω ↦ G n ω-(∫ ω, G n ω ∂μ)) = Y-X := by
    funext n ω
    rw [hmean]
    dsimp [G, X, Y, normalizedCount]
    ring
  rw [he] at hg
  apply tendstoInDistribution_of_tendstoInMeasure_sub Y Z
    (iid_vector_fixed_count_clt U hU hindep hident p (fun i ↦ hunif 0 i p hp.1 hp.2) Z hZ) hg
  intro n
  exact (((memLp_finsetSum _ (fun j _ ↦ thresholdCount_memLp (U j) (hU j) (t n))).sub
    (memLp_const _)).const_mul _).aemeasurable

/-- The moving-count limit for scores with a common continuous marginal CDF.
    The probability transform and preservation of iid clusters are proved here. -/
theorem iid_score_moving_count_clt
    {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (S : ℕ → Ω → ι → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (hident : ∀ j, IdentDistrib (S j) (S 0) μ μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i x, μ.real {ω | S j ω i ≤ x} = F x)
    (p : ℝ) (hp : p ∈ Icc 0 1) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ Icc 0 1) (htp : Tendsto t atTop (nhds p))
    (Z : Ω' → ℝ)
    (hZ : HasLaw Z (gaussianReal 0
      Var[fun ω ↦ thresholdCount p (fun i ↦ F (S 0 ω i)); μ].toNNReal) ν) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ *
      ((∑ j ∈ Finset.range n, thresholdCount (t n) (fun i ↦ F (S j ω i)))-
        n*((Fintype.card ι : ℝ)*t n))) atTop Z (fun _ ↦ μ) ν := by
  let T : (ι → ℝ) → (ι → ℝ) := fun u i ↦ F (u i)
  have hT : Measurable T :=
    measurable_pi_lambda _ (fun i ↦ hF.measurable.comp (measurable_pi_apply i))
  apply iid_vector_moving_count_clt (fun j ω i ↦ F (S j ω i))
    (fun j ↦ hT.comp (hS j)) (hindep.comp (fun _ ↦ T) (fun _ ↦ hT))
    (fun j ↦ (hident j).comp hT) _ p hp t ht htp Z hZ
  intro j i u hu0 hu1
  exact continuous_cdf_transform (fun ω ↦ S j ω i) F hF hmono h0 h1 (hCDF j i) u hu0 hu1

/-- Normalize by the number of individual observations, not by the number of clusters. -/
theorem iid_vector_moving_count_total_scale_clt
    {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (U : ℕ → Ω → ι → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ) (hident : ∀ j, IdentDistrib (U j) (U 0) μ μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (p : ℝ) (hp : p ∈ Icc 0 1) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ Icc 0 1) (htp : Tendsto t atTop (nhds p))
    (Z : Ω' → ℝ)
    (hZ : HasLaw Z (gaussianReal 0 Var[fun ω ↦ thresholdCount p (U 0 ω); μ].toNNReal) ν) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√((n : ℝ)*Fintype.card ι))⁻¹ *
      ((∑ j ∈ Finset.range n, thresholdCount (t n) (U j ω))-
        ((n : ℝ)*Fintype.card ι)*t n)) atTop
      (fun ω ↦ (√(Fintype.card ι : ℝ))⁻¹*Z ω) (fun _ ↦ μ) ν := by
  have hc := iid_vector_moving_count_clt U hU hindep hident hunif p hp t ht htp Z hZ
  have hs := hc.continuous_comp (g := fun z : ℝ ↦ (√(Fintype.card ι : ℝ))⁻¹*z) (by fun_prop)
  have he (n : ℕ) (ω : Ω) :
      (√((n : ℝ)*Fintype.card ι))⁻¹ *
      ((∑ j ∈ Finset.range n, thresholdCount (t n) (U j ω))-((n : ℝ)*Fintype.card ι)*t n) =
      (√(Fintype.card ι : ℝ))⁻¹*((√n)⁻¹ *
      ((∑ j ∈ Finset.range n, thresholdCount (t n) (U j ω))-n*((Fintype.card ι : ℝ)*t n))) := by
    rw [Real.sqrt_mul (by positivity), mul_inv_rev]
    ring
  simpa only [he, Function.comp_def] using hs

end Exceedance
#print axioms Exceedance.thresholdCount_increment_variance

#print axioms Exceedance.independent_threshold_increment_variance
#print axioms Exceedance.iid_vector_fixed_count_clt

#print axioms Exceedance.normalizedCount_increment_variance
#print axioms Exceedance.iid_vector_moving_count_clt

#print axioms Exceedance.iid_score_moving_count_clt
#print axioms Exceedance.iid_vector_moving_count_total_scale_clt
