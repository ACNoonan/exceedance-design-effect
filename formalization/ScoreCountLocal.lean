import BahadurInversion

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma thresholdCount_cdf_mean (U : Ω → ι → ℝ) (hU : Measurable U) (t : ℝ)
    (F : ℝ → ℝ) (hmarg : ∀ i, μ.real {ω | U ω i ≤ t} = F t) :
    (∫ ω, thresholdCount t (U ω) ∂μ) = (Fintype.card ι : ℝ)*F t := by
  rw [thresholdCount_comp]
  have hA (i : ι) : MeasurableSet {ω | U ω i ≤ t} :=
    measurableSet_le ((measurable_pi_apply i).comp hU) measurable_const
  rw [integral_finsetSum _ (fun i _ ↦ (indicator_memLp (hA i)).integrable (by norm_num))]
  simp only [indicator_mean (hA _), hmarg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [Fintype ι] in
lemma cdf_interval_probability (U : Ω → ι → ℝ) (hU : Measurable U)
    (F : ℝ → ℝ) (hF : Monotone F)
    (hunif : ∀ i t, μ.real {ω | U ω i ≤ t} = F t)
    (i : ι) (a b : ℝ) (hab : a ≤ b) :
    μ.real {ω | a < U ω i ∧ U ω i ≤ b} = F b-F a := by
  have he : {ω | a < U ω i ∧ U ω i ≤ b} =
      {ω | U ω i ≤ b} \ {ω | U ω i ≤ a} := by
    ext ω
    simp only [Set.mem_sdiff, mem_setOf_eq, not_le]
    exact and_comm
  have hsub : {ω | U ω i ≤ a} ⊆ {ω | U ω i ≤ b} := fun _ h ↦ le_trans h hab
  have hm : MeasurableSet {ω | U ω i ≤ a} :=
    measurableSet_le ((measurable_pi_apply i).comp hU) measurable_const
  rw [he, measureReal_sdiff (μ := μ) hsub hm, hunif i b, hunif i a]

/-- Both signs of a moving threshold have the same local variance bound. -/
theorem thresholdCount_cdf_increment_variance (U : Ω → ι → ℝ) (hU : Measurable U)
    (F : ℝ → ℝ) (hF : Monotone F)
    (hunif : ∀ i t, μ.real {ω | U ω i ≤ t} = F t)
    (a b : ℝ) :
    Var[fun ω ↦ thresholdCount b (U ω)-thresholdCount a (U ω); μ] ≤
      (Fintype.card ι : ℝ)^2 * |F b-F a| := by
  have hpos (c d : ℝ) (hcd : c ≤ d) :
      Var[fun ω ↦ thresholdCount d (U ω)-thresholdCount c (U ω); μ] ≤
        (Fintype.card ι : ℝ)^2*(F d-F c) := by
    rw [thresholdCount_sub_of_le U c d hcd]
    apply cluster_increment_variance_bound
    · intro i
      exact (measurableSet_lt measurable_const ((measurable_pi_apply i).comp hU)).inter
        (measurableSet_le ((measurable_pi_apply i).comp hU) measurable_const)
    · intro i
      exact cdf_interval_probability U hU F hF hunif i c d hcd
  by_cases hab : a ≤ b
  · rw [abs_of_nonneg (sub_nonneg.2 (hF hab))]
    exact hpos a b hab
  · have hba : b ≤ a := le_of_not_ge hab
    have he : (fun ω ↦ thresholdCount b (U ω)-thresholdCount a (U ω)) =
        (fun ω ↦ -(thresholdCount a (U ω)-thresholdCount b (U ω))) := by
      funext ω
      ring
    rw [he, variance_fun_neg, abs_of_nonpos (sub_nonpos.2 (hF hba)), neg_sub]
    exact hpos b a hba

/-- Independence of score vectors gives independence of their count increments. -/
theorem independent_threshold_cdf_increment_variance
    (U : ℕ → Ω → ι → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ)
    (F : ℝ → ℝ) (hF : Monotone F)
    (hunif : ∀ j i t, μ.real {ω | U j ω i ≤ t} = F t)
    (n : ℕ) (a b : ℝ) :
    Var[fun ω ↦ ∑ j ∈ Finset.range n,
      (thresholdCount b (U j ω)-thresholdCount a (U j ω)); μ] ≤
      (n : ℝ)*(Fintype.card ι : ℝ)^2*|F b-F a| := by
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
    _ ≤ ∑ _j ∈ Finset.range n, (Fintype.card ι : ℝ)^2*|F b-F a| := by
      exact Finset.sum_le_sum (fun j _ ↦ thresholdCount_cdf_increment_variance
        (U j) (hU j) F hF (hunif j) a b)
    _ = _ := by simp; ring


lemma normalizedCount_cdf_mean (U : ℕ → Ω → ι → ℝ) (hU : ∀ j, Measurable (U j))
    (n : ℕ) (t : ℝ) (F : ℝ → ℝ) (hunif : ∀ j i, μ.real {ω | U j ω i ≤ t} = F t) :
    (∫ ω, normalizedCount U n t ω ∂μ) = (√n)⁻¹ * n * (Fintype.card ι : ℝ)*F t := by
  unfold normalizedCount
  rw [integral_const_mul, integral_finsetSum _
    (fun j _ ↦ (thresholdCount_memLp (U j) (hU j) t).integrable (by norm_num))]
  simp_rw [thresholdCount_cdf_mean _ (hU _) t F (hunif _)]
  simp
  ring

/-- The normalized difference of actual threshold counts has vanishing variance. -/
theorem normalizedCount_cdf_increment_variance
    (U : ℕ → Ω → ι → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ)
    (F : ℝ → ℝ) (hF : Monotone F)
    (hunif : ∀ j i t, μ.real {ω | U j ω i ≤ t} = F t)
    (n : ℕ) (a b : ℝ) :
    Var[fun ω ↦ normalizedCount U n b ω-normalizedCount U n a ω; μ] ≤
      (Fintype.card ι : ℝ)^2*|F b-F a| := by
  have he : (fun ω ↦ normalizedCount U n b ω-normalizedCount U n a ω) =
      (fun ω ↦ (√n)⁻¹ * ∑ j ∈ Finset.range n,
        (thresholdCount b (U j ω)-thresholdCount a (U j ω))) := by
    funext ω
    simp only [normalizedCount, Finset.sum_sub_distrib, mul_sub]
  rw [he, variance_const_mul]
  have hv := independent_threshold_cdf_increment_variance U hU hindep F hF hunif n a b
  by_cases hn : n = 0
  · subst n
    simp
    positivity
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    calc
      _ ≤ (√n)⁻¹ ^ 2 * ((n : ℝ)*(Fintype.card ι : ℝ)^2*|F b-F a|) :=
        mul_le_mul_of_nonneg_left hv (sq_nonneg _)
      _ = _ := by
        rw [inv_pow, Real.sq_sqrt (by positivity)]
        field_simp



/-- Fixed-count fluctuations remain bounded in variance under independent clusters. -/
theorem normalizedCount_variance_bound
    (U : ℕ → Ω → ι → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ) (n : ℕ) (t : ℝ) :
    Var[normalizedCount U n t; μ] ≤ (Fintype.card ι : ℝ)^2 := by
  classical
  have hi := hindep.comp (fun _ ↦ thresholdCount (ι := ι) t)
    (fun _ ↦ measurable_thresholdCount t)
  have hv (j : ℕ) : Var[fun ω ↦ thresholdCount t (U j ω); μ] ≤ (Fintype.card ι : ℝ)^2 := by
    have hh := variance_le_sq_of_bounded (μ := μ)
      (Eventually.of_forall (fun ω ↦ thresholdCount_bounds (U j ω) t))
      ((measurable_thresholdCount t).comp (hU j)).aemeasurable
    simp only [sub_zero] at hh
    nlinarith [sq_nonneg (Fintype.card ι : ℝ)]
  have he : (fun ω ↦ ∑ j ∈ Finset.range n, thresholdCount t (U j ω)) =
      ∑ j ∈ Finset.range n, (fun ω ↦ thresholdCount t (U j ω)) := by
    funext ω; simp only [Finset.sum_apply]
  unfold normalizedCount
  rw [variance_const_mul,he,IndepFun.variance_sum
    (fun j _ ↦ thresholdCount_memLp (U j) (hU j) t) (fun j _ k _ hjk ↦ hi.indepFun hjk)]
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range n) ↦ hv j)
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  by_cases hn : n=0
  · subst n; simp
  · calc
      _ ≤ (√n)⁻¹^2*((n:ℝ)*(Fintype.card ι : ℝ)^2) := mul_le_mul_of_nonneg_left hh (sq_nonneg _)
      _ = _ := by
        rw [inv_pow,Real.sq_sqrt (by positivity)]
        have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn
        field_simp

/-- Local centered score-count increments vanish under a common CDF continuous at the target. -/
theorem local_score_count_centered
    (U : ℕ → Ω → ι → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ) (F : ℝ → ℝ) (hF : Monotone F)
    (hmarg : ∀ j i t, μ.real {ω | U j ω i ≤ t} = F t)
    (q : ℝ) (hcont : ContinuousAt F q) (t : ℕ → ℝ) (ht : Tendsto t atTop (nhds q)) :
    TendstoInMeasure μ (fun n ω ↦
      (normalizedCount U (n+1) (t n) ω-normalizedCount U (n+1) q ω)-
        ((√((n+1:ℕ):ℝ))⁻¹*(n+1)*(Fintype.card ι : ℝ)*(F (t n)-F q)))
      atTop (fun _ ↦ 0) := by
  let X := fun n ω ↦ normalizedCount U (n+1) (t n) ω-normalizedCount U (n+1) q ω
  have hX n : MemLp (X n) 2 μ :=
    (normalizedCount_memLp U hU (n+1) (t n)).sub (normalizedCount_memLp U hU (n+1) q)
  have hh := centered_tendstoInMeasure_of_variance_bound X hX
    (fun n ↦ (Fintype.card ι : ℝ)^2*|F (t n)-F q|)
    (fun n ↦ normalizedCount_cdf_increment_variance U hU hindep F hF hmarg (n+1) q (t n))
    (by simpa using ((hcont.tendsto.comp ht).sub_const (F q)).abs.const_mul ((Fintype.card ι : ℝ)^2))
  have he n : (∫ ω, X n ω ∂μ) =
      (√((n+1:ℕ):ℝ))⁻¹*(n+1)*(Fintype.card ι : ℝ)*(F (t n)-F q) := by
    dsimp [X]
    rw [integral_sub ((normalizedCount_memLp U hU (n+1) (t n)).integrable (by norm_num))
      ((normalizedCount_memLp U hU (n+1) q).integrable (by norm_num)),
      normalizedCount_cdf_mean U hU (n+1) (t n) F (fun j i ↦ hmarg j i (t n)),
      normalizedCount_cdf_mean U hU (n+1) q F (fun j i ↦ hmarg j i q)]
    push_cast; ring
  convert hh using 1
  funext n ω
  rw [he]
  rfl

end Exceedance
#print axioms Exceedance.independent_threshold_cdf_increment_variance
