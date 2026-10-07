import RandomCutoff
import CoverageMoments
import Mathlib.Probability.StrongLaw

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma thresholdCount_monotone {m : ℕ} (u : Fin m → ℝ) : Monotone (fun t ↦ thresholdCount t u) := by
  classical
  intro a b hab
  apply Finset.sum_le_sum
  intro i _
  simp only [indicator, Set.indicator, mem_setOf_eq]
  split_ifs <;> norm_num
  all_goals linarith

lemma thresholdCount_continuousAt {m : ℕ} (u : Fin m → ℝ) (p : ℝ)
    (hp : ∀ i, u i ≠ p) : ContinuousAt (fun t ↦ thresholdCount t u) p := by
  have he : ∀ᶠ t in nhds p, ∀ i, (u i ≤ t ↔ u i ≤ p) := by
    apply eventually_all.mpr
    intro i
    rcases lt_or_gt_of_ne (hp i) with hi | hi
    · filter_upwards [eventually_gt_nhds hi] with t ht
      exact iff_of_true ht.le hi.le
    · filter_upwards [eventually_lt_nhds hi] with t ht
      exact iff_of_false (not_le.mpr ht) (not_le.mpr hi)
  apply (show ContinuousAt (fun _ : ℝ ↦ thresholdCount p u) p from continuousAt_const).congr_of_eventuallyEq
  filter_upwards [he] with t ht
  classical
  simp only [thresholdCount, indicator, Set.indicator, mem_setOf_eq, ht]

lemma thresholdCount_power_integrable {m : ℕ} (U : Ω → Fin m → ℝ)
    (hU : Measurable U) (t : ℝ) (r : ℕ) :
    Integrable (fun ω ↦ (thresholdCount t (U ω))^r) μ := by
  apply Integrable.of_bound ((measurable_thresholdCount t).comp hU |>.pow_const r).aestronglyMeasurable
    ((m : ℝ)^r)
  filter_upwards with ω
  have hb := thresholdCount_bounds (U ω) t
  simp only [Fintype.card_fin] at hb
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hb.1 _)]
  exact pow_le_pow_left₀ hb.1 hb.2 _

lemma thresholdCount_moment_continuousAt {m : ℕ} (U : Ω → Fin m → ℝ)
    (hU : Measurable U) (p : ℝ)
    (ha : ∀ i, μ {ω | U ω i = p} = 0) (r : ℕ) :
    ContinuousAt (fun t ↦ ∫ ω, (thresholdCount t (U ω))^r ∂μ) p := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (m : ℝ)^r)
  · exact Eventually.of_forall (fun t ↦ ((measurable_thresholdCount t).comp hU |>.pow_const r).aestronglyMeasurable)
  · apply Eventually.of_forall
    intro t
    filter_upwards with ω
    have hb := thresholdCount_bounds (U ω) t
    simp only [Fintype.card_fin] at hb
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hb.1 _)]
    exact pow_le_pow_left₀ hb.1 hb.2 _
  · exact integrable_const _
  · have he : ∀ᵐ ω ∂μ, ∀ i, U ω i ≠ p := by
      rw [ae_all_iff]
      intro i
      simpa only [ae_iff, not_not] using ha i
    filter_upwards [he] with ω hω
    exact (thresholdCount_continuousAt (U ω) p hω).pow r

/-- Empirical count moments evaluated at an arbitrary fitted consistent cutoff. -/
theorem iid_count_moment_random_cutoff {m : ℕ}
    (U : ℕ → Ω → Fin m → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ) (hident : ∀ j, IdentDistrib (U j) (U 0) μ μ)
    (p : ℝ) (ha : ∀ i, μ {ω | U 0 ω i = p} = 0)
    (C : ℕ → Ω → ℝ) (hC : TendstoInMeasure μ C atTop (fun _ ↦ p)) (r : ℕ) :
    TendstoInMeasure μ
      (fun n ω ↦ (∑ j ∈ Finset.range (n+1), (thresholdCount (C n ω) (U j ω))^r)/(n+1 : ℝ))
      atTop (fun _ ↦ ∫ ω, (thresholdCount p (U 0 ω))^r ∂μ) := by
  apply monotone_random_cutoff_consistency
    (fun n t ω ↦ (∑ j ∈ Finset.range (n+1), (thresholdCount t (U j ω))^r)/(n+1 : ℝ)) C
    (fun t ↦ ∫ ω, (thresholdCount t (U 0 ω))^r ∂μ) p
  · intro n ω a b hab
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro j _
    exact pow_le_pow_left₀ (thresholdCount_bounds (U j ω) a).1
      (thresholdCount_monotone (U j ω) hab) r
  · exact thresholdCount_moment_continuousAt (U 0) (hU 0) p ha r
  · intro t
    let f := fun u : Fin m → ℝ ↦ (thresholdCount t u)^r
    have hf : Measurable f := (measurable_thresholdCount t).pow_const r
    have hi := hindep.comp (fun _ ↦ f) (fun _ ↦ hf)
    have hid := fun j ↦ (hident j).comp hf
    have hs := strong_law_ae_real (fun j ω ↦ f (U j ω))
      (thresholdCount_power_integrable (U 0) (hU 0) t r) (fun i j hij ↦ hi.indepFun hij) hid
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact ((Finset.measurable_sum _ (fun j _ ↦ hf.comp (hU j))).div_const _).aestronglyMeasurable
    · filter_upwards [hs] with ω hω
      simpa only [Function.comp_def, f, Nat.cast_add, Nat.cast_one] using hω.comp (tendsto_add_atTop_nat 1)
  · exact hC

/-- The pooled quantile is consistent without a central-limit assumption. -/
theorem pooled_quantile_consistent {m : ℕ} (hm : 0 < m)
    (U : ℕ → Ω → Fin m → ℝ) (hU : ∀ j, Measurable (U j)) (hindep : iIndepFun U μ)
    (hu : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (k : ∀ n, Fin ((n+1)*m)) (p : ℝ)
    (hkp : Tendsto (fun n ↦ (((k n).val+1 : ℕ) : ℝ)/(((n+1)*m : ℕ)+1)) atTop (nhds p)) :
    TendstoInMeasure μ (fun n ω ↦ sampleQuantile (pooledSample U (n+1) ω) (k n))
      atTop (fun _ ↦ p) := by
  let q := fun n ω ↦ sampleQuantile (pooledSample U (n+1) ω) (k n)
  let pn := fun n ↦ (((k n).val+1 : ℕ) : ℝ)/(((n+1)*m : ℕ)+1)
  have herr : TendstoInMeasure μ (fun n ω ↦ q n ω-pn n) atTop (fun _ ↦ (0:ℝ)) := by
    rw [tendstoInMeasure_iff_measureReal_norm]
    intro e he
    have hb : Tendsto (fun n : ℕ ↦ (2:ℝ)*Real.exp ((-2*(e/2)^2)*(n+1))) atTop (nhds 0) := by
      have hn : Tendsto (fun n : ℕ ↦ (n:ℝ)+1) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      have hh := Real.tendsto_exp_atBot.comp
        (tendsto_const_nhds.neg_mul_atTop (by nlinarith [sq_pos_of_pos he] : -2*(e/2)^2 < 0) hn)
      simpa using hh.const_mul 2
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    · intro n; exact measureReal_nonneg
    · intro n
      have ht := pooled_quantile_tail U hU hindep hu (n+1) (k n) (e/2) (by positivity)
      have hs : {ω | e ≤ ‖q n ω-pn n-0‖} ⊆ {ω | e/2 < |q n ω-pn n|} := by
        intro ω hω
        simp only [mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω ⊢
        linarith
      have hh := (measureReal_mono (μ := μ) hs).trans ht
      convert hh using 1
      push_cast
      have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
      have hn' : (n:ℝ)+1 ≠ 0 := by positivity
      field_simp
  have hpn : TendstoInMeasure μ (fun n (_ : Ω) ↦ pn n) atTop (fun _ ↦ p) :=
    tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const) (Eventually.of_forall (fun _ ↦ hkp))
  have hh := continuous_pair_tendstoInMeasure (fun n ω ↦ q n ω-pn n) (fun n _ ↦ pn n)
    0 p herr hpn (fun z ↦ z.1+z.2) (by fun_prop)
  simpa only [sub_add_cancel, zero_add] using hh

/-- The empirical variance of cluster counts, divided by cluster size. -/
noncomputable def clusterVarianceEstimator {m : ℕ} (U : ℕ → Ω → Fin m → ℝ)
    (C : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  let mean := (∑ j ∈ Finset.range (n+1), thresholdCount (C n ω) (U j ω))/(n+1 : ℝ)
  let second := (∑ j ∈ Finset.range (n+1), (thresholdCount (C n ω) (U j ω))^2)/(n+1 : ℝ)
  ((n+1 : ℝ)/n)*(second-mean^2)/m

/-- The sample variance is consistent at a cutoff fitted on the same iid clusters. -/
theorem iid_clusterVarianceEstimator_consistent {m : ℕ}
    (U : ℕ → Ω → Fin m → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ) (hident : ∀ j, IdentDistrib (U j) (U 0) μ μ)
    (p : ℝ) (ha : ∀ i, μ {ω | U 0 ω i = p} = 0)
    (C : ℕ → Ω → ℝ) (hC : TendstoInMeasure μ C atTop (fun _ ↦ p)) :
    TendstoInMeasure μ (clusterVarianceEstimator U C) atTop
      (fun _ ↦ Var[fun ω ↦ thresholdCount p (U 0 ω); μ]/m) := by
  have hfirst := iid_count_moment_random_cutoff U hU hindep hident p ha C hC 1
  simp only [pow_one] at hfirst
  have hsecond := iid_count_moment_random_cutoff U hU hindep hident p ha C hC 2
  have hv := continuous_pair_tendstoInMeasure _ _ _ _ hfirst hsecond
    (fun z ↦ z.2-z.1^2) (by fun_prop)
  have hratio : Tendsto (fun n : ℕ ↦ (n+1 : ℝ)/n) atTop (nhds 1) := by
    have hh := (tendsto_const_nhds (x := (1:ℝ))).add (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
    have hh' : Tendsto (fun n : ℕ ↦ 1+(n:ℝ)⁻¹) atTop (nhds 1) := by simpa using hh
    apply hh'.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp
  have hr : TendstoInMeasure μ (fun (n : ℕ) (_ : Ω) ↦ (n+1 : ℝ)/n) atTop (fun _ ↦ (1:ℝ)) :=
    tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const) (Eventually.of_forall (fun _ ↦ hratio))
  have hh := continuous_pair_tendstoInMeasure _ _ _ _ hr hv (fun z ↦ z.1*z.2/m) (by fun_prop)
  rw [variance_eq_sub (thresholdCount_memLp (U 0) (hU 0) p)]
  unfold clusterVarianceEstimator
  simpa only [one_mul, Pi.pow_apply] using hh

/-- Appendix B.10 on the uniform scale, with the actual pooled sample quantile. -/
theorem iid_pooled_quantile_estimator_consistent {m : ℕ} (hm : 0 < m)
    (U : ℕ → Ω → Fin m → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ) (hident : ∀ j, IdentDistrib (U j) (U 0) μ μ)
    (hu : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (k : ∀ n, Fin ((n+1)*m)) (p : ℝ)
    (hkp : Tendsto (fun n ↦ (((k n).val+1 : ℕ) : ℝ)/(((n+1)*m : ℕ)+1)) atTop (nhds p)) :
    TendstoInMeasure μ
      (clusterVarianceEstimator U (fun n ω ↦ sampleQuantile (pooledSample U (n+1) ω) (k n)))
      atTop (fun _ ↦ Var[fun ω ↦ thresholdCount p (U 0 ω); μ]/m) :=
  iid_clusterVarianceEstimator_consistent U hU hindep hident p
    (fun i ↦ uniform_marginal_no_atoms _ ((measurable_pi_apply i).comp (hU 0)) (hu 0 i) p) _
    (pooled_quantile_consistent hm U hU hindep hu k p hkp)

omit [MeasurableSpace Ω] in
/-- The moment formula is exactly the usual sample variance with divisor b-1. -/
theorem clusterVarianceEstimator_eq_sample_variance {m : ℕ} (hm : 0 < m)
    (U : ℕ → Ω → Fin m → ℝ) (C : ℕ → Ω → ℝ) (n : ℕ) (hn : 0 < n) (ω : Ω) :
    clusterVarianceEstimator U C n ω =
      (∑ j ∈ Finset.range (n+1), (thresholdCount (C n ω) (U j ω) -
        (∑ i ∈ Finset.range (n+1), thresholdCount (C n ω) (U i ω))/(n+1 : ℝ))^2)/(m*n : ℝ) := by
  unfold clusterVarianceEstimator
  dsimp only
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [← Finset.mul_sum]
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hb' : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

omit [IsProbabilityMeasure μ] in
/-- Atomless transformed scores preserve all threshold comparisons almost surely, even at fitted cutoffs. -/
lemma monotone_transform_threshold_ae (X : Ω → ℝ) (F : ℝ → ℝ) (hmono : Monotone F)
    (ha : ∀ a, μ {ω | F (X ω) = a} = 0) :
    ∀ᵐ ω ∂μ, ∀ t, (F (X ω) ≤ F t ↔ X ω ≤ t) := by
  have he : ∀ᵐ ω ∂μ, ∀ q : ℚ, F (X ω) ≠ F q := by
    rw [ae_all_iff]
    intro q
    simpa only [ae_iff, not_not] using ha (F q)
  filter_upwards [he] with ω hω
  intro t
  constructor
  · intro h
    by_contra hn
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (not_le.mp hn)
    have hq := hmono hq2.le
    have ht := hmono hq1.le
    exact hω q (by linarith)
  · intro h; exact hmono h

/-- Appendix B.10 for the original scores and the actual fitted sample quantile. -/
theorem iid_continuous_score_estimator_consistent {m : ℕ} (hm : 0 < m)
    (S : ℕ → Ω → Fin m → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (hident : ∀ j, IdentDistrib (S j) (S 0) μ μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i t, μ.real {ω | S j ω i ≤ t} = F t)
    (k : ∀ n, Fin ((n+1)*m)) (p : ℝ)
    (hkp : Tendsto (fun n ↦ (((k n).val+1 : ℕ) : ℝ)/(((n+1)*m : ℕ)+1)) atTop (nhds p)) :
    TendstoInMeasure μ
      (clusterVarianceEstimator S (fun n ω ↦ sampleQuantile (pooledSample S (n+1) ω) (k n)))
      atTop (fun _ ↦ Var[fun ω ↦ thresholdCount p (fun i ↦ F (S 0 ω i)); μ]/m) := by
  let T := fun u : Fin m → ℝ ↦ fun i ↦ F (u i)
  have hT : Measurable T := measurable_pi_lambda _ (fun i ↦ hF.measurable.comp (measurable_pi_apply i))
  let U := fun j ω i ↦ F (S j ω i)
  have hU (j : ℕ) : Measurable (U j) := hT.comp (hS j)
  have hu : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t := by
    intro j i t ht0 ht1
    exact continuous_cdf_transform (fun ω ↦ S j ω i) F hF hmono h0 h1 (hCDF j i) t ht0 ht1
  have hh := iid_pooled_quantile_estimator_consistent hm U hU
    (hindep.comp (fun _ ↦ T) (fun _ ↦ hT)) (fun j ↦ (hident j).comp hT) hu k p hkp
  apply hh.congr_left
  intro n
  have he : ∀ᵐ ω ∂μ, ∀ j i t, (F (S j ω i) ≤ F t ↔ S j ω i ≤ t) := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro i
    exact monotone_transform_threshold_ae (fun ω ↦ S j ω i) F hmono
      (uniform_marginal_no_atoms _ ((measurable_pi_apply i).comp (hU j)) (hu j i))
  filter_upwards [he] with ω hω
  have hq : sampleQuantile (pooledSample U (n+1) ω) (k n) =
      F (sampleQuantile (pooledSample S (n+1) ω) (k n)) :=
    sampleQuantile_monotone_map (pooledSample S (n+1) ω) (k n) F hmono
  have hc (j : ℕ) (t : ℝ) : thresholdCount (F t) (U j ω) = thresholdCount t (S j ω) := by
    classical
    simp only [thresholdCount, indicator, Set.indicator, mem_setOf_eq, U, hω]
  simp only [clusterVarianceEstimator, hq, hc]

/-- The exact eventual ceiling rule supplies the estimator's rank assumption. -/
theorem iid_continuous_score_ceil_estimator_consistent {m : ℕ} (hm : 0 < m)
    (S : ℕ → Ω → Fin m → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (hident : ∀ j, IdentDistrib (S j) (S 0) μ μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i t, μ.real {ω | S j ω i ≤ t} = F t)
    (k : ∀ n, Fin ((n+1)*m)) (p : ℝ) (hp : 0 ≤ p)
    (hceil : ∀ᶠ n in atTop, (k n).val+1 = Nat.ceil (((((n+1)*m : ℕ) : ℝ)+1)*p)) :
    TendstoInMeasure μ
      (clusterVarianceEstimator S (fun n ω ↦ sampleQuantile (pooledSample S (n+1) ω) (k n)))
      atTop (fun _ ↦ Var[fun ω ↦ thresholdCount p (fun i ↦ F (S 0 ω i)); μ]/m) := by
  have hN : Tendsto (fun n : ℕ ↦ (n+1)*m) atTop atTop := by
    apply tendsto_atTop_mono (fun n ↦ show n ≤ (n+1)*m from ?_) tendsto_id
    nlinarith
  exact iid_continuous_score_estimator_consistent hm S hS hindep hident F hF hmono h0 h1 hCDF k p
    (ceil_rank_levels_tendsto _ _ hN p hp hceil)

/-- Absolute and relative comparisons with a deterministic variance sequence. -/
theorem consistent_estimator_comparison (E : ℕ → Ω → ℝ) (V : ℕ → ℝ) (v : ℝ)
    (hE : TendstoInMeasure μ E atTop (fun _ ↦ v)) (hV : Tendsto V atTop (nhds v)) :
    TendstoInMeasure μ (fun n ω ↦ E n ω-V n) atTop (fun _ ↦ (0:ℝ)) ∧
    (v ≠ 0 → TendstoInMeasure μ (fun n ω ↦ E n ω/V n) atTop (fun _ ↦ (1:ℝ))) := by
  have hv : TendstoInMeasure μ (fun n (_ : Ω) ↦ V n) atTop (fun _ ↦ v) :=
    tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const) (Eventually.of_forall (fun _ ↦ hV))
  constructor
  · simpa only [sub_self] using
      continuous_pair_tendstoInMeasure E (fun n _ ↦ V n) v v hE hv (fun z ↦ z.1-z.2) (by fun_prop)
  · intro hne
    simpa only [div_self hne] using
      continuous_pair_tendstoInMeasure E (fun n _ ↦ V n) v v hE hv (fun z ↦ z.1/z.2)
        (continuousAt_fst.div continuousAt_snd hne)

/-- The estimator estimates the actual rescaled coverage variance, including at zero limiting variance. -/
theorem iid_continuous_score_estimator_variance_comparison {m : ℕ} (hm : 0 < m)
    (S : ℕ → Ω → Fin m → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (hident : ∀ j, IdentDistrib (S j) (S 0) μ μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i t, μ.real {ω | S j ω i ≤ t} = F t)
    (k : ∀ n, Fin ((n+1)*m)) (p : ℝ) (hp : p ∈ Ioo 0 1)
    (hkp : Tendsto (fun n ↦ (((k n).val+1 : ℕ) : ℝ)/(((n+1)*m : ℕ)+1)) atTop (nhds p)) :
    let E := clusterVarianceEstimator S (fun n ω ↦ sampleQuantile (pooledSample S (n+1) ω) (k n))
    let V := fun n ↦ (((n+1)*m : ℕ) : ℝ)*Var[fun ω ↦ F (sampleQuantile (pooledSample S (n+1) ω) (k n)); μ]
    TendstoInMeasure μ (fun n ω ↦ E n ω-V n) atTop (fun _ ↦ (0:ℝ)) ∧
      ((clusterCoverageVariance (μ := μ) (fun j ω i ↦ F (S j ω i)) p : ℝ) ≠ 0 →
        TendstoInMeasure μ (fun n ω ↦ E n ω/V n) atTop (fun _ ↦ (1:ℝ))) := by
  have hE := iid_continuous_score_estimator_consistent hm S hS hindep hident F hF hmono h0 h1 hCDF k p hkp
  rw [← clusterCoverageVariance_eq (fun j ω i ↦ F (S j ω i)) p] at hE
  exact consistent_estimator_comparison _ _ _ hE
    (iid_continuous_score_coverage_variance_limit hm S hS hindep hident F hF hmono h0 h1 hCDF p hp k hkp)

end Exceedance
#print axioms Exceedance.iid_count_moment_random_cutoff

#print axioms Exceedance.iid_pooled_quantile_estimator_consistent

#print axioms Exceedance.iid_continuous_score_estimator_consistent
#print axioms Exceedance.clusterVarianceEstimator_eq_sample_variance

#print axioms Exceedance.iid_continuous_score_ceil_estimator_consistent
#print axioms Exceedance.iid_continuous_score_estimator_variance_comparison
