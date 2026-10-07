import GaussianTail
import EstimatorConsistency
import TailLimits

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

noncomputable def standardGaussianPair : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)
instance standardGaussianPair_probability : IsProbabilityMeasure standardGaussianPair := by
  unfold standardGaussianPair; infer_instance

lemma standardGaussianPair_first : standardGaussianPair.map Prod.fst = gaussianReal 0 1 := by
  simp [standardGaussianPair, Measure.map_fst_prod]

lemma standardGaussianPair_second : standardGaussianPair.map Prod.snd = gaussianReal 0 1 := by
  simp [standardGaussianPair, Measure.map_snd_prod]

lemma standardGaussianPair_linear (a b : ℝ) :
    standardGaussianPair.map (fun z ↦ a*z.1+b*z.2) =
      gaussianReal 0 ⟨a^2+b^2, add_nonneg (sq_nonneg _) (sq_nonneg _)⟩ := by
  have hx : HasLaw (fun z : ℝ × ℝ ↦ z.1) (gaussianReal 0 1) standardGaussianPair :=
    ⟨measurable_fst.aemeasurable,standardGaussianPair_first⟩
  have hy : HasLaw (fun z : ℝ × ℝ ↦ z.2) (gaussianReal 0 1) standardGaussianPair :=
    ⟨measurable_snd.aemeasurable,standardGaussianPair_second⟩
  have hi : IndepFun (fun z : ℝ × ℝ ↦ a*z.1) (fun z : ℝ × ℝ ↦ b*z.2) standardGaussianPair :=
    indepFun_prod (measurable_id.const_mul a) (measurable_id.const_mul b)
  have hh := gaussianReal_add_gaussianReal_of_indepFun hi
    (gaussianReal_const_mul hx a).map_eq (gaussianReal_const_mul hy b).map_eq
  simp only [mul_zero,zero_add,mul_one] at hh
  convert hh using 1 <;> rfl

noncomputable def correlatedGaussian (rho : ℝ) (z : ℝ × ℝ) : ℝ :=
  rho*z.1+Real.sqrt (1-rho^2)*z.2

lemma correlatedGaussian_measurable (rho : ℝ) : Measurable (correlatedGaussian rho) := by
  unfold correlatedGaussian; fun_prop

lemma correlatedGaussian_law (rho : ℝ) (hr : rho ∈ Icc (-1) 1) :
    standardGaussianPair.map (correlatedGaussian rho) = gaussianReal 0 1 := by
  have hsq : 0 ≤ 1-rho^2 := by nlinarith [hr.1,hr.2]
  have hv : (⟨rho^2+(Real.sqrt (1-rho^2))^2, add_nonneg (sq_nonneg _) (sq_nonneg _)⟩ : NNReal) = 1 := by
    apply NNReal.eq
    change rho^2+(Real.sqrt (1-rho^2))^2 = 1
    rw [Real.sq_sqrt hsq]
    ring
  have hh := standardGaussianPair_linear rho (Real.sqrt (1-rho^2))
  rw [hv] at hh
  exact hh

lemma correlatedGaussian_sum_law (rho : ℝ) (hr : rho ∈ Ioo (-1) 1) :
    standardGaussianPair.map (fun z ↦ z.1+correlatedGaussian rho z) =
      gaussianReal 0 (2*(1+rho)).toNNReal := by
  have hsq : 0 ≤ 1-rho^2 := by nlinarith [hr.1,hr.2]
  have hv : (⟨(1+rho)^2+(Real.sqrt (1-rho^2))^2, add_nonneg (sq_nonneg _) (sq_nonneg _)⟩ : NNReal) =
      (2*(1+rho)).toNNReal := by
    apply NNReal.eq
    change (1+rho)^2+(Real.sqrt (1-rho^2))^2 = ((2*(1+rho)).toNNReal : ℝ)
    rw [Real.coe_toNNReal _ (by linarith [hr.1]),Real.sq_sqrt hsq]
    ring
  have hh := standardGaussianPair_linear (1+rho) (Real.sqrt (1-rho^2))
  rw [hv] at hh
  convert hh using 1
  congr 1
  funext z
  dsimp [correlatedGaussian]
  ring

/-- Both threshold-parametrized tail ratios vanish for the constructed bivariate normal law. -/
theorem correlatedGaussian_tail_ratios (rho : ℝ) (hr : rho ∈ Ioo (-1) 1) :
    Tendsto (fun t ↦ standardGaussianPair.real {z | t < z.1 ∧ t < correlatedGaussian rho z}/
      standardGaussianPair.real {z | t < z.1}) atTop (nhds 0) ∧
    Tendsto (fun t ↦ standardGaussianPair.real {z | z.1 < t ∧ correlatedGaussian rho z < t}/
      standardGaussianPair.real {z | z.1 < t}) atBot (nhds 0) := by
  have hv : 0 < (2*(1+rho)).toNNReal := Real.toNNReal_pos.mpr (by linarith [hr.1,hr.2])
  have hv4 : ((2*(1+rho)).toNNReal:ℝ) < 4 := by rw [Real.coe_toNNReal _ (by linarith [hr.1,hr.2])]; linarith [hr.1,hr.2]
  exact ⟨gaussian_pair_upper_tail_ratio _ _ measurable_fst (correlatedGaussian_measurable rho)
    standardGaussianPair_first _ hv hv4 (correlatedGaussian_sum_law rho hr),
    gaussian_pair_lower_tail_ratio _ _ measurable_fst (correlatedGaussian_measurable rho)
    standardGaussianPair_first _ hv hv4 (correlatedGaussian_sum_law rho hr)⟩


noncomputable def bivariateNormalCDF (rho s t : ℝ) : ℝ :=
  standardGaussianPair.real {z | z.1 ≤ s ∧ correlatedGaussian rho z ≤ t}

/-- The Gaussian indicator-correlation formula at a standard-normal quantile. -/
theorem gaussian_indicator_correlation_formula (rho : ℝ) (hr : rho ∈ Icc (-1) 1)
    (z p : ℝ) (hp : cdf (gaussianReal 0 1) z = p) :
    cov[indicator {w : ℝ × ℝ | w.1 ≤ z}, indicator {w | correlatedGaussian rho w ≤ z}; standardGaussianPair] /
      (p*(1-p)) = (bivariateNormalCDF rho z z-p^2)/(p*(1-p)) := by
  have h1 : standardGaussianPair.real {w : ℝ × ℝ | w.1 ≤ z} = p := by
    rw [← hp,cdf_eq_real,← standardGaussianPair_first,map_measureReal_apply measurable_fst measurableSet_Iic]
    rfl
  have h2 : standardGaussianPair.real {w | correlatedGaussian rho w ≤ z} = p := by
    rw [← hp,cdf_eq_real,← correlatedGaussian_law rho hr,
      map_measureReal_apply (correlatedGaussian_measurable rho) measurableSet_Iic]
    rfl
  rw [indicator_pair_covariance (measurableSet_le measurable_fst measurable_const)
    (measurableSet_le (correlatedGaussian_measurable rho) measurable_const),h1,h2]
  simp only [bivariateNormalCDF,pow_two]
  rfl

lemma standardGaussian_cdf_interior (x : ℝ) : cdf (gaussianReal 0 1) x ∈ Ioo 0 1 := by
  have hi : 0 < (gaussianReal 0 1).real (Iic x) := by
    apply ENNReal.toReal_pos
    · intro h
      have hh := gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:NNReal) ≠ 0) h
      simpa using hh
    · finiteness
  have ho : 0 < (gaussianReal 0 1).real (Ioi x) := by
    apply ENNReal.toReal_pos
    · intro h
      have hh := gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:NNReal) ≠ 0) h
      simpa using hh
    · finiteness
  rw [← compl_Iic,measureReal_compl measurableSet_Iic,probReal_univ] at ho
  rw [cdf_eq_real]
  exact ⟨hi,by linarith⟩

lemma standardGaussian_cdf_continuous : Continuous (cdf (gaussianReal 0 1)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hU : Measurable (fun x : ℝ ↦ fun _ : Fin 1 ↦ x) := by fun_prop
  have hh := thresholdCount_moment_continuousAt (μ := gaussianReal 0 1)
    (fun x : ℝ ↦ fun _ : Fin 1 ↦ x) hU p
    (fun i ↦ by
      haveI := nullSingletonClass_gaussianReal (μ := (0:ℝ)) (by norm_num : (1:NNReal) ≠ 0)
      exact measure_singleton p) 1
  have he (t : ℝ) : (∫ x : ℝ, (thresholdCount t (fun _ : Fin 1 ↦ x))^1 ∂gaussianReal 0 1) =
      cdf (gaussianReal 0 1) t := by
    simp only [thresholdCount,Fin.sum_univ_one,pow_one]
    change (∫ x : ℝ, indicator (Iic t) x ∂gaussianReal 0 1) = cdf (gaussianReal 0 1) t
    rw [indicator_mean measurableSet_Iic,cdf_eq_real]
  simpa only [he] using hh

/-- Every interior probability has a standard-normal quantile. -/
lemma standardGaussian_quantile_exists (p : ℝ) (hp : p ∈ Ioo 0 1) :
    ∃ z, cdf (gaussianReal 0 1) z = p :=
  continuous_cdf_hits_interior _ standardGaussian_cdf_continuous
    (tendsto_cdf_atBot _) (tendsto_cdf_atTop _) p hp.1 hp.2

lemma gaussian_quantile_upper_tendsto (z : ℝ → ℝ)
    (hz : ∀ p ∈ Ioo 0 1, cdf (gaussianReal 0 1) (z p) = p) :
    Tendsto z (nhdsWithin 1 (Ioo 0 1)) atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hp : Tendsto (fun p : ℝ ↦ p) (nhdsWithin 1 (Ioo 0 1)) (nhds 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  filter_upwards [hp.eventually_const_lt (standardGaussian_cdf_interior b).2,self_mem_nhdsWithin] with p hpb hp
  by_contra h
  have hh := monotone_cdf (gaussianReal 0 1) (le_of_lt (lt_of_not_ge h))
  rw [hz p hp] at hh
  linarith

lemma gaussian_quantile_lower_tendsto (z : ℝ → ℝ)
    (hz : ∀ p ∈ Ioo 0 1, cdf (gaussianReal 0 1) (z p) = p) :
    Tendsto z (nhdsWithin 0 (Ioo 0 1)) atBot := by
  apply tendsto_atBot.mpr
  intro b
  have hp : Tendsto (fun p : ℝ ↦ p) (nhdsWithin 0 (Ioo 0 1)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  filter_upwards [hp.eventually_lt_const (standardGaussian_cdf_interior b).1,self_mem_nhdsWithin] with p hpb hp
  by_contra h
  have hh := monotone_cdf (gaussianReal 0 1) (le_of_lt (lt_of_not_ge h))
  rw [hz p hp] at hh
  linarith


lemma correlatedGaussian_marginal_probabilities (rho : ℝ) (hr : rho ∈ Icc (-1) 1) (t : ℝ) :
    standardGaussianPair.real {w : ℝ × ℝ | w.1 ≤ t} = cdf (gaussianReal 0 1) t ∧
    standardGaussianPair.real {w | correlatedGaussian rho w ≤ t} = cdf (gaussianReal 0 1) t := by
  constructor
  · rw [cdf_eq_real,← standardGaussianPair_first,map_measureReal_apply measurable_fst measurableSet_Iic]
    rfl
  · rw [cdf_eq_real,← correlatedGaussian_law rho hr,
      map_measureReal_apply (correlatedGaussian_measurable rho) measurableSet_Iic]
    rfl

lemma correlatedGaussian_lower_probabilities (rho : ℝ) (hr : rho ∈ Icc (-1) 1) (t : ℝ) :
    standardGaussianPair.real {w : ℝ × ℝ | w.1 < t} = cdf (gaussianReal 0 1) t ∧
    standardGaussianPair.real {w | w.1 < t ∧ correlatedGaussian rho w < t} = bivariateNormalCDF rho t t := by
  haveI := nullSingletonClass_gaussianReal (μ := (0:ℝ)) (by norm_num : (1:NNReal) ≠ 0)
  have hX : standardGaussianPair {w : ℝ × ℝ | w.1 = t} = 0 := by
    have hh := (show HasLaw Prod.fst (gaussianReal 0 1) standardGaussianPair from
      ⟨measurable_fst.aemeasurable,standardGaussianPair_first⟩).measure_eq (measurableSet_singleton t)
    change standardGaussianPair {w : ℝ × ℝ | w.1 = t} = (gaussianReal 0 1) {t} at hh
    simpa using hh
  have hY : standardGaussianPair {w | correlatedGaussian rho w = t} = 0 := by
    have hh := (show HasLaw (correlatedGaussian rho) (gaussianReal 0 1) standardGaussianPair from
      ⟨(correlatedGaussian_measurable rho).aemeasurable,correlatedGaussian_law rho hr⟩).measure_eq
        (measurableSet_singleton t)
    change standardGaussianPair {w | correlatedGaussian rho w = t} = (gaussianReal 0 1) {t} at hh
    simpa using hh
  constructor
  · rw [probability_lt_eq_le _ t hX]
    exact (correlatedGaussian_marginal_probabilities rho hr t).1
  · apply measureReal_congr
    have hx : ∀ᵐ w ∂standardGaussianPair, w.1 ≠ t := by simpa only [ae_iff,not_not] using hX
    have hy : ∀ᵐ w ∂standardGaussianPair, correlatedGaussian rho w ≠ t := by simpa only [ae_iff,not_not] using hY
    filter_upwards [hx,hy] with w hx hy
    change (w.1 < t ∧ correlatedGaussian rho w < t) = (w.1 ≤ t ∧ correlatedGaussian rho w ≤ t)
    exact propext (and_congr (lt_iff_le_and_ne.trans (and_iff_left hx))
      (lt_iff_le_and_ne.trans (and_iff_left hy)))

lemma correlatedGaussian_upper_probabilities (rho : ℝ) (hr : rho ∈ Icc (-1) 1) (t : ℝ) :
    standardGaussianPair.real {w : ℝ × ℝ | t < w.1} = 1-cdf (gaussianReal 0 1) t ∧
    standardGaussianPair.real {w | t < w.1 ∧ t < correlatedGaussian rho w} =
      1-2*cdf (gaussianReal 0 1) t+bivariateNormalCDF rho t t := by
  have hA : MeasurableSet {w : ℝ × ℝ | w.1 ≤ t} := measurableSet_le measurable_fst measurable_const
  have hB : MeasurableSet {w | correlatedGaussian rho w ≤ t} :=
    measurableSet_le (correlatedGaussian_measurable rho) measurable_const
  have hprob := correlatedGaussian_marginal_probabilities rho hr t
  constructor
  · rw [show {w : ℝ × ℝ | t < w.1} = {w | w.1 ≤ t}ᶜ by ext w; simp,
      measureReal_compl hA,probReal_univ,hprob.1]
  · rw [show {w : ℝ × ℝ | t < w.1 ∧ t < correlatedGaussian rho w} =
      ({w | w.1 ≤ t} ∪ {w | correlatedGaussian rho w ≤ t})ᶜ by ext w; simp,
      measureReal_compl (hA.union hB),probReal_univ]
    have hh := measureReal_union_add_inter (μ := standardGaussianPair) (s := {w : ℝ × ℝ | w.1 ≤ t}) hB
    rw [hprob.1,hprob.2] at hh
    change _ = 1-2*cdf (gaussianReal 0 1) t+
      standardGaussianPair.real ({w | w.1 ≤ t} ∩ {w | correlatedGaussian rho w ≤ t})
    linarith

noncomputable def standardNormalQuantile (p : ℝ) : ℝ :=
  if hp : p ∈ Ioo 0 1 then (standardGaussian_quantile_exists p hp).choose else 0

lemma standardNormalQuantile_cdf (p : ℝ) (hp : p ∈ Ioo 0 1) :
    cdf (gaussianReal 0 1) (standardNormalQuantile p) = p := by
  rw [standardNormalQuantile,dif_pos hp]
  exact (standardGaussian_quantile_exists p hp).choose_spec

noncomputable def gaussianCopulaDiagonal (rho p : ℝ) : ℝ :=
  bivariateNormalCDF rho (standardNormalQuantile p) (standardNormalQuantile p)

/-- Both Gaussian copula tail-dependence coefficients vanish, at probability endpoints. -/
theorem gaussian_copula_tail_coefficients (rho : ℝ) (hr : rho ∈ Ioo (-1) 1) :
    Tendsto (fun p ↦ (1-2*p+gaussianCopulaDiagonal rho p)/(1-p))
      (nhdsWithin 1 (Ioo 0 1)) (nhds 0) ∧
    Tendsto (fun p ↦ gaussianCopulaDiagonal rho p/p)
      (nhdsWithin 0 (Ioo 0 1)) (nhds 0) := by
  have hh := correlatedGaussian_tail_ratios rho hr
  constructor
  · apply (hh.1.comp (gaussian_quantile_upper_tendsto standardNormalQuantile standardNormalQuantile_cdf)).congr'
    filter_upwards [self_mem_nhdsWithin] with p hp
    dsimp only [Function.comp_apply]
    rw [(correlatedGaussian_upper_probabilities rho ⟨hr.1.le,hr.2.le⟩ _).1,
      (correlatedGaussian_upper_probabilities rho ⟨hr.1.le,hr.2.le⟩ _).2,standardNormalQuantile_cdf p hp]
    rfl
  · apply (hh.2.comp (gaussian_quantile_lower_tendsto standardNormalQuantile standardNormalQuantile_cdf)).congr'
    filter_upwards [self_mem_nhdsWithin] with p hp
    dsimp only [Function.comp_apply]
    rw [(correlatedGaussian_lower_probabilities rho ⟨hr.1.le,hr.2.le⟩ _).1,
      (correlatedGaussian_lower_probabilities rho ⟨hr.1.le,hr.2.le⟩ _).2,standardNormalQuantile_cdf p hp]
    rfl


/-- The construction's score covariance, and hence its score correlation, is rho. -/
theorem correlatedGaussian_covariance (rho : ℝ) :
    cov[(fun w : ℝ × ℝ ↦ w.1), correlatedGaussian rho; standardGaussianPair] = rho := by
  have hx : MemLp (fun w : ℝ × ℝ ↦ w.1) 2 standardGaussianPair :=
    (memLp_id_gaussianReal' 2 (by norm_num)).comp_measurePreserving
      ⟨measurable_fst,standardGaussianPair_first⟩
  have hy : MemLp (fun w : ℝ × ℝ ↦ w.2) 2 standardGaussianPair :=
    (memLp_id_gaussianReal' 2 (by norm_num)).comp_measurePreserving
      ⟨measurable_snd,standardGaussianPair_second⟩
  have hi : IndepFun (fun w : ℝ × ℝ ↦ w.1) (fun w : ℝ × ℝ ↦ w.2) standardGaussianPair :=
    indepFun_prod measurable_id measurable_id
  have hv : Var[fun w : ℝ × ℝ ↦ w.1; standardGaussianPair] = 1 := by
    rw [← variance_id_map measurable_fst.aemeasurable,standardGaussianPair_first,variance_id_gaussianReal]
    rfl
  change cov[(fun w : ℝ × ℝ ↦ w.1), (fun w ↦ rho*w.1)+(fun w ↦ Real.sqrt (1-rho^2)*w.2); standardGaussianPair] = rho
  rw [covariance_add_right hx (hx.const_mul _) (hy.const_mul _),
    covariance_const_mul_right,covariance_const_mul_right,covariance_self hx.aemeasurable,
    hv,hi.covariance_eq_zero hx hy]
  ring

/-- Indicator correlation also tends to zero at both Gaussian copula endpoints. -/
theorem gaussian_indicator_correlation_tail_limits (rho : ℝ) (hr : rho ∈ Ioo (-1) 1) :
    Tendsto (fun p ↦ (gaussianCopulaDiagonal rho p-p^2)/(p*(1-p)))
      (nhdsWithin 1 (Ioo 0 1)) (nhds 0) ∧
    Tendsto (fun p ↦ (gaussianCopulaDiagonal rho p-p^2)/(p*(1-p)))
      (nhdsWithin 0 (Ioo 0 1)) (nhds 0) :=
  ⟨indicator_correlation_upper_tail _ 0 (gaussian_copula_tail_coefficients rho hr).1,
    indicator_correlation_lower_tail _ 0 (gaussian_copula_tail_coefficients rho hr).2⟩

end Exceedance
#print axioms Exceedance.correlatedGaussian_law
#print axioms Exceedance.correlatedGaussian_tail_ratios

#print axioms Exceedance.gaussian_indicator_correlation_formula

#print axioms Exceedance.gaussian_copula_tail_coefficients

#print axioms Exceedance.correlatedGaussian_covariance
#print axioms Exceedance.gaussian_indicator_correlation_tail_limits
