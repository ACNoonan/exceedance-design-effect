import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter
namespace Exceedance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def indicator (A : Set Ω) : Ω → ℝ := A.indicator (fun _ ↦ 1)

lemma indicator_memLp {A : Set Ω} (hA : MeasurableSet A) : MemLp (indicator A) 2 μ := by
  exact (memLp_const (1 : ℝ)).indicator hA

omit [IsProbabilityMeasure μ] in
lemma indicator_mean {A : Set Ω} (hA : MeasurableSet A) : μ[indicator A] = μ.real A := by
  exact integral_indicator_one hA

omit [MeasurableSpace Ω] in
lemma indicator_square (A : Set Ω) : (fun ω ↦ indicator A ω ^ 2) = indicator A := by
  classical
  funext ω
  by_cases h : ω ∈ A <;> simp [indicator, Set.indicator, h]

omit [MeasurableSpace Ω] in
lemma indicator_product (A B : Set Ω) : indicator A * indicator B = indicator (A ∩ B) := by
  classical
  funext ω
  by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [indicator, Set.indicator, ha, hb]

lemma indicator_variance {A : Set Ω} (hA : MeasurableSet A) :
    Var[indicator A; μ] = μ.real A * (1 - μ.real A) := by
  rw [variance_eq_sub (indicator_memLp hA)]
  change (∫ ω, indicator A ω ^ 2 ∂μ) - μ[indicator A] ^ 2 = _
  rw [indicator_square, indicator_mean hA]
  ring

lemma indicator_pair_covariance {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    cov[indicator A, indicator B; μ] = μ.real (A ∩ B) - μ.real A * μ.real B := by
  rw [covariance_eq_sub (indicator_memLp hA) (indicator_memLp hB),
      indicator_product, indicator_mean (hA.inter hB), indicator_mean hA, indicator_mean hB]

/-- Exact finite-cluster variance, from event probabilities rather than assumed covariance sums.
    Equal off-diagonal probabilities are weaker than full within-cluster exchangeability. -/
theorem cluster_indicator_variance {ι : Type*} [Fintype ι]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (p δ : ℝ)
    (hmarg : ∀ i, μ.real (A i) = p)
    (hpair : ∀ i j, i ≠ j → μ.real (A i ∩ A j) = δ) :
    Var[fun ω ↦ ∑ i, indicator (A i) ω; μ] =
      (Fintype.card ι : ℝ) * (p * (1-p)) +
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)-1) * (δ-p^2) := by
  classical
  have hcov (i j : ι) : cov[indicator (A i), indicator (A j); μ] =
      (δ-p^2) + if i=j then p*(1-p)-(δ-p^2) else 0 := by
    by_cases h : i=j
    · subst j
      rw [covariance_self (indicator_memLp (hA i)).aemeasurable, indicator_variance (hA i), hmarg]
      simp
    · rw [indicator_pair_covariance (hA i) (hA j), hpair i j h, hmarg, hmarg]
      simp [h, pow_two]
  rw [variance_fun_sum (fun i ↦ indicator_memLp (hA i))]
  simp_rw [hcov, Finset.sum_add_distrib]
  simp
  ring


set_option maxHeartbeats 800000 in
/-- Fixed-level count CLT. Independence is required across clusters, not within them.
    The Gaussian variance is derived from the common event probabilities.
    This does not yet transfer convergence to an estimated quantile. -/
theorem cluster_count_clt {ι Ω' : Type*} [Fintype ι] [MeasurableSpace Ω']
    {ν : Measure Ω'} [IsProbabilityMeasure ν] {Y : Ω' → ℝ}
    (A : ℕ → ι → Set Ω) (hA : ∀ j i, MeasurableSet (A j i)) (p δ : ℝ)
    (hmarg : ∀ i, μ.real (A 0 i) = p)
    (hpair : ∀ i k, i ≠ k → μ.real (A 0 i ∩ A 0 k) = δ)
    (hindep : iIndepFun (fun j ω ↦ ∑ i, indicator (A j i) ω) μ)
    (hident : ∀ j, IdentDistrib (fun ω ↦ ∑ i, indicator (A j i) ω)
      (fun ω ↦ ∑ i, indicator (A 0 i) ω) μ μ)
    (hY : HasLaw Y (gaussianReal 0
      ((Fintype.card ι : ℝ) * (p*(1-p)) +
       (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)-1) * (δ-p^2)).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ *
        (∑ j ∈ Finset.range n, (∑ i, indicator (A j i) ω) -
          n * ((Fintype.card ι : ℝ) * p))) atTop Y (fun _ ↦ μ) ν := by
  classical
  have hLp : MemLp (fun ω ↦ ∑ i, indicator (A 0 i) ω) 2 μ :=
    memLp_finsetSum _ (fun i _ ↦ indicator_memLp (hA 0 i))
  have hmean : μ[fun ω ↦ ∑ i, indicator (A 0 i) ω] = (Fintype.card ι : ℝ)*p := by
    rw [integral_finsetSum _ (fun i _ ↦ (indicator_memLp (hA 0 i)).integrable (by norm_num))]
    simp only [indicator_mean (hA 0 _), hmarg, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hvar := cluster_indicator_variance (A 0) (hA 0) p δ hmarg hpair
  have hY' : HasLaw Y (gaussianReal 0
      Var[fun ω ↦ ∑ i, indicator (A 0 i) ω; μ].toNNReal) ν := by
    rwa [hvar]
  have hc := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun j ω ↦ ∑ i, indicator (A j i) ω) (P := μ) (P' := ν) (Y := Y)
    hY' hLp hindep hident
  rw [hmean] at hc
  exact hc

/-- A count of rare events has variance at most m²h, without assumptions on dependence.
    Apply this to events that an observation lies between two nearby thresholds. -/
theorem cluster_increment_variance_bound {ι : Type*} [Fintype ι]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (h : ℝ)
    (hmarg : ∀ i, μ.real (A i) = h) :
    Var[fun ω ↦ ∑ i, indicator (A i) ω; μ] ≤ (Fintype.card ι : ℝ)^2 * h := by
  classical
  have hLp : MemLp (fun ω ↦ ∑ i, indicator (A i) ω) 2 μ :=
    memLp_finsetSum _ (fun i _ ↦ indicator_memLp (hA i))
  have hmean : μ[fun ω ↦ ∑ i, indicator (A i) ω] = (Fintype.card ι : ℝ)*h := by
    rw [integral_finsetSum _ (fun i _ ↦ (indicator_memLp (hA i)).integrable (by norm_num))]
    simp only [indicator_mean (hA _), hmarg, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hb : ∀ ω, (∑ i, indicator (A i) ω) ∈ Set.Icc 0 (Fintype.card ι : ℝ) := by
    intro ω
    constructor
    · exact Finset.sum_nonneg (fun i _ ↦ by simp [indicator, Set.indicator]; split_ifs <;> norm_num)
    · calc
        ∑ i, indicator (A i) ω ≤ ∑ _i : ι, (1 : ℝ) := by
          exact Finset.sum_le_sum (fun i _ ↦ by simp [indicator, Set.indicator]; split_ifs <;> norm_num)
        _ = (Fintype.card ι : ℝ) := by simp
  have hv := variance_le_sub_mul_sub (Filter.Eventually.of_forall hb) hLp.aemeasurable
  rw [hmean] at hv
  nlinarith [sq_nonneg ((Fintype.card ι : ℝ)*h)]


/-- Independent clusters add their rare-event count variances.
    For b clusters of size m, this is the b m² h bound used in local count inversion. -/
theorem independent_increment_variance_bound {κ ι : Type*} [Fintype κ] [Fintype ι]
    (A : κ → ι → Set Ω) (hA : ∀ j i, MeasurableSet (A j i)) (h : ℝ)
    (hmarg : ∀ j i, μ.real (A j i) = h)
    (hindep : iIndepFun (fun j ω ↦ ∑ i, indicator (A j i) ω) μ) :
    Var[∑ j, (fun ω ↦ ∑ i, indicator (A j i) ω); μ] ≤
      (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)^2 * h := by
  classical
  rw [IndepFun.variance_sum
    (fun j _ ↦ memLp_finsetSum _ (fun i _ ↦ indicator_memLp (hA j i)))
    (fun j _ l _ hjl ↦ hindep.indepFun hjl)]
  calc
    ∑ j, Var[fun ω ↦ ∑ i, indicator (A j i) ω; μ] ≤
        ∑ _j : κ, (Fintype.card ι : ℝ)^2*h :=
      Finset.sum_le_sum (fun j _ ↦ cluster_increment_variance_bound (A j) (hA j) h (hmarg j))
    _ = _ := by simp; ring


/-- Chebyshev bound for local count increments across independent clusters. -/
theorem independent_increment_deviation_bound {κ ι : Type*} [Fintype κ] [Fintype ι]
    (A : κ → ι → Set Ω) (hA : ∀ j i, MeasurableSet (A j i)) (h c : ℝ) (hc : 0 < c)
    (hmarg : ∀ j i, μ.real (A j i) = h)
    (hindep : iIndepFun (fun j ω ↦ ∑ i, indicator (A j i) ω) μ) :
    μ {ω | c ≤ |(∑ j, ∑ i, indicator (A j i) ω) -
      μ[fun ω ↦ ∑ j, ∑ i, indicator (A j i) ω]|} ≤
      ENNReal.ofReal ((Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)^2 * h / c^2) := by
  classical
  have hLp : MemLp (fun ω ↦ ∑ j, ∑ i, indicator (A j i) ω) 2 μ :=
    memLp_finsetSum _ (fun j _ ↦ memLp_finsetSum _ (fun i _ ↦ indicator_memLp (hA j i)))
  have hv := independent_increment_variance_bound A hA h hmarg hindep
  have hv' : Var[fun ω ↦ ∑ j, ∑ i, indicator (A j i) ω; μ] ≤
      (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)^2 * h := by
    have he : (∑ j, (fun ω ↦ ∑ i, indicator (A j i) ω)) =
        (fun ω ↦ ∑ j, ∑ i, indicator (A j i) ω) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [← he]
    exact hv
  exact (meas_ge_le_variance_div_sq hLp hc).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hv' (sq_nonneg c)))

/-- Vanishing variance makes centered random variables converge in probability to zero. -/
theorem centered_tendstoInMeasure_of_variance_bound
    (X : ℕ → Ω → ℝ) (hX : ∀ n, MemLp (X n) 2 μ)
    (v : ℕ → ℝ) (hv : ∀ n, Var[X n; μ] ≤ v n)
    (hv0 : Tendsto v atTop (nhds 0)) :
    TendstoInMeasure μ (fun n ω ↦ X n ω - (∫ ω, X n ω ∂μ)) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hu : Tendsto (fun n ↦ ENNReal.ofReal (v n / ε^2)) atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal (hv0.div_const (ε^2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro n
    exact zero_le
  · intro n
    simpa only [Pi.zero_apply, sub_zero, Real.norm_eq_abs] using
      (meas_ge_le_variance_div_sq (hX n) hε).trans
        (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hv n) (sq_nonneg ε)))

/-- A normalized local count increment vanishes as its interval probability vanishes.
    Rows may use different intervals and cluster laws. Independence is only required within rows. -/
theorem normalized_increment_tendstoInMeasure {ι : Type*} [Fintype ι]
    (hm : 0 < Fintype.card ι)
    (A : (n : ℕ) → Fin (n+1) → ι → Set Ω)
    (hA : ∀ n j i, MeasurableSet (A n j i))
    (h : ℕ → ℝ) (hh : Tendsto h atTop (nhds 0))
    (hmarg : ∀ n j i, μ.real (A n j i) = h n)
    (hindep : ∀ n, iIndepFun (fun j ω ↦ ∑ i, indicator (A n j i) ω) μ) :
    TendstoInMeasure μ
      (fun n ω ↦ ((√((n+1 : ℕ) * (Fintype.card ι : ℝ)))⁻¹ *
        (∑ j, ∑ i, indicator (A n j i) ω)) -
        (∫ ω, (√((n+1 : ℕ) * (Fintype.card ι : ℝ)))⁻¹ *
          (∑ j, ∑ i, indicator (A n j i) ω) ∂μ)) atTop 0 := by
  classical
  apply centered_tendstoInMeasure_of_variance_bound
    (v := fun n ↦ (Fintype.card ι : ℝ) * h n)
  · intro n
    exact (memLp_finsetSum _ (fun j _ ↦ memLp_finsetSum _
      (fun i _ ↦ indicator_memLp (hA n j i)))).const_mul _
  · intro n
    have hv := independent_increment_variance_bound (A n) (hA n) (h n) (hmarg n) (hindep n)
    have he : (∑ j, (fun ω ↦ ∑ i, indicator (A n j i) ω)) =
        (fun ω ↦ ∑ j, ∑ i, indicator (A n j i) ω) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [he] at hv
    rw [variance_const_mul]
    have hn : (0 : ℝ) < (n+1 : ℕ) := by positivity
    have hm' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hm
    have hs : (√((n+1 : ℕ) * (Fintype.card ι : ℝ)))^2 =
        (n+1 : ℕ) * (Fintype.card ι : ℝ) := Real.sq_sqrt (by positivity)
    calc
      _ ≤ (√((n+1 : ℕ) * (Fintype.card ι : ℝ)))⁻¹ ^ 2 *
          ((Fintype.card (Fin (n+1)) : ℝ) * (Fintype.card ι : ℝ)^2 * h n) :=
        mul_le_mul_of_nonneg_left hv (sq_nonneg _)
      _ = _ := by
        rw [inv_pow, hs]
        simp only [Fintype.card_fin]
        field_simp
  · simpa using hh.const_mul (Fintype.card ι : ℝ)


/-- A centered local perturbation with vanishing variance preserves the count CLT.
    The limit law can be degenerate. No positive-variance assumption is used here. -/
theorem count_limit_stable_under_local_perturbation
    {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (X Y : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (hXZ : TendstoInDistribution X atTop Z (fun _ ↦ μ) ν)
    (hY : ∀ n, AEMeasurable (Y n) μ)
    (hLp : ∀ n, MemLp (fun ω ↦ Y n ω - X n ω) 2 μ)
    (hmean : ∀ n, (∫ ω, Y n ω - X n ω ∂μ) = 0)
    (v : ℕ → ℝ) (hv : ∀ n, Var[fun ω ↦ Y n ω-X n ω; μ] ≤ v n)
    (hv0 : Tendsto v atTop (nhds 0)) :
    TendstoInDistribution Y atTop Z (fun _ ↦ μ) ν := by
  have hp := centered_tendstoInMeasure_of_variance_bound
    (fun n ω ↦ Y n ω-X n ω) hLp v hv hv0
  have hp' : TendstoInMeasure μ (Y-X) atTop 0 := by
    change TendstoInMeasure μ (fun n ω ↦ Y n ω-X n ω) atTop 0
    simpa only [hmean, sub_zero, Pi.sub_apply] using hp
  exact tendstoInDistribution_of_tendstoInMeasure_sub Y Z hXZ hp' hY


end Exceedance
#print axioms Exceedance.cluster_indicator_variance

#print axioms Exceedance.cluster_count_clt

#print axioms Exceedance.cluster_increment_variance_bound

#print axioms Exceedance.independent_increment_variance_bound

#print axioms Exceedance.independent_increment_deviation_bound

#print axioms Exceedance.normalized_increment_tendstoInMeasure

#print axioms Exceedance.count_limit_stable_under_local_perturbation
