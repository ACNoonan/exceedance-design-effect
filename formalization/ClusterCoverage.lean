import ClusterSample
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

noncomputable def clusterCoverageVariance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {m : ℕ} (U : ℕ → Ω → Fin m → ℝ) (p : ℝ) : NNReal :=
  NNReal.mk (((√(m : ℝ))⁻¹)^2) (sq_nonneg _) *
    Var[fun ω ↦ thresholdCount p (U 0 ω); μ].toNNReal

/-- The limiting variance is the cluster-count variance divided by cluster size. -/
theorem clusterCoverageVariance_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {m : ℕ} (U : ℕ → Ω → Fin m → ℝ) (p : ℝ) :
    (clusterCoverageVariance (μ := μ) U p : ℝ) =
      Var[fun ω ↦ thresholdCount p (U 0 ω); μ]/(m : ℝ) := by
  unfold clusterCoverageVariance
  simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ (variance_nonneg _ _)]
  rw [inv_pow, Real.sq_sqrt (by positivity)]
  ring

/-- Coverage CDF limit derived from iid uniform-marginal clusters.
    The ranks can be any valid sequence whose normalized levels converge to p.
    No fixed-level or moving-count CLT is assumed as an input.
    The conclusion applies at every continuity point of the limiting Gaussian CDF. -/
theorem iid_cluster_coverage_cdf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m)
    (U : ℕ → Ω → Fin m → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ) (hident : ∀ j, IdentDistrib (U j) (U 0) μ μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (p : ℝ) (hp : p ∈ Ioo 0 1)
    (k : (n : ℕ) → Fin ((n+1)*m))
    (hkp : Tendsto (fun n ↦ (((k n).val+1 : ℕ) : ℝ)/(((n+1)*m : ℕ)+1)) atTop (nhds p))
    (x : ℝ) (hx : clusterCoverageVariance (μ := μ) U p ≠ 0 ∨ x ≠ 0) :
    Tendsto (fun n ↦ μ.real {ω | √(((n+1)*m : ℕ) : ℝ) *
      (sampleQuantile (pooledSample U (n+1) ω) (k n)-
        (((k n).val+1 : ℕ) : ℝ)/(((n+1)*m : ℕ)+1)) ≤ x}) atTop
      (nhds (cdf (gaussianReal 0 (clusterCoverageVariance (μ := μ) U p)) x)) := by
  classical
  let N : ℕ → ℕ := fun n ↦ (n+1)*m
  let pn : ℕ → ℝ := fun n ↦ (((k n).val+1 : ℕ) : ℝ)/(N n+1)
  have hNt : Tendsto N atTop atTop := by
    apply tendsto_atTop_mono (fun n ↦ show n ≤ N n from ?_) tendsto_id
    dsimp [N]
    nlinarith
  have hnreal : Tendsto (fun n ↦ (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hNt
  have hi : Tendsto (fun n ↦ (√(N n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hnreal)
  let t : ℕ → ℝ := fun n ↦ pn n+x/√(N n : ℝ)
  have htp : Tendsto t atTop (nhds p) := by
    have hh := hkp.add (hi.const_mul x)
    simpa only [mul_zero, add_zero, ← div_eq_mul_inv] using hh
  let ν := gaussianReal 0 Var[fun ω ↦ thresholdCount p (U 0 ω); μ].toNNReal
  have hZ : HasLaw (id : ℝ → ℝ) ν ν := HasLaw.id
  have hc := iid_pooled_moving_count_clt U hU hindep hident hunif p hp t htp id hZ
  have hg : HasLaw (fun z : ℝ ↦ (√(m : ℝ))⁻¹*z)
      (gaussianReal 0 (clusterCoverageVariance (μ := μ) U p)) ν := by
    have hh := gaussianReal_const_mul hZ (√(m : ℝ))⁻¹
    simpa only [mul_zero, id_eq, clusterCoverageVariance, ν] using hh
  have hr := coverage_probability_limit_of_gaussian_count_limit N
    (fun n i ω ↦ pooledSample U (n+1) ω i) k hNt id monotone_id x
    (fun z : ℝ ↦ (√(m : ℝ))⁻¹*z) (clusterCoverageVariance (μ := μ) U p)
    hc hg hx
  simpa only [id_eq] using hr

/-- Coverage CLT in CDF form for iid clusters with a common continuous marginal.
    The input rank levels converge to an interior target. All count-limit steps are derived.
    The zero-variance Gaussian is included at its continuity points. -/
theorem iid_continuous_score_coverage_cdf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m)
    (S : ℕ → Ω → Fin m → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (hident : ∀ j, IdentDistrib (S j) (S 0) μ μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i z, μ.real {ω | S j ω i ≤ z} = F z)
    (p : ℝ) (hp : p ∈ Ioo 0 1)
    (k : (n : ℕ) → Fin ((n+1)*m))
    (hkp : Tendsto (fun n ↦ (((k n).val+1 : ℕ) : ℝ)/(((n+1)*m : ℕ)+1)) atTop (nhds p))
    (x : ℝ)
    (hx : clusterCoverageVariance (μ := μ) (fun j ω i ↦ F (S j ω i)) p ≠ 0 ∨ x ≠ 0) :
    Tendsto (fun n ↦ μ.real {ω | √(((n+1)*m : ℕ) : ℝ) *
      (F (sampleQuantile (pooledSample S (n+1) ω) (k n))-
        (((k n).val+1 : ℕ) : ℝ)/(((n+1)*m : ℕ)+1)) ≤ x}) atTop
      (nhds (cdf (gaussianReal 0
        (clusterCoverageVariance (μ := μ) (fun j ω i ↦ F (S j ω i)) p)) x)) := by
  let T : (Fin m → ℝ) → (Fin m → ℝ) := fun u i ↦ F (u i)
  have hT : Measurable T :=
    measurable_pi_lambda _ (fun i ↦ hF.measurable.comp (measurable_pi_apply i))
  have hunif (j : ℕ) (i : Fin m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      μ.real {ω | F (S j ω i) ≤ t} = t :=
    continuous_cdf_transform (fun ω ↦ S j ω i) F hF hmono h0 h1 (hCDF j i) t ht0 ht1
  have hc := iid_cluster_coverage_cdf hm (fun j ω i ↦ F (S j ω i))
    (fun j ↦ hT.comp (hS j)) (hindep.comp (fun _ ↦ T) (fun _ ↦ hT))
    (fun j ↦ (hident j).comp hT) hunif p hp k hkp x hx
  have he (n : ℕ) (ω : Ω) :
      sampleQuantile (pooledSample (fun j ω i ↦ F (S j ω i)) (n+1) ω) (k n) =
        F (sampleQuantile (pooledSample S (n+1) ω) (k n)) :=
    sampleQuantile_monotone_map (pooledSample S (n+1) ω) (k n) F hmono
  simpa only [he] using hc

/-- Equal pair probabilities give the paper's exceedance design-effect variance. -/
theorem clusterCoverageVariance_indicator_formula
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m) (U : ℕ → Ω → Fin m → ℝ) (hU : Measurable (U 0))
    (p δ : ℝ) (hp : p ∈ Ioo 0 1)
    (hmarg : ∀ i, μ.real {ω | U 0 ω i ≤ p} = p)
    (hpair : ∀ i j, i ≠ j → μ.real ({ω | U 0 ω i ≤ p} ∩ {ω | U 0 ω j ≤ p}) = δ) :
    (clusterCoverageVariance (μ := μ) U p : ℝ) =
      p*(1-p)*(1+((m : ℝ)-1)*((δ-p^2)/(p*(1-p)))) := by
  have hA (i : Fin m) : MeasurableSet {ω | U 0 ω i ≤ p} :=
    measurableSet_le ((measurable_pi_apply i).comp hU) measurable_const
  rw [clusterCoverageVariance_eq, thresholdCount_comp]
  rw [cluster_indicator_variance _ hA p δ hmarg hpair]
  simp only [Fintype.card_fin]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hp' : p ≠ 0 := hp.1.ne'
  have hp1 : 1-p ≠ 0 := by linarith [hp.2]
  field_simp

/-- The split-conformal ceiling convention implies convergence of the normalized rank.
    Only an eventual equality is needed, so empty or infinite initial cutoffs can be omitted. -/
theorem ceil_rank_levels_tendsto (N r : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (p : ℝ) (hp : 0 ≤ p)
    (hr : ∀ᶠ n in atTop, r n = Nat.ceil (((N n : ℝ)+1)*p)) :
    Tendsto (fun n ↦ (r n : ℝ)/((N n : ℝ)+1)) atTop (nhds p) := by
  have hn : Tendsto (fun n ↦ (N n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hN)
  have hi : Tendsto (fun n ↦ ((N n : ℝ)+1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hn
  have hu : Tendsto (fun n ↦ p+1/((N n : ℝ)+1)) atTop (nhds p) := by
    simpa only [one_div, add_zero] using hi.const_add p
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [hr] with n he
    rw [he, le_div_iff₀ (by positivity)]
    simpa only [mul_comm p] using Nat.le_ceil (((N n : ℝ)+1)*p)
  · filter_upwards [hr] with n he
    rw [he, div_le_iff₀ (by positivity)]
    have hh := Nat.ceil_lt_add_one (show 0 ≤ ((N n : ℝ)+1)*p by positivity)
    have hd : (p+1/((N n : ℝ)+1))*((N n : ℝ)+1) = p*((N n : ℝ)+1)+1 := by
      field_simp
    rw [hd]
    nlinarith

/-- The paper's ceiling-rank coverage limit, derived without a count-CLT hypothesis.
    Finite initial ranks may differ from the ceiling rule; they do not affect the limit. -/
theorem iid_continuous_score_ceil_coverage_cdf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m)
    (S : ℕ → Ω → Fin m → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (hident : ∀ j, IdentDistrib (S j) (S 0) μ μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i z, μ.real {ω | S j ω i ≤ z} = F z)
    (p : ℝ) (hp : p ∈ Ioo 0 1)
    (k : (n : ℕ) → Fin ((n+1)*m))
    (hceil : ∀ᶠ n in atTop, (k n).val+1 = Nat.ceil (((((n+1)*m : ℕ) : ℝ)+1)*p))
    (x : ℝ)
    (hx : clusterCoverageVariance (μ := μ) (fun j ω i ↦ F (S j ω i)) p ≠ 0 ∨ x ≠ 0) :
    Tendsto (fun n ↦ μ.real {ω | √(((n+1)*m : ℕ) : ℝ) *
      (F (sampleQuantile (pooledSample S (n+1) ω) (k n))-
        (((k n).val+1 : ℕ) : ℝ)/(((n+1)*m : ℕ)+1)) ≤ x}) atTop
      (nhds (cdf (gaussianReal 0
        (clusterCoverageVariance (μ := μ) (fun j ω i ↦ F (S j ω i)) p)) x)) := by
  have hN : Tendsto (fun n : ℕ ↦ (n+1)*m) atTop atTop := by
    apply tendsto_atTop_mono (fun n ↦ show n ≤ (n+1)*m from ?_) tendsto_id
    nlinarith
  exact iid_continuous_score_coverage_cdf hm S hS hindep hident F hF hmono h0 h1 hCDF
    p hp k (ceil_rank_levels_tendsto _ _ hN p hp.1.le hceil) x hx

end Exceedance
#print axioms Exceedance.clusterCoverageVariance_eq
#print axioms Exceedance.iid_cluster_coverage_cdf

#print axioms Exceedance.iid_continuous_score_coverage_cdf
#print axioms Exceedance.clusterCoverageVariance_indicator_formula

#print axioms Exceedance.ceil_rank_levels_tendsto
#print axioms Exceedance.iid_continuous_score_ceil_coverage_cdf
