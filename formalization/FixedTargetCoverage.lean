import BahadurRepresentation

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

theorem iid_cluster_fixed_target_cdf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m)
    (U : ℕ → Ω → Fin m → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ) (hident : ∀ j, IdentDistrib (U j) (U 0) μ μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (p : ℝ) (hp : p ∈ Ioo 0 1)
    (k : (n : ℕ) → Fin ((n+1)*m))
    (hceil : ∀ᶠ n in atTop, (k n).val+1 = Nat.ceil (((((n+1)*m:ℕ):ℝ)+1)*p))
    (x : ℝ) (hx : clusterCoverageVariance (μ := μ) U p ≠ 0 ∨ x ≠ 0) :
    Tendsto (fun n ↦ μ.real {ω | √(((n+1)*m : ℕ) : ℝ) *
      (sampleQuantile (pooledSample U (n+1) ω) (k n)-
        p) ≤ x}) atTop
      (nhds (cdf (gaussianReal 0 (clusterCoverageVariance (μ := μ) U p)) x)) := by
  classical
  let N : ℕ → ℕ := fun n ↦ (n+1)*m
  have hNt : Tendsto N atTop atTop := by
    apply tendsto_atTop_mono (fun n ↦ show n ≤ N n from ?_) tendsto_id
    dsimp [N]
    nlinarith
  have hnreal : Tendsto (fun n ↦ (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hNt
  have hi : Tendsto (fun n ↦ (√(N n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hnreal)
  let t : ℕ → ℝ := fun n ↦ p+x/√(N n : ℝ)
  have htp : Tendsto t atTop (nhds p) := by
    have hh := (hi.const_mul x).const_add p
    simpa only [mul_zero, add_zero, ← div_eq_mul_inv] using hh
  let ν := gaussianReal 0 Var[fun ω ↦ thresholdCount p (U 0 ω); μ].toNNReal
  have hZ : HasLaw (id : ℝ → ℝ) ν ν := HasLaw.id
  have hc := iid_pooled_moving_count_clt U hU hindep hident hunif p hp t htp id hZ
  have hg : HasLaw (fun z : ℝ ↦ (√(m : ℝ))⁻¹*z)
      (gaussianReal 0 (clusterCoverageVariance (μ := μ) U p)) ν := by
    have hh := gaussianReal_const_mul hZ (√(m : ℝ))⁻¹
    simpa only [mul_zero, id_eq, clusterCoverageVariance, ν] using hh
  have hz := ceil_rank_count_centering m p hp (fun n ↦ (k n).val+1) hceil
  have hz' : Tendsto (fun n ↦ (((k n).val+1:ℕ)-(N n:ℝ)*p)/√(N n:ℝ)) atTop (nhds 0) := by
    have hh := hz.div_const (Real.sqrt (m:ℝ))
    simp only [zero_div] at hh
    convert hh using 1
    funext n
    dsimp [N]
    rw [Nat.cast_mul,Real.sqrt_mul (by positivity : (0:ℝ)≤((n+1:ℕ):ℝ))]
    push_cast
    ring
  have hcut : Tendsto (fun n ↦ (((k n).val+1:ℕ)-(N n:ℝ)*(p+x/√(N n:ℝ)))/√(N n:ℝ))
      atTop (nhds (-x)) := by
    have hh := hz'.sub_const x
    simp only [zero_sub] at hh
    apply hh.congr'
    exact Eventually.of_forall (fun n ↦ by
      have hn : (0:ℝ)<N n := by dsimp [N]; positivity
      have hs : √(N n:ℝ)≠0 := (Real.sqrt_pos.mpr hn).ne'
      field_simp
      linear_combination -x*(Real.sq_sqrt hn.le))
  have hr := quantile_cdf_limit_of_count_limit N
    (fun n i ω ↦ pooledSample U (n+1) ω i) k (fun _ ↦ p) (fun n ↦ √(N n:ℝ))
    (fun n ↦ Real.sqrt_pos.mpr (by dsimp [N]; positivity)) x (-x)
    (fun z : ℝ ↦ (√(m:ℝ))⁻¹*z) hc hcut (centered_gaussian_no_atom_at_continuity _ _ hg x hx)
  rw [centered_gaussian_reflected_tail _ _ hg x] at hr
  exact hr

/-- Coverage CLT in CDF form for iid clusters with a common continuous marginal.
    The input rank levels converge to an interior target. All count-limit steps are derived.
    The zero-variance Gaussian is included at its continuity points. -/
theorem iid_continuous_score_fixed_target_cdf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m)
    (S : ℕ → Ω → Fin m → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (hident : ∀ j, IdentDistrib (S j) (S 0) μ μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i z, μ.real {ω | S j ω i ≤ z} = F z)
    (p : ℝ) (hp : p ∈ Ioo 0 1)
    (k : (n : ℕ) → Fin ((n+1)*m))
    (hceil : ∀ᶠ n in atTop, (k n).val+1 = Nat.ceil (((((n+1)*m:ℕ):ℝ)+1)*p))
    (x : ℝ)
    (hx : clusterCoverageVariance (μ := μ) (fun j ω i ↦ F (S j ω i)) p ≠ 0 ∨ x ≠ 0) :
    Tendsto (fun n ↦ μ.real {ω | √(((n+1)*m : ℕ) : ℝ) *
      (F (sampleQuantile (pooledSample S (n+1) ω) (k n))-
        p) ≤ x}) atTop
      (nhds (cdf (gaussianReal 0
        (clusterCoverageVariance (μ := μ) (fun j ω i ↦ F (S j ω i)) p)) x)) := by
  let T : (Fin m → ℝ) → (Fin m → ℝ) := fun u i ↦ F (u i)
  have hT : Measurable T :=
    measurable_pi_lambda _ (fun i ↦ hF.measurable.comp (measurable_pi_apply i))
  have hunif (j : ℕ) (i : Fin m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      μ.real {ω | F (S j ω i) ≤ t} = t :=
    continuous_cdf_transform (fun ω ↦ S j ω i) F hF hmono h0 h1 (hCDF j i) t ht0 ht1
  have hc := iid_cluster_fixed_target_cdf hm (fun j ω i ↦ F (S j ω i))
    (fun j ↦ hT.comp (hS j)) (hindep.comp (fun _ ↦ T) (fun _ ↦ hT))
    (fun j ↦ (hident j).comp hT) hunif p hp k hceil x hx
  have he (n : ℕ) (ω : Ω) :
      sampleQuantile (pooledSample (fun j ω i ↦ F (S j ω i)) (n+1) ω) (k n) =
        F (sampleQuantile (pooledSample S (n+1) ω) (k n)) :=
    sampleQuantile_monotone_map (pooledSample S (n+1) ω) (k n) F hmono
  simpa only [he] using hc


end Exceedance
#print axioms Exceedance.iid_continuous_score_fixed_target_cdf
