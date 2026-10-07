import CoverageMoments

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

/-- A valid finite rank at every nonempty sample size; it agrees with the ceiling rank eventually. -/
noncomputable def clampedCeilRank (m : ℕ) (hm : 0 < m) (p : ℝ) (n : ℕ) : Fin ((n+1)*m) :=
  ⟨min (⌈((((n+1)*m : ℕ) : ℝ)+1)*p⌉₊-1) ((n+1)*m-1), by
    have hn : 0 < (n+1)*m := Nat.mul_pos (Nat.succ_pos _) hm
    exact lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hn (by decide))⟩

lemma eventually_valid_ceil_rank (m : ℕ) (hm : 0 < m) (p : ℝ) (hp : p ∈ Ioo 0 1) :
    ∀ᶠ n : ℕ in atTop, 0 < ⌈((((n+1)*m : ℕ) : ℝ)+1)*p⌉₊ ∧
      ⌈((((n+1)*m : ℕ) : ℝ)+1)*p⌉₊ ≤ (n+1)*m := by
  have hN : Tendsto (fun n : ℕ ↦ (((n+1)*m : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    apply tendsto_atTop_mono (fun n ↦ ?_) (tendsto_add_atTop_nat 1)
    exact Nat.le_mul_of_pos_right _ hm
  filter_upwards [hN.eventually (eventually_ge_atTop (p/(1-p)))] with n hn
  constructor
  · apply Nat.ceil_pos.mpr
    exact mul_pos (by positivity) hp.1
  · apply Nat.ceil_le.mpr
    have hh := (div_le_iff₀ (by linarith [hp.2] : 0 < 1-p)).mp hn
    nlinarith

lemma clampedCeilRank_eventually (m : ℕ) (hm : 0 < m) (p : ℝ) (hp : p ∈ Ioo 0 1) :
    ∀ᶠ n : ℕ in atTop, (clampedCeilRank m hm p n).val+1 =
      ⌈((((n+1)*m : ℕ) : ℝ)+1)*p⌉₊ := by
  filter_upwards [eventually_valid_ceil_rank m hm p hp] with n hn
  simp only [clampedCeilRank]
  omega

/-- Coverage of the ceiling-rule cutoff. The value 1 represents the infinite cutoff. -/
noncomputable def ceilingRuleCoverage {Ω : Type*} (m : ℕ) (hm : 0 < m) (p : ℝ)
    (S : ℕ → Ω → Fin m → ℝ) (F : ℝ → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  if ⌈((((n+1)*m : ℕ) : ℝ)+1)*p⌉₊ ≤ (n+1)*m then
    F (sampleQuantile (pooledSample S (n+1) ω) (clampedCeilRank m hm p n))
  else 1

/-- Exceptional initial infinite cutoffs change no eventual finite-sample coverage function. -/
theorem ceilingRuleCoverage_eventually_eq {Ω : Type*}
    (m : ℕ) (hm : 0 < m) (p : ℝ) (hp : p ∈ Ioo 0 1)
    (S : ℕ → Ω → Fin m → ℝ) (F : ℝ → ℝ) :
    ∀ᶠ n in atTop, ceilingRuleCoverage m hm p S F n =
      (fun ω ↦ F (sampleQuantile (pooledSample S (n+1) ω) (clampedCeilRank m hm p n))) := by
  filter_upwards [eventually_valid_ceil_rank m hm p hp] with n hn
  funext ω
  exact if_pos hn.2

/-- Any rescaled variance limit transfers to the true ceiling policy, including its initial infinite cutoffs. -/
theorem ceilingRuleCoverage_variance_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : ℕ) (hm : 0 < m) (p : ℝ) (hp : p ∈ Ioo 0 1)
    (S : ℕ → Ω → Fin m → ℝ) (F : ℝ → ℝ) (v : ℝ)
    (hv : Tendsto (fun n : ℕ ↦ (((n+1)*m : ℕ) : ℝ)*
      Var[fun ω ↦ F (sampleQuantile (pooledSample S (n+1) ω) (clampedCeilRank m hm p n)); μ])
      atTop (nhds v)) :
    Tendsto (fun n : ℕ ↦ (((n+1)*m : ℕ) : ℝ)*
      Var[ceilingRuleCoverage m hm p S F n; μ]) atTop (nhds v) := by
  apply hv.congr'
  filter_upwards [ceilingRuleCoverage_eventually_eq m hm p hp S F] with n hn
  rw [hn]

/-- The central variance theorem also covers the exact ceiling policy at every initial sample size. -/
theorem iid_ceilingRuleCoverage_variance_limit {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m)
    (S : ℕ → Ω → Fin m → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (hident : ∀ j, IdentDistrib (S j) (S 0) μ μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i z, μ.real {ω | S j ω i ≤ z} = F z)
    (p : ℝ) (hp : p ∈ Ioo 0 1) :
    Tendsto (fun n : ℕ ↦ (((n+1)*m : ℕ) : ℝ)*
      Var[ceilingRuleCoverage m hm p S F n; μ]) atTop
      (nhds (clusterCoverageVariance (μ := μ) (fun j ω i ↦ F (S j ω i)) p : ℝ)) := by
  apply ceilingRuleCoverage_variance_limit μ m hm p hp S F
  exact iid_continuous_score_ceil_coverage_variance_limit hm S hS hindep hident
    F hF hmono h0 h1 hCDF p hp (clampedCeilRank m hm p)
    (clampedCeilRank_eventually m hm p hp)

end Exceedance
#print axioms Exceedance.clampedCeilRank_eventually
#print axioms Exceedance.ceilingRuleCoverage_eventually_eq
#print axioms Exceedance.ceilingRuleCoverage_variance_limit

#print axioms Exceedance.iid_ceilingRuleCoverage_variance_limit
