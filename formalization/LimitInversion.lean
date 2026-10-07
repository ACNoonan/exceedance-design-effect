import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.CDF
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

/-- A distributional limit gives half-line probabilities at non-atomic cutoffs. -/
theorem probability_ge_tendsto_of_distribution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (h : TendstoInDistribution X atTop Z (fun _ ↦ μ) ν)
    (a : ℝ) (ha : ν {ω | Z ω = a} = 0) :
    Tendsto (fun n ↦ μ.real {ω | a ≤ X n ω}) atTop
      (nhds (ν.real {ω | a ≤ Z ω})) := by
  have hb : (ν.map Z) (frontier (Ici a)) = 0 := by
    rw [frontier_Ici, Measure.map_apply_of_aemeasurable h.aemeasurable_limit (measurableSet_singleton a)]
    exact ha
  have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    h.tendsto hb
  have hr := (ENNReal.tendsto_toReal (measure_ne_top (ν.map Z) (Ici a))).comp hp
  change Tendsto (fun n ↦ ((μ.map (X n)) (Ici a)).toReal) atTop
    (nhds (((ν.map Z) (Ici a)).toReal)) at hr
  have hm (n : ℕ) : ((μ.map (X n)) (Ici a)).toReal = μ.real {ω | a ≤ X n ω} := by
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) measurableSet_Ici]
    rfl
  have hz : ((ν.map Z) (Ici a)).toReal = ν.real {ω | a ≤ Z ω} := by
    rw [Measure.map_apply_of_aemeasurable h.aemeasurable_limit measurableSet_Ici]
    rfl
  simp_rw [hm, hz] at hr
  exact hr


/-- Moving deterministic cutoffs are allowed when they converge to a non-atomic cutoff. -/
theorem probability_ge_moving_tendsto
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (h : TendstoInDistribution X atTop Z (fun _ ↦ μ) ν)
    (a : ℕ → ℝ) (c : ℝ) (ha : Tendsto a atTop (nhds c))
    (hc : ν {ω | Z ω = c} = 0) :
    Tendsto (fun n ↦ μ.real {ω | a n ≤ X n ω}) atTop
      (nhds (ν.real {ω | c ≤ Z ω})) := by
  have hm : TendstoInMeasure μ (fun n (_ω : Ω) ↦ a n) atTop (fun _ ↦ c) :=
    tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
      (Filter.Eventually.of_forall (fun _ ↦ ha))
  have hs := h.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun (z : ℝ × ℝ) ↦ z.1-z.2) (by fun_prop) hm
    (fun _ ↦ aemeasurable_const)
  have hc' : ν {ω | Z ω-c = 0} = 0 := by simpa only [sub_eq_zero] using hc
  have ht := probability_ge_tendsto_of_distribution
    (fun n ω ↦ X n ω-a n) (fun ω ↦ Z ω-c) hs 0 hc'
  simpa only [sub_nonneg] using ht


/-- The reflected tail of a centered Gaussian is its CDF, including zero variance. -/
theorem centered_gaussian_reflected_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Ω → ℝ) (v : NNReal)
    (hZ : HasLaw Z (gaussianReal 0 v) μ) (x : ℝ) :
    μ.real {ω | -x ≤ Z ω} = cdf (gaussianReal 0 v) x := by
  have hn : HasLaw (-Z) (gaussianReal 0 v) μ := by
    simpa only [neg_zero] using gaussianReal_neg hZ
  have hh := hn.measureReal_eq (p := fun z : ℝ ↦ z ≤ x) measurableSet_Iic
  rw [cdf_eq_real]
  simpa only [Pi.neg_apply, neg_le, Set.Iic] using hh

/-- Every cutoff is non-atomic for positive Gaussian variance.
    For zero variance, only the cutoff at zero is excluded. -/
theorem centered_gaussian_no_atom_at_continuity {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Ω → ℝ) (v : NNReal)
    (hZ : HasLaw Z (gaussianReal 0 v) μ) (x : ℝ) (hx : v ≠ 0 ∨ x ≠ 0) :
    μ {ω | Z ω = -x} = 0 := by
  rw [hZ.measure_eq (p := fun z : ℝ ↦ z = -x) (measurableSet_singleton (-x))]
  by_cases hv : v = 0
  · subst v
    have hx' : x ≠ 0 := hx.resolve_left (not_not_intro rfl)
    simp [hx']
  · letI := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) hv
    exact measure_singleton _

end Exceedance
#print axioms Exceedance.probability_ge_tendsto_of_distribution
#print axioms Exceedance.probability_ge_moving_tendsto

#print axioms Exceedance.centered_gaussian_reflected_tail
#print axioms Exceedance.centered_gaussian_no_atom_at_continuity
