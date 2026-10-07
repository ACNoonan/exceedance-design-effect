import CountInversion
import LimitInversion
import ProbabilityTransform
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

/-- Count inversion transfers a moving-threshold count limit to a coverage CDF limit.
    This is the exact finite-sample bridge. Establishing its count-limit hypothesis for
    the independent-cluster model is a separate step. -/
theorem quantile_cdf_limit_of_count_limit
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (N : ℕ → ℕ) (U : (n : ℕ) → Fin (N n) → Ω → ℝ)
    (k : (n : ℕ) → Fin (N n)) (p s : ℕ → ℝ) (hs : ∀ n, 0 < s n)
    (x c : ℝ) (Z : Ω' → ℝ)
    (hcount : TendstoInDistribution
      (fun n ω ↦ (((Finset.univ.filter (fun i ↦ U n i ω ≤ p n+x/s n)).card : ℝ) -
        (N n : ℝ)*(p n+x/s n))/s n) atTop Z (fun _ ↦ μ) ν)
    (hcut : Tendsto (fun n ↦ (((k n).val+1 : ℕ) -
      (N n : ℝ)*(p n+x/s n))/s n) atTop (nhds c))
    (hZ : ν {ω | Z ω = c} = 0) :
    Tendsto (fun n ↦ μ.real {ω | s n * (sampleQuantile (fun i ↦ U n i ω) (k n)-p n) ≤ x})
      atTop (nhds (ν.real {ω | c ≤ Z ω})) := by
  classical
  have ht := probability_ge_moving_tendsto _ Z hcount _ c hcut hZ
  have he (n : ℕ) :
      {ω | s n * (sampleQuantile (fun i ↦ U n i ω) (k n)-p n) ≤ x} =
      {ω | (((k n).val+1 : ℕ) - (N n : ℝ)*(p n+x/s n))/s n ≤
        (((Finset.univ.filter (fun i ↦ U n i ω ≤ p n+x/s n)).card : ℝ) -
          (N n : ℝ)*(p n+x/s n))/s n} := by
    ext ω
    simp only [mem_setOf_eq]
    have hq : s n * (sampleQuantile (fun i ↦ U n i ω) (k n)-p n) ≤ x ↔
        sampleQuantile (fun i ↦ U n i ω) (k n) ≤ p n+x/s n := by
      rw [mul_comm, ← le_div_iff₀ (hs n), sub_le_iff_le_add, add_comm (x/s n)]
    rw [hq, sampleQuantile_le_iff, div_le_div_iff_of_pos_right (hs n), sub_le_sub_iff_right]
    exact_mod_cast Iff.rfl
  simpa only [← he] using ht

/-- The split-conformal rank offset in the count inversion formula is exact. -/
theorem coverage_rank_cutoff_identity (N k : ℕ) (hN : 0 < N) (x : ℝ) :
    ((k : ℝ) - (N : ℝ)*((k : ℝ)/(N+1)+x/√(N : ℝ)))/√(N : ℝ) =
      ((k : ℝ)/(N+1))/√(N : ℝ)-x := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : (√(N : ℝ))^2 = N := Real.sq_sqrt hn.le
  have hsn : √(N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
  have hnp : (N : ℝ)+1 ≠ 0 := by positivity
  field_simp
  linear_combination ((N : ℝ)+1)*x*hs


/-- Under the split-conformal centering, the moving count cutoff tends to -x. -/
theorem coverage_rank_cutoff_tendsto
    (N k : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hkt : ∀ n, k n ≤ N n+1) (hNt : Tendsto N atTop atTop) (x : ℝ) :
    Tendsto (fun n ↦ ((k n : ℝ) - (N n : ℝ)*
      ((k n : ℝ)/(N n+1)+x/√(N n : ℝ)))/√(N n : ℝ)) atTop (nhds (-x)) := by
  have hreal : Tendsto (fun n ↦ (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hNt
  have hinv : Tendsto (fun n ↦ (√(N n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hreal)
  have hsmall : Tendsto (fun n ↦ ((k n : ℝ)/(N n+1))/√(N n : ℝ)) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv
    · intro n
      positivity
    · intro n
      have hp : (k n : ℝ)/(N n+1) ≤ 1 := by
        apply (div_le_one (by positivity)).2
        exact_mod_cast hkt n
      calc
        _ ≤ 1/√(N n : ℝ) := div_le_div_of_nonneg_right hp (Real.sqrt_nonneg _)
        _ = _ := one_div _
  have he : (fun n ↦ ((k n : ℝ) - (N n : ℝ)*
      ((k n : ℝ)/(N n+1)+x/√(N n : ℝ)))/√(N n : ℝ)) =
      (fun n ↦ ((k n : ℝ)/(N n+1))/√(N n : ℝ)-x) := by
    funext n
    exact coverage_rank_cutoff_identity (N n) (k n) (hN n) x
  rw [he]
  simpa only [zero_sub] using hsmall.sub_const x


/-- Coverage probabilities follow from the transformed moving-count CLT.
    This combines the actual sample quantile, CDF transformation, rank centering,
    and moving-cutoff limit. The independent-cluster count limit remains an explicit hypothesis. -/
theorem coverage_probability_limit_of_transformed_count_limit
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (N : ℕ → ℕ) (S : (n : ℕ) → Fin (N n) → Ω → ℝ)
    (k : (n : ℕ) → Fin (N n)) (hNt : Tendsto N atTop atTop)
    (F : ℝ → ℝ) (hmono : Monotone F) (x : ℝ) (Z : Ω' → ℝ)
    (hcount : TendstoInDistribution
      (fun n ω ↦ (((Finset.univ.filter (fun i ↦ F (S n i ω) ≤
        (((k n).val+1 : ℕ) : ℝ)/(N n+1)+x/√(N n : ℝ))).card : ℝ) -
        (N n : ℝ)*((((k n).val+1 : ℕ) : ℝ)/(N n+1)+x/√(N n : ℝ)))/√(N n : ℝ))
      atTop Z (fun _ ↦ μ) ν)
    (hZ : ν {ω | Z ω = -x} = 0) :
    Tendsto (fun n ↦ μ.real {ω | √(N n : ℝ) *
      (F (sampleQuantile (fun i ↦ S n i ω) (k n)) -
        (((k n).val+1 : ℕ) : ℝ)/(N n+1)) ≤ x})
      atTop (nhds (ν.real {ω | -x ≤ Z ω})) := by
  classical
  have hn (n : ℕ) : 0 < N n := (Nat.zero_le _).trans_lt (k n).isLt
  have hs (n : ℕ) : 0 < √(N n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn n)
  have hk (n : ℕ) : (k n).val+1 ≤ N n+1 := Nat.succ_le_succ (Nat.le_of_lt (k n).isLt)
  have ht := quantile_cdf_limit_of_count_limit N (fun n i ω ↦ F (S n i ω)) k
    (fun n ↦ (((k n).val+1 : ℕ) : ℝ)/(N n+1)) (fun n ↦ √(N n : ℝ)) hs x (-x) Z hcount
    (coverage_rank_cutoff_tendsto N (fun n ↦ (k n).val+1) hn hk hNt x) hZ
  have he (n : ℕ) (ω : Ω) :
      sampleQuantile (fun i ↦ F (S n i ω)) (k n) =
      F (sampleQuantile (fun i ↦ S n i ω) (k n)) :=
    sampleQuantile_monotone_map (fun i ↦ S n i ω) (k n) F hmono
  simpa only [he] using ht


/-- Gaussian coverage CDF at all continuity points, conditional on the moving-count CLT.
    The zero-variance case excludes x=0 because its limit CDF jumps there. -/
theorem coverage_probability_limit_of_gaussian_count_limit
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (N : ℕ → ℕ) (S : (n : ℕ) → Fin (N n) → Ω → ℝ)
    (k : (n : ℕ) → Fin (N n)) (hNt : Tendsto N atTop atTop)
    (F : ℝ → ℝ) (hmono : Monotone F) (x : ℝ) (Z : Ω' → ℝ) (v : NNReal)
    (hcount : TendstoInDistribution
      (fun n ω ↦ (((Finset.univ.filter (fun i ↦ F (S n i ω) ≤
        (((k n).val+1 : ℕ) : ℝ)/(N n+1)+x/√(N n : ℝ))).card : ℝ) -
        (N n : ℝ)*((((k n).val+1 : ℕ) : ℝ)/(N n+1)+x/√(N n : ℝ)))/√(N n : ℝ))
      atTop Z (fun _ ↦ μ) ν)
    (hgauss : HasLaw Z (gaussianReal 0 v) ν) (hx : v ≠ 0 ∨ x ≠ 0) :
    Tendsto (fun n ↦ μ.real {ω | √(N n : ℝ) *
      (F (sampleQuantile (fun i ↦ S n i ω) (k n)) -
        (((k n).val+1 : ℕ) : ℝ)/(N n+1)) ≤ x})
      atTop (nhds (cdf (gaussianReal 0 v) x)) := by
  have ht := coverage_probability_limit_of_transformed_count_limit N S k hNt F hmono x Z
    hcount (centered_gaussian_no_atom_at_continuity Z v hgauss x hx)
  rw [centered_gaussian_reflected_tail Z v hgauss x] at ht
  exact ht

end Exceedance
#print axioms Exceedance.quantile_cdf_limit_of_count_limit
#print axioms Exceedance.coverage_rank_cutoff_identity

#print axioms Exceedance.coverage_rank_cutoff_tendsto

#print axioms Exceedance.coverage_probability_limit_of_transformed_count_limit

#print axioms Exceedance.coverage_probability_limit_of_gaussian_count_limit
