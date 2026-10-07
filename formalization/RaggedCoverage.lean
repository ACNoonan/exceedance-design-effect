import RaggedQuantileConcentration
import QuantileMoments

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

noncomputable def normalizedRaggedQuantile {Ω : Type*} {b : ℕ} (m : Fin b → ℕ)
    (U : (j : Fin b) → Ω → Fin (m j) → ℝ) (k : Fin (raggedSize m)) (ω : Ω) : ℝ :=
  Real.sqrt (raggedSize m) * (sampleQuantile (raggedSample m U ω) k -
    (k.val+1 : ℝ)/((raggedSize m : ℝ)+1))

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma measurable_normalizedRaggedQuantile {b : ℕ} (m : Fin b → ℕ)
    (U : (j : Fin b) → Ω → Fin (m j) → ℝ) (hU : ∀ j, Measurable (U j))
    (k : Fin (raggedSize m)) : Measurable (normalizedRaggedQuantile m U k) := by
  have hq : Measurable (fun ω ↦ sampleQuantile (raggedSample m U ω) k) :=
    measurable_sampleQuantile _ (fun _ ↦ (measurable_pi_apply _).comp (hU _)) k
  exact (hq.sub_const _).const_mul _

lemma normalizedRaggedQuantile_memLp {b : ℕ} (m : Fin b → ℕ)
    (U : (j : Fin b) → Ω → Fin (m j) → ℝ) (hU : ∀ j, Measurable (U j))
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (k : Fin (raggedSize m)) : MemLp (normalizedRaggedQuantile m U k) 2 μ := by
  have hq : Measurable (fun ω ↦ sampleQuantile (raggedSample m U ω) k) :=
    measurable_sampleQuantile _ (fun _ ↦ (measurable_pi_apply _).comp (hU _)) k
  exact ((memLp_of_bounded (ragged_quantile_support m U hU hunif k) hq.aestronglyMeasurable 2).sub
    (memLp_const _)).const_mul _

/-- A common upper bound on cluster sizes gives a common Gaussian tail bound. -/
theorem ragged_normalized_quantile_tail {b : ℕ} (m : Fin b → ℕ)
    (U : (j : Fin b) → Ω → Fin (m j) → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (M : ℝ) (hM : 0 < M) (hm : ∀ j, (m j : ℝ) ≤ M)
    (k : Fin (raggedSize m)) (y : ℝ) (hy : 0 ≤ y) :
    μ.real {ω | y < |normalizedRaggedQuantile m U k ω|} ≤ 2*Real.exp (-2*y^2/M) := by
  let N : ℝ := raggedSize m
  let S : ℝ := ∑ j, (m j : ℝ)^2
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  have hNS : N ≤ S := by
    dsimp [N,S]
    rw [raggedSize_eq_sum, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro j _
    exact_mod_cast (show m j ≤ (m j)^2 by simpa [pow_two] using Nat.le_mul_self (m j))
  have hS : 0 < S := hN.trans_le hNS
  have hSM : S ≤ M*N := by
    dsimp [N,S]
    rw [raggedSize_eq_sum, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    nlinarith [hm j, Nat.cast_nonneg (α := ℝ) (m j)]
  have hs := Real.sqrt_pos.mpr hN
  have hsq := Real.sq_sqrt hN.le
  have ht := ragged_quantile_tail m U hU hindep hunif k (y/Real.sqrt N) (div_nonneg hy hs.le)
  have he : {ω | y < |normalizedRaggedQuantile m U k ω|} =
      {ω | y/Real.sqrt N < |sampleQuantile (raggedSample m U ω) k -
        ((k.val+1 : ℕ) : ℝ)/(N+1)|} := by
    ext ω
    simp only [normalizedRaggedQuantile, Nat.cast_add, Nat.cast_one, mem_setOf_eq]
    change y < |Real.sqrt N * (sampleQuantile (raggedSample m U ω) k - (k.val+1 : ℝ)/(N+1))| ↔
      y/Real.sqrt N < |sampleQuantile (raggedSample m U ω) k - (k.val+1 : ℝ)/(N+1)|
    simp only [abs_mul, abs_of_pos hs, div_lt_iff₀ hs]
    rw [mul_comm (Real.sqrt _)]
  rw [he]
  have hexp : -2*N^2*(y/Real.sqrt N)^2/S = -2*N*y^2/S := by
    rw [div_pow, hsq]
    field_simp
  change μ.real _ ≤ 2*Real.exp (-2*N^2*(y/Real.sqrt N)^2/S) at ht
  rw [hexp] at ht
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  apply (div_le_div_iff₀ hS hM).mpr
  nlinarith [mul_le_mul_of_nonneg_right hSM (sq_nonneg y)]

/-- Uniform integrability for arbitrary arrays with a common bound on cluster sizes. -/
theorem ragged_coverage_square_uniformIntegrable
    (b : ℕ → ℕ) (m : (n : ℕ) → Fin (b n) → ℕ)
    (U : (n : ℕ) → (j : Fin (b n)) → Ω → Fin (m n j) → ℝ)
    (hU : ∀ n j, Measurable (U n j)) (hindep : ∀ n, iIndepFun (U n) μ)
    (hunif : ∀ n j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U n j ω i ≤ t} = t)
    (M : ℝ) (hM : 0 < M) (hm : ∀ n j, (m n j : ℝ) ≤ M)
    (k : ∀ n, Fin (raggedSize (m n))) :
    UniformIntegrable (fun n ω ↦ (normalizedRaggedQuantile (m n) (U n) (k n) ω)^2) 1 μ := by
  apply uniformIntegrable_of_exponential_tail _
    (fun n ↦ (measurable_normalizedRaggedQuantile (m n) (U n) (hU n) (k n)).pow_const 2)
    (fun n ↦ (normalizedRaggedQuantile_memLp (m n) (U n) (hU n) (hunif n) (k n)).integrable_sq)
    (fun _ _ ↦ sq_nonneg _) 2 (2/M) (by positivity)
  intro n t ht
  exact gaussian_tail_square_tail _ M
    (ragged_normalized_quantile_tail (m n) (U n) (hU n) (hindep n) (hunif n) M hM (hm n) (k n)) t ht

/-- The unequal-size concentration bound on the true continuous-CDF coverage scale. -/
theorem ragged_continuous_score_coverage_tail {b : ℕ} (m : Fin b → ℕ)
    (S : (j : Fin b) → Ω → Fin (m j) → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i t, μ.real {ω | S j ω i ≤ t} = F t)
    (k : Fin (raggedSize m)) (x : ℝ) (hx : 0 ≤ x) :
    μ.real {ω | x < |F (sampleQuantile (raggedSample m S ω) k) -
      (k.val+1 : ℝ)/((raggedSize m : ℝ)+1)|} ≤
      2*Real.exp (-2*(raggedSize m : ℝ)^2*x^2/(∑ j, (m j : ℝ)^2)) := by
  let T := fun j (u : Fin (m j) → ℝ) i ↦ F (u i)
  have hT (j : Fin b) : Measurable (T j) :=
    measurable_pi_lambda _ (fun i ↦ hF.measurable.comp (measurable_pi_apply i))
  let U := fun j ω i ↦ F (S j ω i)
  have hU (j : Fin b) : Measurable (U j) := (hT j).comp (hS j)
  have hi : iIndepFun U μ := hindep.comp T hT
  have hu : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t := by
    intro j i t ht0 ht1
    exact continuous_cdf_transform (fun ω ↦ S j ω i) F hF hmono h0 h1 (hCDF j i) t ht0 ht1
  have ht := ragged_quantile_tail m U hU hi hu k x hx
  have he (ω : Ω) : sampleQuantile (raggedSample m U ω) k =
      F (sampleQuantile (raggedSample m S ω) k) :=
    sampleQuantile_monotone_map (raggedSample m S ω) k F hmono
  simpa only [he, Nat.cast_add, Nat.cast_one] using ht

/-- Uniform integrability for bounded unequal clusters on the original continuous-CDF scale. -/
theorem ragged_continuous_score_coverage_square_uniformIntegrable
    (b : ℕ → ℕ) (m : (n : ℕ) → Fin (b n) → ℕ)
    (S : (n : ℕ) → (j : Fin (b n)) → Ω → Fin (m n j) → ℝ)
    (hS : ∀ n j, Measurable (S n j)) (hindep : ∀ n, iIndepFun (S n) μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ n j i t, μ.real {ω | S n j ω i ≤ t} = F t)
    (M : ℝ) (hM : 0 < M) (hm : ∀ n j, (m n j : ℝ) ≤ M)
    (k : ∀ n, Fin (raggedSize (m n))) :
    UniformIntegrable (fun n ω ↦ (Real.sqrt (raggedSize (m n)) *
      (F (sampleQuantile (raggedSample (m n) (S n) ω) (k n)) -
        ((k n).val+1 : ℝ)/((raggedSize (m n) : ℝ)+1)))^2) 1 μ := by
  let T := fun n j (u : Fin (m n j) → ℝ) i ↦ F (u i)
  have hT (n : ℕ) (j : Fin (b n)) : Measurable (T n j) :=
    measurable_pi_lambda _ (fun i ↦ hF.measurable.comp (measurable_pi_apply i))
  let U := fun n j ω i ↦ F (S n j ω i)
  have hU (n : ℕ) (j : Fin (b n)) : Measurable (U n j) := (hT n j).comp (hS n j)
  have hi (n : ℕ) : iIndepFun (U n) μ := (hindep n).comp (T n) (hT n)
  have hu : ∀ n j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U n j ω i ≤ t} = t := by
    intro n j i t ht0 ht1
    exact continuous_cdf_transform (fun ω ↦ S n j ω i) F hF hmono h0 h1 (hCDF n j i) t ht0 ht1
  have ht := ragged_coverage_square_uniformIntegrable b m U hU hi hu M hM hm k
  have he (n : ℕ) (ω : Ω) : sampleQuantile (raggedSample (m n) (U n) ω) (k n) =
      F (sampleQuantile (raggedSample (m n) (S n) ω) (k n)) :=
    sampleQuantile_monotone_map (raggedSample (m n) (S n) ω) (k n) F hmono
  simpa only [normalizedRaggedQuantile, he] using ht

end Exceedance
#print axioms Exceedance.ragged_normalized_quantile_tail
#print axioms Exceedance.ragged_coverage_square_uniformIntegrable
#print axioms Exceedance.ragged_continuous_score_coverage_tail

#print axioms Exceedance.ragged_continuous_score_coverage_square_uniformIntegrable
