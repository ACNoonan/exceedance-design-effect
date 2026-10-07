import RaggedCoverage

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

/-- The prescribed correction uses the actual sum of squared cluster sizes. -/
noncomputable def clusterCorrection {b : ℕ} (m : Fin b → ℕ) (eta : ℝ) : ℝ :=
  Real.sqrt ((∑ j, (m j : ℝ)^2)*Real.log (1/eta)/(2*(raggedSize m : ℝ)^2))

/-- A finite corrected rank, or coverage one for the infinite cutoff. -/
noncomputable def correctedCoverage {Ω : Type*} {b : ℕ} (m : Fin b → ℕ)
    (S : (j : Fin b) → Ω → Fin (m j) → ℝ) (F : ℝ → ℝ) (p eta : ℝ) (ω : Ω) : ℝ :=
  let r := ⌈((raggedSize m : ℝ)+1)*(p+clusterCorrection m eta)⌉₊
  if h : 0 < r ∧ r ≤ raggedSize m then
    F (sampleQuantile (raggedSample m S ω) ⟨r-1, by omega⟩)
  else 1

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A one-sided count bound for any finite rank above the corrected target. -/
theorem ragged_quantile_undercoverage {b : ℕ} (m : Fin b → ℕ)
    (U : (j : Fin b) → Ω → Fin (m j) → ℝ)
    (hU : ∀ j, Measurable (U j)) (hindep : iIndepFun U μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (k : Fin (raggedSize m)) (p e : ℝ) (hp : p ∈ Icc 0 1) (he : 0 ≤ e)
    (hk : ((raggedSize m : ℝ)+1)*(p+e) ≤ (k.val+1 : ℝ)) :
    μ.real {ω | sampleQuantile (raggedSample m U ω) k < p} ≤
      Real.exp (-2*(raggedSize m : ℝ)^2*e^2/(∑ j, (m j : ℝ)^2)) := by
  have ht := (ragged_count_tails m U hU hindep hunif p hp
    ((raggedSize m : ℝ)*e) (by positivity)).1
  have hs : {ω | sampleQuantile (raggedSample m U ω) k < p} ⊆
      {ω | (raggedSize m : ℝ)*e ≤ (∑ j, thresholdCount p (U j ω)) -
        (raggedSize m : ℝ)*p} := by
    intro ω hω
    have hc := (sampleQuantile_le_iff (raggedSample m U ω) k p).mp hω.le
    have hc' : (k.val+1 : ℝ) ≤
        ((Finset.univ.filter (fun i ↦ raggedSample m U ω i ≤ p)).card : ℝ) := by
      exact_mod_cast hc
    rw [raggedSample_count] at hc'
    simp only [mem_setOf_eq]
    nlinarith [hp.1]
  convert (measureReal_mono (μ := μ) hs).trans ht using 1 <;> congr 1
  ring

lemma clusterCorrection_exp {b : ℕ} (m : Fin b → ℕ)
    (hN : 0 < raggedSize m) (eta : ℝ) (heta : eta ∈ Ioo 0 1) :
    Real.exp (-2*(raggedSize m : ℝ)^2*(clusterCorrection m eta)^2 /
      (∑ j, (m j : ℝ)^2)) = eta := by
  have hNr : (0:ℝ) < raggedSize m := by exact_mod_cast hN
  have hS : (0:ℝ) < ∑ j, (m j : ℝ)^2 := by
    have hh : (raggedSize m : ℝ) ≤ ∑ j, (m j : ℝ)^2 := by
      rw [raggedSize_eq_sum, Nat.cast_sum]
      apply Finset.sum_le_sum
      intro j _
      exact_mod_cast (show m j ≤ (m j)^2 by simpa [pow_two] using Nat.le_mul_self (m j))
    exact hNr.trans_le hh
  have hl : 0 ≤ Real.log (1/eta) := Real.log_nonneg (by
    apply (le_div_iff₀ heta.1).mpr
    linarith [heta.2])
  rw [clusterCorrection, Real.sq_sqrt (by positivity)]
  have he : -2*(raggedSize m : ℝ)^2 *
      ((∑ j, (m j : ℝ)^2)*Real.log (1/eta)/(2*(raggedSize m : ℝ)^2)) /
      (∑ j, (m j : ℝ)^2) = -Real.log (1/eta) := by
    field_simp
  rw [he, Real.log_div (by norm_num) (ne_of_gt heta.1), Real.log_one]
  simpa using Real.exp_log heta.1

/-- Section 6.2, including the prescribed rank and the infinite-cutoff case. -/
theorem correctedCoverage_failure_bound {b : ℕ} (m : Fin b → ℕ)
    (hN : 0 < raggedSize m)
    (S : (j : Fin b) → Ω → Fin (m j) → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i t, μ.real {ω | S j ω i ≤ t} = F t)
    (p eta : ℝ) (hp : p ∈ Ioo 0 1) (heta : eta ∈ Ioo 0 1) :
    μ.real {ω | correctedCoverage m S F p eta ω < p} ≤ eta := by
  let r := ⌈((raggedSize m : ℝ)+1)*(p+clusterCorrection m eta)⌉₊
  have hr : 0 < r := Nat.ceil_pos.mpr (mul_pos (by positivity)
    (add_pos_of_pos_of_nonneg hp.1 (Real.sqrt_nonneg _)))
  by_cases hn : r ≤ raggedSize m
  · let k : Fin (raggedSize m) := ⟨r-1, by omega⟩
    let T := fun j (u : Fin (m j) → ℝ) i ↦ F (u i)
    have hT (j : Fin b) : Measurable (T j) :=
      measurable_pi_lambda _ (fun i ↦ hF.measurable.comp (measurable_pi_apply i))
    let U := fun j ω i ↦ F (S j ω i)
    have hU (j : Fin b) : Measurable (U j) := (hT j).comp (hS j)
    have hi : iIndepFun U μ := hindep.comp T hT
    have hu : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t := by
      intro j i t ht0 ht1
      exact continuous_cdf_transform (fun ω ↦ S j ω i) F hF hmono h0 h1 (hCDF j i) t ht0 ht1
    have hk : (k.val+1 : ℝ) = r := by
      have : k.val+1 = r := by dsimp [k]; omega
      exact_mod_cast this
    have ht := ragged_quantile_undercoverage m U hU hi hu k p (clusterCorrection m eta)
      ⟨hp.1.le, hp.2.le⟩ (Real.sqrt_nonneg _) (by rw [hk]; exact Nat.le_ceil _)
    rw [clusterCorrection_exp m hN eta heta] at ht
    have he (ω : Ω) : correctedCoverage m S F p eta ω = sampleQuantile (raggedSample m U ω) k := by
      unfold correctedCoverage
      dsimp only
      rw [dif_pos (show 0 < r ∧ r ≤ raggedSize m from ⟨hr, hn⟩)]
      exact (sampleQuantile_monotone_map (raggedSample m S ω) k F hmono).symm
    simpa only [he] using ht
  · have he (ω : Ω) : correctedCoverage m S F p eta ω = 1 := by
      unfold correctedCoverage
      dsimp only
      rw [dif_neg (show ¬(0 < r ∧ r ≤ raggedSize m) from fun h ↦ hn h.2)]
    simp only [he, not_lt.mpr hp.2.le, Set.setOf_false, measureReal_empty]
    exact heta.1.le

/-- The equivalent success-probability statement in Section 6.2. -/
theorem correctedCoverage_success_bound {b : ℕ} (m : Fin b → ℕ)
    (hN : 0 < raggedSize m)
    (S : (j : Fin b) → Ω → Fin (m j) → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i t, μ.real {ω | S j ω i ≤ t} = F t)
    (p eta : ℝ) (hp : p ∈ Ioo 0 1) (heta : eta ∈ Ioo 0 1) :
    1-eta ≤ μ.real {ω | p ≤ correctedCoverage m S F p eta ω} := by
  have hm : Measurable (correctedCoverage m S F p eta) := by
    unfold correctedCoverage
    dsimp only
    split_ifs
    · exact hF.measurable.comp (measurable_sampleQuantile _
        (fun _ ↦ (measurable_pi_apply _).comp (hS _)) _)
    · exact measurable_const
  have he : {ω | p ≤ correctedCoverage m S F p eta ω} =
      {ω | correctedCoverage m S F p eta ω < p}ᶜ := by ext ω; simp
  rw [he, measureReal_compl (measurableSet_lt hm measurable_const), probReal_univ]
  linarith [correctedCoverage_failure_bound m hN S hS hindep F hF hmono h0 h1 hCDF p eta hp heta]

end Exceedance
#print axioms Exceedance.correctedCoverage_failure_bound

#print axioms Exceedance.correctedCoverage_success_bound
