import ClusterSample
import Concentration
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

/-- Every cluster count lies between zero and the cluster size, including with ties. -/
lemma thresholdCount_bounds {ι : Type*} [Fintype ι] (u : ι → ℝ) (t : ℝ) :
    thresholdCount t u ∈ Icc 0 (Fintype.card ι : ℝ) := by
  classical
  constructor
  · apply Finset.sum_nonneg
    intro i _
    simp only [indicator, Set.indicator, mem_setOf_eq]
    split_ifs <;> norm_num
  · calc
      _ ≤ ∑ _i : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [indicator, Set.indicator, mem_setOf_eq]
        split_ifs <;> norm_num
      _ = _ := by simp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Count tails for independent clusters with uniform marginals.
    Identical joint distributions of the clusters are not needed here. -/
theorem pooled_count_tails {m : ℕ} (U : ℕ → Ω → Fin m → ℝ)
    (hU : ∀ j, Measurable (U j)) (hindep : iIndepFun U μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (b : ℕ) (t : ℝ) (ht : t ∈ Icc 0 1) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ (∑ j ∈ Finset.range b, thresholdCount t (U j ω)) -
      (b : ℝ)*m*t} ≤ Real.exp (-2*ε^2/((b : ℝ)*m^2)) ∧
    μ.real {ω | ε ≤ (b : ℝ)*m*t -
      (∑ j ∈ Finset.range b, thresholdCount t (U j ω))} ≤
      Real.exp (-2*ε^2/((b : ℝ)*m^2)) := by
  classical
  let X : Fin b → Ω → ℝ := fun j ω ↦ thresholdCount t (U j ω)
  have hX (j : Fin b) : Measurable (X j) := (measurable_thresholdCount t).comp (hU j)
  have hi : iIndepFun X μ := (hindep.precomp Fin.val_injective).comp
    (fun _ ↦ thresholdCount t) (fun _ ↦ measurable_thresholdCount t)
  have hb (j : Fin b) : ∀ᵐ ω ∂μ, X j ω ∈ Icc 0 (m : ℝ) :=
    Filter.Eventually.of_forall (fun ω ↦ by simpa using thresholdCount_bounds (U j ω) t)
  have hmean (j : Fin b) : (∫ ω, X j ω ∂μ) = (m : ℝ)*t := by
    simpa [X] using thresholdCount_mean (U j) (hU j) t (fun i ↦ hunif j i t ht.1 ht.2)
  have hu := cluster_count_upper_tail X (fun _ ↦ (m : ℝ))
    (fun j ↦ (hX j).aemeasurable) hb hi ε hε
  have hl := cluster_count_lower_tail X (fun _ ↦ (m : ℝ))
    (fun j ↦ (hX j).aemeasurable) hb hi ε hε
  simp only [hmean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, X] at hu hl
  simp_rw [← Fin.sum_univ_eq_sum_range]
  simpa only [mul_assoc] using And.intro hu hl

/-- Exact upper survival event for an unsorted sample, including ties. -/
lemma sampleQuantile_gt_iff {n : ℕ} (u : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    t < sampleQuantile u k ↔ (Finset.univ.filter (fun i ↦ u i ≤ t)).card ≤ k.val := by
  rw [← not_le, sampleQuantile_le_iff]
  omega


/-- Uniform marginal CDFs imply support in the unit interval almost surely. -/
lemma uniform_marginal_support (X : Ω → ℝ) (hX : Measurable X)
    (hunif : ∀ t, 0 ≤ t → t ≤ 1 → μ.real {ω | X ω ≤ t} = t) :
    ∀ᵐ ω ∂μ, X ω ∈ Icc 0 1 := by
  have hzero : μ {ω | X ω ≤ 0} = 0 :=
    (measureReal_eq_zero_iff).mp (hunif 0 le_rfl zero_le_one)
  have hlo : ∀ᵐ ω ∂μ, ¬ X ω ≤ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hzero
  have hone : μ {ω | X ω ≤ 1} = 1 := by
    apply ENNReal.toReal_eq_toReal_iff' (by finiteness) (by simp) |>.mp
    simpa only [measureReal_def, ENNReal.toReal_one] using hunif 1 zero_le_one le_rfl
  have hhi : ∀ᵐ ω ∂μ, X ω ≤ 1 :=
    (mem_ae_iff_prob_eq_one (measurableSet_le hX measurable_const)).mpr hone
  filter_upwards [hlo, hhi] with ω hω hω'
  exact ⟨(lt_of_not_ge hω).le, hω'⟩

/-- The pooled sample quantile inherits the marginal support. -/
lemma pooled_quantile_support {m : ℕ} (U : ℕ → Ω → Fin m → ℝ)
    (hU : ∀ j, Measurable (U j))
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (b : ℕ) (k : Fin (b*m)) :
    ∀ᵐ ω ∂μ, sampleQuantile (pooledSample U b ω) k ∈ Icc 0 1 := by
  have hs : ∀ j i, ∀ᵐ ω ∂μ, U j ω i ∈ Icc 0 1 := fun j i ↦
    uniform_marginal_support (fun ω ↦ U j ω i)
      ((measurable_pi_apply i).comp (hU j)) (hunif j i)
  have hall : ∀ᵐ ω ∂μ, ∀ j i, U j ω i ∈ Icc 0 1 := by
    exact ae_all_iff.mpr (fun j ↦ ae_all_iff.mpr (hs j))
  filter_upwards [hall] with ω hω
  exact hω _ _

/-- A sample quantile has a finite-sample two-sided tail bound under independent clusters.
    The center is the exact rank level k/(N+1). Cluster distributions may differ. -/
theorem pooled_quantile_tail {m : ℕ} (U : ℕ → Ω → Fin m → ℝ)
    (hU : ∀ j, Measurable (U j)) (hindep : iIndepFun U μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (b : ℕ) (k : Fin (b*m)) (x : ℝ) (hx : 0 ≤ x) :
    μ.real {ω | x < |sampleQuantile (pooledSample U b ω) k -
      ((k.val+1 : ℕ) : ℝ)/((b*m : ℕ)+1)|} ≤
      2 * Real.exp (-2*((b*m : ℕ) : ℝ)^2*x^2/((b : ℝ)*m^2)) := by
  classical
  let N : ℝ := (b*m : ℕ)
  let p : ℝ := ((k.val+1 : ℕ) : ℝ)/(N+1)
  let C : Ω → ℝ := fun ω ↦ sampleQuantile (pooledSample U b ω) k
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  have hkp : ((k.val+1 : ℕ) : ℝ) = (N+1)*p := by
    dsimp [p]; field_simp
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    apply (div_le_one (by positivity : 0 < N+1)).mpr
    have hk : k.val+1 ≤ b*m := k.isLt
    have hk' : ((k.val+1 : ℕ) : ℝ) ≤ N := by dsimp [N]; exact_mod_cast hk
    linarith
  let R : ℝ := Real.exp (-2*N^2*x^2/((b : ℝ)*m^2))
  have hR : 0 ≤ R := (Real.exp_pos _).le
  have hs := pooled_quantile_support U hU hunif b k
  have hlo : μ.real {ω | C ω < p-x} ≤ R := by
    by_cases ht : 0 ≤ p-x
    · have ht1 : p-x ≤ 1 := by linarith
      have hu := (pooled_count_tails U hU hindep hunif b (p-x) ⟨ht, ht1⟩
        (N*x) (mul_nonneg hN.le hx)).1
      have hsub : {ω | C ω < p-x} ⊆
          {ω | N*x ≤ (∑ j ∈ Finset.range b, thresholdCount (p-x) (U j ω)) -
            (b : ℝ)*m*(p-x)} := by
        intro ω hω
        have hc := (sampleQuantile_le_iff (pooledSample U b ω) k (p-x)).mp hω.le
        have hc' : ((k.val+1 : ℕ) : ℝ) ≤
            ((Finset.univ.filter (fun i ↦ pooledSample U b ω i ≤ p-x)).card : ℝ) := by
          exact_mod_cast hc
        rw [pooledSample_count] at hc'
        have hn : (b : ℝ)*m = N := by simp [N]
        dsimp only [mem_setOf_eq]
        rw [hn]
        nlinarith
      have hh := (measureReal_mono (μ := μ) hsub).trans hu
      dsimp [R]
      convert hh using 1 <;> congr 1
      ring
    · have hz : μ {ω | C ω < p-x} = 0 := by
        have he : ∀ᵐ ω ∂μ, ¬ C ω < p-x := by
          filter_upwards [hs] with ω hω
          change C ω ∈ Icc 0 1 at hω
          linarith [hω.1]
        simpa only [not_not] using (ae_iff.mp he)
      rw [measureReal_def, hz, ENNReal.toReal_zero]
      exact hR
  have hhi : μ.real {ω | p+x < C ω} ≤ R := by
    by_cases ht : p+x ≤ 1
    · have ht0 : 0 ≤ p+x := by linarith
      have hl := (pooled_count_tails U hU hindep hunif b (p+x) ⟨ht0, ht⟩
        (N*x) (mul_nonneg hN.le hx)).2
      have hsub : {ω | p+x < C ω} ⊆
          {ω | N*x ≤ (b : ℝ)*m*(p+x) -
            (∑ j ∈ Finset.range b, thresholdCount (p+x) (U j ω))} := by
        intro ω hω
        have hc := (sampleQuantile_gt_iff (pooledSample U b ω) k (p+x)).mp hω
        have hc' : ((Finset.univ.filter (fun i ↦ pooledSample U b ω i ≤ p+x)).card : ℝ) ≤
            (k.val : ℝ) := by exact_mod_cast hc
        rw [pooledSample_count] at hc'
        have hn : (b : ℝ)*m = N := by simp [N]
        have hkcast : ((k.val+1 : ℕ) : ℝ) = (k.val : ℝ)+1 := by simp
        dsimp only [mem_setOf_eq]
        rw [hn]
        nlinarith
      have hh := (measureReal_mono (μ := μ) hsub).trans hl
      dsimp [R]
      convert hh using 1 <;> congr 1
      ring
    · have hz : μ {ω | p+x < C ω} = 0 := by
        have he : ∀ᵐ ω ∂μ, ¬ p+x < C ω := by
          filter_upwards [hs] with ω hω
          change C ω ∈ Icc 0 1 at hω
          linarith [hω.2]
        simpa only [not_not] using (ae_iff.mp he)
      rw [measureReal_def, hz, ENNReal.toReal_zero]
      exact hR
  have he : {ω | x < |C ω-p|} = {ω | C ω < p-x} ∪ {ω | p+x < C ω} := by
    ext ω
    simp only [mem_setOf_eq, mem_union, lt_abs]
    constructor <;> intro h <;> rcases h with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  change μ.real {ω | x < |C ω-p|} ≤ 2*R
  rw [he]
  exact (measureReal_union_le _ _).trans (by linarith)


/-- The normalized quantile has a Gaussian tail bound uniform in the number of clusters. -/
theorem normalized_pooled_quantile_tail {m : ℕ} (U : ℕ → Ω → Fin m → ℝ)
    (hU : ∀ j, Measurable (U j)) (hindep : iIndepFun U μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (b : ℕ) (k : Fin (b*m)) (y : ℝ) (hy : 0 ≤ y) :
    μ.real {ω | y < |Real.sqrt (b*m : ℕ) *
      (sampleQuantile (pooledSample U b ω) k -
        ((k.val+1 : ℕ) : ℝ)/((b*m : ℕ)+1))|} ≤
      2 * Real.exp (-2*y^2/(m : ℝ)) := by
  have hN : 0 < ((b*m : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  have hb : (b : ℝ) ≠ 0 := by
    have : b ≠ 0 := by intro h; simp [h] at hN
    exact_mod_cast this
  have hm : (m : ℝ) ≠ 0 := by
    have : m ≠ 0 := by intro h; simp [h] at hN
    exact_mod_cast this
  have hs := Real.sqrt_pos.mpr hN
  have hsq := Real.sq_sqrt hN.le
  have ht := pooled_quantile_tail U hU hindep hunif b k
    (y/Real.sqrt (b*m : ℕ)) (div_nonneg hy hs.le)
  have he : {ω | y < |Real.sqrt (b*m : ℕ) *
      (sampleQuantile (pooledSample U b ω) k -
        ((k.val+1 : ℕ) : ℝ)/((b*m : ℕ)+1))|} =
      {ω | y/Real.sqrt (b*m : ℕ) < |sampleQuantile (pooledSample U b ω) k -
        ((k.val+1 : ℕ) : ℝ)/((b*m : ℕ)+1)|} := by
    ext ω
    simp only [mem_setOf_eq, abs_mul, abs_of_pos hs, div_lt_iff₀ hs]
    rw [mul_comm (Real.sqrt _)]
  rw [he]
  have hexp : -2*((b*m : ℕ) : ℝ)^2*(y/Real.sqrt (b*m : ℕ))^2/((b : ℝ)*m^2) =
      -2*y^2/(m : ℝ) := by
    rw [div_pow, hsq]
    simp only [Nat.cast_mul]
    field_simp
  rwa [hexp] at ht

/-- The same bound applies on the true continuous-CDF coverage scale. -/
theorem continuous_score_coverage_tail {m : ℕ} (S : ℕ → Ω → Fin m → ℝ)
    (hS : ∀ j, Measurable (S j)) (hindep : iIndepFun S μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i t, μ.real {ω | S j ω i ≤ t} = F t)
    (b : ℕ) (k : Fin (b*m)) (y : ℝ) (hy : 0 ≤ y) :
    μ.real {ω | y < |Real.sqrt (b*m : ℕ) *
      (F (sampleQuantile (pooledSample S b ω) k) -
        ((k.val+1 : ℕ) : ℝ)/((b*m : ℕ)+1))|} ≤
      2 * Real.exp (-2*y^2/(m : ℝ)) := by
  let T : (Fin m → ℝ) → (Fin m → ℝ) := fun u i ↦ F (u i)
  have hT : Measurable T := measurable_pi_lambda _ (fun i ↦ hF.measurable.comp (measurable_pi_apply i))
  let U : ℕ → Ω → Fin m → ℝ := fun j ω i ↦ F (S j ω i)
  have hU (j : ℕ) : Measurable (U j) := hT.comp (hS j)
  have hi : iIndepFun U μ := hindep.comp (fun _ ↦ T) (fun _ ↦ hT)
  have hu : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t := by
    intro j i t ht0 ht1
    exact continuous_cdf_transform (fun ω ↦ S j ω i) F hF hmono h0 h1 (hCDF j i) t ht0 ht1
  have ht := normalized_pooled_quantile_tail U hU hi hu b k y hy
  have he (ω : Ω) : sampleQuantile (pooledSample U b ω) k =
      F (sampleQuantile (pooledSample S b ω) k) :=
    sampleQuantile_monotone_map (pooledSample S b ω) k F hmono
  simpa only [he] using ht

end Exceedance
#print axioms Exceedance.pooled_count_tails

#print axioms Exceedance.pooled_quantile_tail

#print axioms Exceedance.normalized_pooled_quantile_tail
#print axioms Exceedance.continuous_score_coverage_tail
