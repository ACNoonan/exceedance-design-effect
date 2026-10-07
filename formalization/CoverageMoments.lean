import QuantileMoments
import ClusterCoverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Uniform marginal probabilities exclude atoms, including at the endpoints. -/
lemma uniform_marginal_no_atoms (X : Ω → ℝ) (hX : Measurable X)
    (hu : ∀ t, 0 ≤ t → t ≤ 1 → μ.real {ω | X ω ≤ t} = t) (a : ℝ) :
    μ {ω | X ω = a} = 0 := by
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ measureReal_nonneg
  by_cases ha0 : a ≤ 0
  · have hs : {ω | X ω = a} ⊆ {ω | X ω ≤ 0} := fun ω h ↦ by
      change X ω = a at h
      change X ω ≤ 0
      linarith
    exact (measureReal_mono (μ := μ) hs).trans_eq (hu 0 le_rfl zero_le_one)
  by_cases ha1 : a ≤ 1
  · apply le_of_forall_pos_le_add
    intro ε hε
    let l : ℝ := max 0 (a-ε)
    have hl0 : 0 ≤ l := le_max_left _ _
    have hla : l < a := max_lt (by linarith) (by linarith)
    have hm : μ.real {ω | l < X ω ∧ X ω ≤ a} = a-l := by
      have hs : {ω | l < X ω ∧ X ω ≤ a} = {ω | X ω ≤ a} \ {ω | X ω ≤ l} := by
        ext ω
        simp only [Set.mem_sdiff, mem_setOf_eq, not_le]
        exact and_comm
      have hsub : {ω | X ω ≤ l} ⊆ {ω | X ω ≤ a} := fun _ h ↦ h.trans hla.le
      rw [hs, measureReal_sdiff (μ := μ) hsub
        (measurableSet_le hX measurable_const), hu a (by linarith) ha1, hu l hl0 (hla.le.trans ha1)]
    have hs : {ω | X ω = a} ⊆ {ω | l < X ω ∧ X ω ≤ a} := by
      intro ω h
      change X ω = a at h
      change l < X ω ∧ X ω ≤ a
      rw [h]
      exact ⟨hla, le_rfl⟩
    have hh := (measureReal_mono (μ := μ) hs).trans_eq hm
    have hl : a-ε ≤ l := le_max_right _ _
    linarith
  · have hs := uniform_marginal_support X hX hu
    have hz : μ {ω | X ω = a} = 0 := by
      have he : ∀ᵐ ω ∂μ, ¬ X ω = a := by
        filter_upwards [hs] with ω hω
        intro he
        rw [he] at hω
        exact ha1 hω.2
      simpa only [not_not] using ae_iff.mp he
    rw [measureReal_def, hz, ENNReal.toReal_zero]

omit [IsProbabilityMeasure μ] in
/-- A finite order statistic has no atoms when every coordinate has no atoms.
    Coordinates need not be independent. -/
lemma sampleQuantile_no_atoms {n : ℕ} (X : Fin n → Ω → ℝ)
    (ha : ∀ i a, μ {ω | X i ω = a} = 0) (k : Fin n) (a : ℝ) :
    μ {ω | sampleQuantile (fun i ↦ X i ω) k = a} = 0 := by
  have he : ∀ᵐ ω ∂μ, ∀ i, X i ω ≠ a := by
    apply ae_all_iff.mpr
    intro i
    rw [ae_iff]
    simpa only [not_not] using ha i a
  have hh : ∀ᵐ ω ∂μ, ¬ sampleQuantile (fun i ↦ X i ω) k = a := by
    filter_upwards [he] with ω hω
    exact hω _
  simpa only [not_not] using ae_iff.mp hh

lemma normalizedPooledQuantile_no_atoms {m : ℕ} (U : ℕ → Ω → Fin m → ℝ)
    (hU : ∀ j, Measurable (U j))
    (hu : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (b : ℕ) (k : Fin (b*m)) (a : ℝ) :
    μ {ω | normalizedPooledQuantile U b k ω = a} = 0 := by
  have hn : 0 < ((b*m : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  have hr := Real.sqrt_pos.mpr hn
  let p : ℝ := ((k.val+1 : ℕ) : ℝ)/((b*m : ℕ)+1)
  have hc := sampleQuantile_no_atoms (μ := μ) (fun i ω ↦ pooledSample U b ω i)
    (fun i t ↦ uniform_marginal_no_atoms _ ((measurable_pi_apply _).comp (hU _)) (hu _ _) t)
    k (p+a/Real.sqrt (b*m : ℕ))
  apply measure_mono_null _ hc
  intro ω hω
  change Real.sqrt (b*m : ℕ)*(sampleQuantile (pooledSample U b ω) k-p) = a at hω
  change sampleQuantile (pooledSample U b ω) k = p+a/Real.sqrt (b*m : ℕ)
  have hd : sampleQuantile (pooledSample U b ω) k-p = a/Real.sqrt (b*m : ℕ) :=
    (eq_div_iff hr.ne').mpr (by nlinarith [hω])
  linarith

omit [IsProbabilityMeasure μ] in
/-- Strict and non-strict lower tails agree at a non-atomic point. -/
lemma probability_lt_eq_le (X : Ω → ℝ) (a : ℝ) (ha : μ {ω | X ω = a} = 0) :
    μ.real {ω | X ω < a} = μ.real {ω | X ω ≤ a} := by
  apply measureReal_congr
  have he : ∀ᵐ ω ∂μ, X ω ≠ a := by
    rw [ae_iff]
    simpa only [not_not] using ha
  filter_upwards [he] with ω hω
  change (X ω < a) = (X ω ≤ a)
  exact propext (lt_iff_le_and_ne.trans (and_iff_left hω))

omit [IsProbabilityMeasure μ] in
/-- A common integrable tail bound permits convergence of expectations by layer cake. -/
theorem nonnegative_expectation_limit_of_tail_limit
    {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (Y : ℕ → Ω → ℝ) (W : Ω' → ℝ)
    (hi : ∀ n, Integrable (Y n) μ) (hW : Integrable W ν)
    (hY0 : ∀ n ω, 0 ≤ Y n ω) (hW0 : ∀ ω, 0 ≤ W ω)
    (B : ℝ → ℝ) (hB : IntegrableOn B (Ioi 0))
    (hbound : ∀ n t, 0 < t → μ.real {ω | t < Y n ω} ≤ B t)
    (hlim : ∀ t, 0 < t → Tendsto (fun n ↦ μ.real {ω | t < Y n ω}) atTop
      (nhds (ν.real {ω | t < W ω}))) :
    Tendsto (fun n ↦ ∫ ω, Y n ω ∂μ) atTop (nhds (∫ ω, W ω ∂ν)) := by
  have hm (n : ℕ) : Measurable (fun t ↦ μ.real {ω | t < Y n ω}) := by
    apply Measurable.ennreal_toReal
    exact Antitone.measurable (fun _ _ h ↦ measure_mono (fun _ hω ↦ lt_of_le_of_lt h hω))
  have ht := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioi 0))
    (f := fun t ↦ ν.real {ω | t < W ω}) B
    (fun n ↦ (hm n).aestronglyMeasurable) hB
    (fun n ↦ ?_) ?_
  · have he (n : ℕ) := (hi n).integral_eq_integral_meas_lt (Eventually.of_forall (hY0 n))
    have hw := hW.integral_eq_integral_meas_lt (Eventually.of_forall hW0)
    simpa only [← he, ← hw] using ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact hbound n t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hlim t ht


lemma probability_gt_eq_one_sub_le (X : Ω → ℝ) (hX : Measurable X) (a : ℝ) :
    μ.real {ω | a < X ω} = 1-μ.real {ω | X ω ≤ a} := by
  have he : {ω | a < X ω} = {ω | X ω ≤ a}ᶜ := by ext ω; simp
  rw [he, measureReal_compl (measurableSet_le hX measurable_const), probReal_univ]

/-- A squared tail is the sum of the two disjoint one-sided tails. -/
lemma square_tail_cdf_identity (X : Ω → ℝ) (hX : Measurable X)
    (t : ℝ) (ht : 0 < t) (ha : μ {ω | X ω = -Real.sqrt t} = 0) :
    μ.real {ω | t < (X ω)^2} =
      μ.real {ω | X ω ≤ -Real.sqrt t} + (1-μ.real {ω | X ω ≤ Real.sqrt t}) := by
  have hs := Real.sqrt_pos.mpr ht
  have hsq := Real.sq_sqrt ht.le
  have he : {ω | t < (X ω)^2} =
      {ω | X ω < -Real.sqrt t} ∪ {ω | Real.sqrt t < X ω} := by
    ext ω
    simp only [mem_setOf_eq, mem_union]
    constructor
    · intro h
      by_cases hx : X ω < -Real.sqrt t
      · exact Or.inl hx
      · exact Or.inr (by nlinarith)
    · rintro (h | h) <;> nlinarith
  have hd : Disjoint {ω | X ω < -Real.sqrt t} {ω | Real.sqrt t < X ω} := by
    apply disjoint_left.mpr
    intro ω h1 h2
    dsimp only [mem_setOf_eq] at h1 h2
    linarith
  rw [he, measureReal_union₀ (measurableSet_lt measurable_const hX).nullMeasurableSet hd.aedisjoint,
    probability_lt_eq_le X _ ha, probability_gt_eq_one_sub_le X hX]

/-- Squared normalized quantile errors converge in expectation to the Gaussian second moment. -/
theorem iid_pooled_quantile_second_moment_limit {m : ℕ} (hm : 0 < m)
    (U : ℕ → Ω → Fin m → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ) (hident : ∀ j, IdentDistrib (U j) (U 0) μ μ)
    (hu : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (p : ℝ) (hp : p ∈ Ioo 0 1) (k : ∀ n : ℕ, Fin ((n+1)*m))
    (hkp : Tendsto (fun n ↦ (((k n).val+1 : ℕ) : ℝ)/(((n+1)*m : ℕ)+1)) atTop (nhds p)) :
    Tendsto (fun n ↦ ∫ ω, (normalizedPooledQuantile U (n+1) (k n) ω)^2 ∂μ) atTop
      (nhds (clusterCoverageVariance (μ := μ) U p : ℝ)) := by
  let v := clusterCoverageVariance (μ := μ) U p
  let ν := gaussianReal 0 v
  let Z : ℕ → Ω → ℝ := fun n ↦ normalizedPooledQuantile U (n+1) (k n)
  have hz (n : ℕ) : Measurable (Z n) := measurable_normalizedPooledQuantile U hU (n+1) (k n)
  have hc (x : ℝ) (hx : x ≠ 0) : Tendsto (fun n ↦ μ.real {ω | Z n ω ≤ x}) atTop
      (nhds (ν.real {z : ℝ | z ≤ x})) := by
    simpa only [cdf_eq_real, Z, normalizedPooledQuantile, ν, v, Iic] using iid_cluster_coverage_cdf hm U hU hindep hident hu p hp k hkp x (Or.inr hx)
  have ht (t : ℝ) (ht : 0 < t) : Tendsto (fun n ↦ μ.real {ω | t < (Z n ω)^2}) atTop
      (nhds (ν.real {z : ℝ | t < z^2})) := by
    have hs := Real.sqrt_pos.mpr ht
    have ha : ν {z : ℝ | z = -Real.sqrt t} = 0 :=
      centered_gaussian_no_atom_at_continuity id v HasLaw.id _ (Or.inr hs.ne')
    have he (n : ℕ) := square_tail_cdf_identity (Z n) (hz n) t ht
      (normalizedPooledQuantile_no_atoms U hU hu (n+1) (k n) _)
    have hv := square_tail_cdf_identity (μ := ν) id measurable_id t ht ha
    simp only [id_eq] at hv
    simp_rw [he]
    rw [hv]
    exact (hc _ (neg_ne_zero.mpr hs.ne')).add (tendsto_const_nhds.sub (hc _ hs.ne'))
  have hiW : Integrable (fun z : ℝ ↦ z^2) ν :=
    (memLp_id_gaussianReal' 2 (by norm_num)).integrable_sq
  have hB : IntegrableOn (fun t : ℝ ↦ 2*Real.exp (-(2/(m : ℝ))*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (div_pos (by norm_num) (by exact_mod_cast hm))) 0).const_mul 2
  have hl := nonnegative_expectation_limit_of_tail_limit (ν := ν)
    (fun n ω ↦ (Z n ω)^2) (fun z : ℝ ↦ z^2)
    (fun n ↦ (normalizedPooledQuantile_memLp U hU hu (n+1) (k n)).integrable_sq) hiW
    (fun _ _ ↦ sq_nonneg _) (fun _ ↦ sq_nonneg _) _ hB
    (fun n t ht ↦ gaussian_tail_square_tail _ _
      (normalized_pooled_quantile_tail U hU hindep hu (n+1) (k n)) t ht.le) ht
  have hv : (∫ z : ℝ, z^2 ∂ν) = (v : ℝ) := by
    have hh := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
    rw [variance_eq_integral (X := fun z : ℝ ↦ z) (by fun_prop)] at hh
    simpa only [integral_id_gaussianReal, sub_zero] using hh
  rwa [hv] at hl


omit [IsProbabilityMeasure μ] in
lemma integrable_positive_part (X : Ω → ℝ) (hX : Measurable X) (hi : Integrable X μ) :
    Integrable (fun ω ↦ max (X ω) 0) μ := by
  apply hi.norm.mono' (hX.max measurable_const).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
  exact max_le (le_abs_self _) (abs_nonneg _)

omit [IsProbabilityMeasure μ] [MeasurableSpace Ω] in
lemma positive_part_tail (X : Ω → ℝ) (t : ℝ) (ht : 0 < t) :
    {ω | t < max (X ω) 0} = {ω | t < X ω} := by
  ext ω
  simp only [mem_setOf_eq, lt_max_iff, not_lt_of_ge ht.le, or_false]

/-- Convergence of the two one-sided tails gives convergence of signed expectations. -/
theorem expectation_limit_of_two_tail_limits
    {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (W : Ω' → ℝ)
    (hX : ∀ n, Measurable (X n)) (hW : Measurable W)
    (hi : ∀ n, Integrable (X n) μ) (hiW : Integrable W ν)
    (B : ℝ → ℝ) (hB : IntegrableOn B (Ioi 0))
    (hbound : ∀ n t, 0 < t → μ.real {ω | t < |X n ω|} ≤ B t)
    (hpos : ∀ t, 0 < t → Tendsto (fun n ↦ μ.real {ω | t < X n ω}) atTop
      (nhds (ν.real {ω | t < W ω})))
    (hneg : ∀ t, 0 < t → Tendsto (fun n ↦ μ.real {ω | t < -X n ω}) atTop
      (nhds (ν.real {ω | t < -W ω}))) :
    Tendsto (fun n ↦ ∫ ω, X n ω ∂μ) atTop (nhds (∫ ω, W ω ∂ν)) := by
  have hp := nonnegative_expectation_limit_of_tail_limit (ν := ν)
    (fun n ω ↦ max (X n ω) 0) (fun ω ↦ max (W ω) 0)
    (fun n ↦ integrable_positive_part _ (hX n) (hi n)) (integrable_positive_part _ hW hiW)
    (fun _ _ ↦ le_max_right _ _) (fun _ ↦ le_max_right _ _) B hB
    (fun n t ht ↦ by
      rw [positive_part_tail _ t ht]
      have hs : {ω | t < X n ω} ⊆ {ω | t < |X n ω|}  := by
        intro ω h
        change t < X n ω at h
        change t < |X n ω|
        exact h.trans_le (le_abs_self _)
      exact (measureReal_mono (μ := μ) hs).trans (hbound n t ht))
    (fun t ht ↦ by simpa only [positive_part_tail _ t ht] using hpos t ht)
  have hn := nonnegative_expectation_limit_of_tail_limit (ν := ν)
    (fun n ω ↦ max (-X n ω) 0) (fun ω ↦ max (-W ω) 0)
    (fun n ↦ integrable_positive_part _ (hX n).neg (hi n).neg) (integrable_positive_part _ hW.neg hiW.neg)
    (fun _ _ ↦ le_max_right _ _) (fun _ ↦ le_max_right _ _) B hB
    (fun n t ht ↦ by
      rw [positive_part_tail _ t ht]
      have hs : {ω | t < -X n ω} ⊆ {ω | t < |X n ω|}  := by
        intro ω h
        change t < -X n ω at h
        change t < |X n ω|
        exact h.trans_le (neg_le_abs _)
      exact (measureReal_mono (μ := μ) hs).trans (hbound n t ht))
    (fun t ht ↦ by simpa only [positive_part_tail _ t ht] using hneg t ht)
  have he (x : ℝ) : max x 0-max (-x) 0 = x := by
    by_cases h : 0 ≤ x
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  have hiEq (n : ℕ) : (∫ ω, max (X n ω) 0 ∂μ)-(∫ ω, max (-X n ω) 0 ∂μ) =
      ∫ ω, X n ω ∂μ := by
    have hh := integral_sub (integrable_positive_part _ (hX n) (hi n))
      (integrable_positive_part _ (hX n).neg (hi n).neg)
    simp only [Pi.neg_apply] at hh
    rw [← hh]
    simp_rw [he]
  have hwEq : (∫ ω, max (W ω) 0 ∂ν)-(∫ ω, max (-W ω) 0 ∂ν) = ∫ ω, W ω ∂ν := by
    have hh := integral_sub (integrable_positive_part _ hW hiW) (integrable_positive_part _ hW.neg hiW.neg)
    simp only [Pi.neg_apply] at hh
    rw [← hh]
    simp_rw [he]
  have hh := hp.sub hn
  simpa only [hiEq, hwEq] using hh


/-- The normalized quantile error has mean tending to zero. This gives no second-order drift expansion. -/
theorem iid_pooled_quantile_mean_limit {m : ℕ} (hm : 0 < m)
    (U : ℕ → Ω → Fin m → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ) (hident : ∀ j, IdentDistrib (U j) (U 0) μ μ)
    (hu : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (p : ℝ) (hp : p ∈ Ioo 0 1) (k : ∀ n : ℕ, Fin ((n+1)*m))
    (hkp : Tendsto (fun n ↦ (((k n).val+1 : ℕ) : ℝ)/(((n+1)*m : ℕ)+1)) atTop (nhds p)) :
    Tendsto (fun n ↦ ∫ ω, normalizedPooledQuantile U (n+1) (k n) ω ∂μ) atTop (nhds 0) := by
  let v := clusterCoverageVariance (μ := μ) U p
  let ν := gaussianReal 0 v
  let Z : ℕ → Ω → ℝ := fun n ↦ normalizedPooledQuantile U (n+1) (k n)
  have hz (n : ℕ) : Measurable (Z n) := measurable_normalizedPooledQuantile U hU (n+1) (k n)
  have hc (x : ℝ) (hx : x ≠ 0) : Tendsto (fun n ↦ μ.real {ω | Z n ω ≤ x}) atTop
      (nhds (ν.real {z : ℝ | z ≤ x})) := by
    simpa only [cdf_eq_real, Z, normalizedPooledQuantile, ν, v, Iic] using
      iid_cluster_coverage_cdf hm U hU hindep hident hu p hp k hkp x (Or.inr hx)
  have hp' (t : ℝ) (ht : 0 < t) : Tendsto (fun n ↦ μ.real {ω | t < Z n ω}) atTop
      (nhds (ν.real {z : ℝ | t < z})) := by
    simp_rw [probability_gt_eq_one_sub_le _ (hz _) t]
    rw [probability_gt_eq_one_sub_le (μ := ν) (fun z : ℝ ↦ z) (by fun_prop) t]
    exact tendsto_const_nhds.sub (hc t ht.ne')
  have hn' (t : ℝ) (ht : 0 < t) : Tendsto (fun n ↦ μ.real {ω | t < -Z n ω}) atTop
      (nhds (ν.real {z : ℝ | t < -z})) := by
    have he (n : ℕ) : μ.real {ω | t < -Z n ω} = μ.real {ω | Z n ω ≤ -t} := by
      have hh : {ω | t < -Z n ω} = {ω | Z n ω < -t} := by ext ω; simp only [mem_setOf_eq]; constructor <;> intro h <;> linarith
      rw [hh, probability_lt_eq_le _ _ (normalizedPooledQuantile_no_atoms U hU hu (n+1) (k n) _)]
    have hv : ν.real {z : ℝ | t < -z} = ν.real {z : ℝ | z ≤ -t} := by
      have hh : {z : ℝ | t < -z} = {z : ℝ | z < -t} := by ext z; simp only [mem_setOf_eq]; constructor <;> intro h <;> linarith
      rw [hh]
      simpa only [id_eq] using probability_lt_eq_le (μ := ν) id (-t)
        (centered_gaussian_no_atom_at_continuity id v HasLaw.id t (Or.inr ht.ne'))
    simp_rw [he]
    rw [hv]
    exact hc _ (neg_ne_zero.mpr ht.ne')
  have hcpos : 0 < 2/(m : ℝ) := div_pos (by norm_num) (by exact_mod_cast hm)
  have hB : IntegrableOn (fun t : ℝ ↦ 2*Real.exp (-(2/(m : ℝ))*t^2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq hcpos).integrableOn.const_mul 2
  have hb (n : ℕ) (t : ℝ) (ht : 0 < t) : μ.real {ω | t < |Z n ω|} ≤
      2*Real.exp (-(2/(m : ℝ))*t^2) := by
    have hh := normalized_pooled_quantile_tail U hU hindep hu (n+1) (k n) t ht.le
    have he : -(2/(m : ℝ))*t^2 = -2*t^2/(m : ℝ) := by ring
    simpa only [he, Z, normalizedPooledQuantile] using hh
  have hl := expectation_limit_of_two_tail_limits (ν := ν) Z id hz measurable_id
    (fun n ↦ (normalizedPooledQuantile_memLp U hU hu (n+1) (k n)).integrable (by norm_num))
    ((memLp_id_gaussianReal' 2 (by norm_num)).integrable (by norm_num)) _ hB hb hp' hn'
  simpa only [id_eq, ν, integral_id_gaussianReal] using hl

/-- The complete rescaled-variance limit for the pooled quantile under iid clusters. -/
theorem iid_pooled_quantile_variance_limit {m : ℕ} (hm : 0 < m)
    (U : ℕ → Ω → Fin m → ℝ) (hU : ∀ j, Measurable (U j))
    (hindep : iIndepFun U μ) (hident : ∀ j, IdentDistrib (U j) (U 0) μ μ)
    (hu : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (p : ℝ) (hp : p ∈ Ioo 0 1) (k : ∀ n : ℕ, Fin ((n+1)*m))
    (hkp : Tendsto (fun n ↦ (((k n).val+1 : ℕ) : ℝ)/(((n+1)*m : ℕ)+1)) atTop (nhds p)) :
    Tendsto (fun n ↦ (((n+1)*m : ℕ) : ℝ) *
      Var[fun ω ↦ sampleQuantile (pooledSample U (n+1) ω) (k n); μ]) atTop
      (nhds (clusterCoverageVariance (μ := μ) U p : ℝ)) := by
  have hmean := iid_pooled_quantile_mean_limit hm U hU hindep hident hu p hp k hkp
  have hsquare := iid_pooled_quantile_second_moment_limit hm U hU hindep hident hu p hp k hkp
  have ht := hsquare.sub (hmean.pow 2)
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at ht
  have he (n : ℕ) : (∫ ω, (normalizedPooledQuantile U (n+1) (k n) ω)^2 ∂μ) -
      (∫ ω, normalizedPooledQuantile U (n+1) (k n) ω ∂μ)^2 =
      (((n+1)*m : ℕ) : ℝ) * Var[fun ω ↦ sampleQuantile (pooledSample U (n+1) ω) (k n); μ] := by
    have hv := variance_eq_sub (normalizedPooledQuantile_memLp U hU hu (n+1) (k n))
    simp only [Pi.pow_apply] at hv
    rw [← hv]
    unfold normalizedPooledQuantile
    rw [variance_const_mul, Real.sq_sqrt (by positivity)]
    congr 1
    apply variance_sub_const
    exact (measurable_sampleQuantile (fun i ω ↦ pooledSample U (n+1) ω i)
      (fun i ↦ (measurable_pi_apply _).comp (hU _)) (k n)).aestronglyMeasurable
  simpa only [he] using ht


/-- Rescaled coverage variance converges under the original iid score model. -/
theorem iid_continuous_score_coverage_variance_limit {m : ℕ} (hm : 0 < m)
    (S : ℕ → Ω → Fin m → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (hident : ∀ j, IdentDistrib (S j) (S 0) μ μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i z, μ.real {ω | S j ω i ≤ z} = F z)
    (p : ℝ) (hp : p ∈ Ioo 0 1) (k : ∀ n : ℕ, Fin ((n+1)*m))
    (hkp : Tendsto (fun n ↦ (((k n).val+1 : ℕ) : ℝ)/(((n+1)*m : ℕ)+1)) atTop (nhds p)) :
    Tendsto (fun n ↦ (((n+1)*m : ℕ) : ℝ) *
      Var[fun ω ↦ F (sampleQuantile (pooledSample S (n+1) ω) (k n)); μ]) atTop
      (nhds (clusterCoverageVariance (μ := μ) (fun j ω i ↦ F (S j ω i)) p : ℝ)) := by
  let T : (Fin m → ℝ) → (Fin m → ℝ) := fun u i ↦ F (u i)
  have hT : Measurable T := measurable_pi_lambda _ (fun i ↦ hF.measurable.comp (measurable_pi_apply i))
  have hu (j : ℕ) (i : Fin m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      μ.real {ω | F (S j ω i) ≤ t} = t :=
    continuous_cdf_transform (fun ω ↦ S j ω i) F hF hmono h0 h1 (hCDF j i) t ht0 ht1
  have hl := iid_pooled_quantile_variance_limit hm (fun j ω i ↦ F (S j ω i))
    (fun j ↦ hT.comp (hS j)) (hindep.comp (fun _ ↦ T) (fun _ ↦ hT))
    (fun j ↦ (hident j).comp hT) hu p hp k hkp
  have he (n : ℕ) (ω : Ω) : sampleQuantile (pooledSample (fun j ω i ↦ F (S j ω i)) (n+1) ω) (k n) =
      F (sampleQuantile (pooledSample S (n+1) ω) (k n)) :=
    sampleQuantile_monotone_map (pooledSample S (n+1) ω) (k n) F hmono
  simpa only [he] using hl

/-- End-to-end rescaled coverage variance limit, including the eventual ceiling-rank rule. -/
theorem iid_continuous_score_ceil_coverage_variance_limit {m : ℕ} (hm : 0 < m)
    (S : ℕ → Ω → Fin m → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (hident : ∀ j, IdentDistrib (S j) (S 0) μ μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i z, μ.real {ω | S j ω i ≤ z} = F z)
    (p : ℝ) (hp : p ∈ Ioo 0 1) (k : ∀ n : ℕ, Fin ((n+1)*m))
    (hceil : ∀ᶠ n in atTop, (k n).val+1 = Nat.ceil (((((n+1)*m : ℕ) : ℝ)+1)*p)) :
    Tendsto (fun n ↦ (((n+1)*m : ℕ) : ℝ) *
      Var[fun ω ↦ F (sampleQuantile (pooledSample S (n+1) ω) (k n)); μ]) atTop
      (nhds (clusterCoverageVariance (μ := μ) (fun j ω i ↦ F (S j ω i)) p : ℝ)) := by
  have hN : Tendsto (fun n : ℕ ↦ (n+1)*m) atTop atTop := by
    apply tendsto_atTop_mono (fun n ↦ show n ≤ (n+1)*m from ?_) tendsto_id
    nlinarith
  exact iid_continuous_score_coverage_variance_limit hm S hS hindep hident F hF hmono h0 h1 hCDF
    p hp k (ceil_rank_levels_tendsto _ _ hN p hp.1.le hceil)


/-- The paper's indicator design-effect formula for the rescaled coverage variance limit. -/
theorem iid_continuous_score_ceil_design_effect_variance_limit {m : ℕ} (hm : 0 < m)
    (S : ℕ → Ω → Fin m → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (hident : ∀ j, IdentDistrib (S j) (S 0) μ μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i z, μ.real {ω | S j ω i ≤ z} = F z)
    (p : ℝ) (hp : p ∈ Ioo 0 1) (k : ∀ n : ℕ, Fin ((n+1)*m))
    (hceil : ∀ᶠ n in atTop, (k n).val+1 = Nat.ceil (((((n+1)*m : ℕ) : ℝ)+1)*p))
    (δ : ℝ)
    (hpair : ∀ i j, i ≠ j → μ.real ({ω | F (S 0 ω i) ≤ p} ∩ {ω | F (S 0 ω j) ≤ p}) = δ) :
    Tendsto (fun n ↦ (((n+1)*m : ℕ) : ℝ) *
      Var[fun ω ↦ F (sampleQuantile (pooledSample S (n+1) ω) (k n)); μ]) atTop
      (nhds (p*(1-p)*(1+((m : ℝ)-1)*((δ-p^2)/(p*(1-p)))))) := by
  have hl := iid_continuous_score_ceil_coverage_variance_limit hm S hS hindep hident
    F hF hmono h0 h1 hCDF p hp k hceil
  have hU : Measurable (fun ω i ↦ F (S 0 ω i)) :=
    measurable_pi_lambda _ (fun i ↦ hF.measurable.comp ((measurable_pi_apply i).comp (hS 0)))
  have hv := clusterCoverageVariance_indicator_formula hm (fun j ω i ↦ F (S j ω i)) hU p δ hp
    (fun i ↦ continuous_cdf_transform (fun ω ↦ S 0 ω i) F hF hmono h0 h1 (hCDF 0 i) p hp.1.le hp.2.le) hpair
  rwa [hv] at hl

end Exceedance
#print axioms Exceedance.normalizedPooledQuantile_no_atoms
#print axioms Exceedance.nonnegative_expectation_limit_of_tail_limit

#print axioms Exceedance.iid_pooled_quantile_second_moment_limit

#print axioms Exceedance.iid_pooled_quantile_mean_limit
#print axioms Exceedance.iid_pooled_quantile_variance_limit

#print axioms Exceedance.iid_continuous_score_coverage_variance_limit
#print axioms Exceedance.iid_continuous_score_ceil_coverage_variance_limit

#print axioms Exceedance.iid_continuous_score_ceil_design_effect_variance_limit
