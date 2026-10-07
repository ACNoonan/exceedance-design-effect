import RaggedModel

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance.RaggedUniformModel
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (G : RaggedUniformModel Ω μ)

/-- Proposition 2's Gaussian CDF limit for the actual pooled unequal-size sample. -/
theorem coverage_cdf (p : ℝ) (hp : p ∈ Ioo 0 1)
    (k : ∀ n, Fin (G.N n))
    (hkp : Tendsto (fun n ↦ ((k n).val+1 : ℝ)/((G.N n : ℝ)+1)) atTop (nhds p))
    (x : ℝ) (hx : (G.varianceLimit p).toNNReal ≠ 0 ∨ x ≠ 0) :
    Tendsto (fun n ↦ μ.real {ω | normalizedRaggedQuantile (G.m n) (G.U n) (k n) ω ≤ x})
      atTop (nhds (cdf (gaussianReal 0 (G.varianceLimit p).toNNReal) x)) := by
  have hi : Tendsto (fun n ↦ (Real.sqrt (G.N n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp G.N_grows))
  let t := fun n ↦ ((k n).val+1 : ℝ)/((G.N n : ℝ)+1)+x/Real.sqrt (G.N n)
  have ht : Tendsto t atTop (nhds p) := by
    simpa only [mul_zero, add_zero, ← div_eq_mul_inv] using hkp.add (hi.const_mul x)
  have hc := G.moving_count_interior_clt p hp t ht
  have hh := coverage_probability_limit_of_gaussian_count_limit (μ := μ) G.N
    (fun n i ω ↦ raggedSample (G.m n) (G.U n) ω i) k G.N_grows id monotone_id x id
    (G.varianceLimit p).toNNReal (by
      convert hc using 1
      funext n ω
      simp only [id_eq, Nat.cast_add, Nat.cast_one, t]
      congr 2
      exact raggedSample_count (G.m n) (G.U n) ω (t n))
    HasLaw.id hx
  simpa only [id_eq, normalizedRaggedQuantile, Nat.cast_add, Nat.cast_one, N] using hh

lemma quantile_no_atoms (n : ℕ) (k : Fin (G.N n)) (a : ℝ) :
    μ {ω | normalizedRaggedQuantile (G.m n) (G.U n) k ω = a} = 0 := by
  have hn : 0 < (G.N n : ℝ) := by exact_mod_cast G.N_pos n
  have hr := Real.sqrt_pos.mpr hn
  let p : ℝ := (k.val+1 : ℝ)/((G.N n : ℝ)+1)
  have hc := sampleQuantile_no_atoms (μ := μ) (fun i ω ↦ raggedSample (G.m n) (G.U n) ω i)
    (fun i t ↦ uniform_marginal_no_atoms _ ((measurable_pi_apply _).comp (G.measurable n _)) (G.uniform n _ _) t)
    k (p+a/Real.sqrt (G.N n))
  apply measure_mono_null _ hc
  intro ω hω
  change Real.sqrt (G.N n)*(sampleQuantile (raggedSample (G.m n) (G.U n) ω) k-p) = a at hω
  change sampleQuantile (raggedSample (G.m n) (G.U n) ω) k = p+a/Real.sqrt (G.N n)
  have hd : sampleQuantile (raggedSample (G.m n) (G.U n) ω) k-p = a/Real.sqrt (G.N n) :=
    (eq_div_iff hr.ne').mpr (by nlinarith [hω])
  linarith

/-- The second moment follows from the proved CDF limit and the common tail bound. -/
theorem second_moment_limit (p : ℝ) (hp : p ∈ Ioo 0 1) (k : ∀ n, Fin (G.N n))
    (hkp : Tendsto (fun n ↦ ((k n).val+1 : ℝ)/((G.N n : ℝ)+1)) atTop (nhds p)) :
    Tendsto (fun n ↦ ∫ ω, (normalizedRaggedQuantile (G.m n) (G.U n) (k n) ω)^2 ∂μ) atTop
      (nhds ((G.varianceLimit p).toNNReal : ℝ)) := by
  let v := (G.varianceLimit p).toNNReal
  let ν := gaussianReal 0 v
  let Z : ℕ → Ω → ℝ := fun n ↦ normalizedRaggedQuantile (G.m n) (G.U n) (k n)
  have hz (n : ℕ) : Measurable (Z n) := measurable_normalizedRaggedQuantile (G.m n) (G.U n) (G.measurable n) (k n)
  have hc (x : ℝ) (hx : x ≠ 0) : Tendsto (fun n ↦ μ.real {ω | Z n ω ≤ x}) atTop
      (nhds (ν.real {z : ℝ | z ≤ x})) := by
    simpa only [cdf_eq_real, Z, normalizedRaggedQuantile, ν, v, Iic] using G.coverage_cdf p hp k hkp x (Or.inr hx)
  have ht (t : ℝ) (ht : 0 < t) : Tendsto (fun n ↦ μ.real {ω | t < (Z n ω)^2}) atTop
      (nhds (ν.real {z : ℝ | t < z^2})) := by
    have hs := Real.sqrt_pos.mpr ht
    have ha : ν {z : ℝ | z = -Real.sqrt t} = 0 :=
      centered_gaussian_no_atom_at_continuity id v HasLaw.id _ (Or.inr hs.ne')
    have he (n : ℕ) := square_tail_cdf_identity (Z n) (hz n) t ht
      (G.quantile_no_atoms n (k n) _)
    have hv := square_tail_cdf_identity (μ := ν) id measurable_id t ht ha
    simp only [id_eq] at hv
    simp_rw [he]
    rw [hv]
    exact (hc _ (neg_ne_zero.mpr hs.ne')).add (tendsto_const_nhds.sub (hc _ hs.ne'))
  have hiW : Integrable (fun z : ℝ ↦ z^2) ν :=
    (memLp_id_gaussianReal' 2 (by norm_num)).integrable_sq
  have hB : IntegrableOn (fun t : ℝ ↦ 2*Real.exp (-(2/G.M)*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (div_pos (by norm_num) G.M_pos)) 0).const_mul 2
  have hl := nonnegative_expectation_limit_of_tail_limit (ν := ν)
    (fun n ω ↦ (Z n ω)^2) (fun z : ℝ ↦ z^2)
    (fun n ↦ (normalizedRaggedQuantile_memLp (G.m n) (G.U n) (G.measurable n) (G.uniform n) (k n)).integrable_sq) hiW
    (fun _ _ ↦ sq_nonneg _) (fun _ ↦ sq_nonneg _) _ hB
    (fun n t ht ↦ gaussian_tail_square_tail _ _
      (ragged_normalized_quantile_tail (G.m n) (G.U n) (G.measurable n) (G.independent n) (G.uniform n) G.M G.M_pos (G.size_le n) (k n)) t ht.le) ht
  have hv : (∫ z : ℝ, z^2 ∂ν) = (v : ℝ) := by
    have hh := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
    rw [variance_eq_integral (X := fun z : ℝ ↦ z) (by fun_prop)] at hh
    simpa only [integral_id_gaussianReal, sub_zero] using hh
  rwa [hv] at hl


/-- The normalized coverage error has vanishing mean. -/
theorem mean_limit (p : ℝ) (hp : p ∈ Ioo 0 1) (k : ∀ n, Fin (G.N n))
    (hkp : Tendsto (fun n ↦ ((k n).val+1 : ℝ)/((G.N n : ℝ)+1)) atTop (nhds p)) :
    Tendsto (fun n ↦ ∫ ω, normalizedRaggedQuantile (G.m n) (G.U n) (k n) ω ∂μ) atTop
      (nhds (0:ℝ)) := by
  let v := (G.varianceLimit p).toNNReal
  let ν := gaussianReal 0 v
  let Z : ℕ → Ω → ℝ := fun n ↦ normalizedRaggedQuantile (G.m n) (G.U n) (k n)
  have hz (n : ℕ) : Measurable (Z n) := measurable_normalizedRaggedQuantile (G.m n) (G.U n) (G.measurable n) (k n)
  have hc (x : ℝ) (hx : x ≠ 0) : Tendsto (fun n ↦ μ.real {ω | Z n ω ≤ x}) atTop
      (nhds (ν.real {z : ℝ | z ≤ x})) := by
    simpa only [cdf_eq_real, Z, normalizedRaggedQuantile, ν, v, Iic] using
      G.coverage_cdf p hp k hkp x (Or.inr hx)
  have hp' (t : ℝ) (ht : 0 < t) : Tendsto (fun n ↦ μ.real {ω | t < Z n ω}) atTop
      (nhds (ν.real {z : ℝ | t < z})) := by
    simp_rw [probability_gt_eq_one_sub_le _ (hz _) t]
    rw [probability_gt_eq_one_sub_le (μ := ν) (fun z : ℝ ↦ z) (by fun_prop) t]
    exact tendsto_const_nhds.sub (hc t ht.ne')
  have hn' (t : ℝ) (ht : 0 < t) : Tendsto (fun n ↦ μ.real {ω | t < -Z n ω}) atTop
      (nhds (ν.real {z : ℝ | t < -z})) := by
    have he (n : ℕ) : μ.real {ω | t < -Z n ω} = μ.real {ω | Z n ω ≤ -t} := by
      have hh : {ω | t < -Z n ω} = {ω | Z n ω < -t} := by ext ω; simp only [mem_setOf_eq]; constructor <;> intro h <;> linarith
      rw [hh, probability_lt_eq_le _ _ (G.quantile_no_atoms n (k n) _)]
    have hv : ν.real {z : ℝ | t < -z} = ν.real {z : ℝ | z ≤ -t} := by
      have hh : {z : ℝ | t < -z} = {z : ℝ | z < -t} := by ext z; simp only [mem_setOf_eq]; constructor <;> intro h <;> linarith
      rw [hh]
      simpa only [id_eq] using probability_lt_eq_le (μ := ν) id (-t)
        (centered_gaussian_no_atom_at_continuity id v HasLaw.id t (Or.inr ht.ne'))
    simp_rw [he]
    rw [hv]
    exact hc _ (neg_ne_zero.mpr ht.ne')
  have hcpos : 0 < 2/G.M := div_pos (by norm_num) G.M_pos
  have hB : IntegrableOn (fun t : ℝ ↦ 2*Real.exp (-(2/G.M)*t^2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq hcpos).integrableOn.const_mul 2
  have hb (n : ℕ) (t : ℝ) (ht : 0 < t) : μ.real {ω | t < |Z n ω|} ≤
      2*Real.exp (-(2/G.M)*t^2) := by
    have hh := ragged_normalized_quantile_tail (G.m n) (G.U n) (G.measurable n) (G.independent n) (G.uniform n) G.M G.M_pos (G.size_le n) (k n) t ht.le
    have he : -(2/G.M)*t^2 = -2*t^2/G.M := by ring
    simpa only [he, Z, normalizedRaggedQuantile] using hh
  have hl := expectation_limit_of_two_tail_limits (ν := ν) Z id hz measurable_id
    (fun n ↦ (normalizedRaggedQuantile_memLp (G.m n) (G.U n) (G.measurable n) (G.uniform n) (k n)).integrable (by norm_num))
    ((memLp_id_gaussianReal' 2 (by norm_num)).integrable (by norm_num)) _ hB hb hp' hn'
  simpa only [id_eq, ν, integral_id_gaussianReal] using hl


/-- Proposition 2's rescaled variance limit, derived from both moment limits. -/
theorem coverage_variance_limit (p : ℝ) (hp : p ∈ Ioo 0 1) (k : ∀ n, Fin (G.N n))
    (hkp : Tendsto (fun n ↦ ((k n).val+1 : ℝ)/((G.N n : ℝ)+1)) atTop (nhds p)) :
    Tendsto (fun n ↦ (G.N n : ℝ)*Var[fun ω ↦ sampleQuantile (raggedSample (G.m n) (G.U n) ω) (k n); μ])
      atTop (nhds (G.varianceLimit p)) := by
  have ht := (G.second_moment_limit p hp k hkp).sub ((G.mean_limit p hp k hkp).pow 2)
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), sub_zero,
    Real.coe_toNNReal _ (G.varianceLimit_nonneg p hp)] at ht
  have he (n : ℕ) : (∫ ω, (normalizedRaggedQuantile (G.m n) (G.U n) (k n) ω)^2 ∂μ) -
      (∫ ω, normalizedRaggedQuantile (G.m n) (G.U n) (k n) ω ∂μ)^2 =
      (G.N n : ℝ)*Var[fun ω ↦ sampleQuantile (raggedSample (G.m n) (G.U n) ω) (k n); μ] := by
    have hv := variance_eq_sub (normalizedRaggedQuantile_memLp (G.m n) (G.U n) (G.measurable n) (G.uniform n) (k n))
    simp only [Pi.pow_apply] at hv
    rw [← hv]
    unfold normalizedRaggedQuantile
    rw [variance_const_mul, Real.sq_sqrt (by positivity)]
    congr 1
    apply variance_sub_const
    exact (measurable_sampleQuantile _ (fun _ ↦ (measurable_pi_apply _).comp (G.measurable n _)) (k n)).aestronglyMeasurable
  simpa only [he] using ht

/-- Both conclusions of Proposition 2 with the paper's ceiling-rank rule. -/
theorem ceil_coverage_certificate (p : ℝ) (hp : p ∈ Ioo 0 1) (k : ∀ n, Fin (G.N n))
    (hceil : ∀ᶠ n in atTop, (k n).val+1 = Nat.ceil (((G.N n : ℝ)+1)*p)) :
    (∀ x : ℝ, (G.varianceLimit p).toNNReal ≠ 0 ∨ x ≠ 0 →
      Tendsto (fun n ↦ μ.real {ω | normalizedRaggedQuantile (G.m n) (G.U n) (k n) ω ≤ x})
        atTop (nhds (cdf (gaussianReal 0 (G.varianceLimit p).toNNReal) x))) ∧
    Tendsto (fun n ↦ (G.N n : ℝ)*Var[fun ω ↦ sampleQuantile (raggedSample (G.m n) (G.U n) ω) (k n); μ])
      atTop (nhds (p*(1-p)*(1+(G.sizeLimit-1)*G.rho p))) := by
  have hk := ceil_rank_levels_tendsto G.N (fun n ↦ (k n).val+1) G.N_grows p hp.1.le hceil
  simp only [Nat.cast_add, Nat.cast_one] at hk
  exact ⟨fun x hx ↦ G.coverage_cdf p hp k hk x hx, G.coverage_variance_limit p hp k hk⟩

end Exceedance.RaggedUniformModel
#print axioms Exceedance.RaggedUniformModel.coverage_cdf
#print axioms Exceedance.RaggedUniformModel.second_moment_limit
#print axioms Exceedance.RaggedUniformModel.mean_limit

#print axioms Exceedance.RaggedUniformModel.coverage_variance_limit
#print axioms Exceedance.RaggedUniformModel.ceil_coverage_certificate
