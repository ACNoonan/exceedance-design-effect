import QuantileConcentration
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- An exponential tail bounds the expected excess above any nonnegative cutoff. -/
theorem exponential_tail_excess_bound (Y : Ω → ℝ) (hY : Measurable Y)
    (hi : Integrable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (A c : ℝ) (hc : 0 < c)
    (htail : ∀ t, 0 ≤ t → μ.real {ω | t < Y ω} ≤ A*Real.exp (-c*t))
    (K : ℝ) (hK : 0 ≤ K) :
    (∫ ω, max (Y ω-K) 0 ∂μ) ≤ A/c*Real.exp (-c*K) := by
  have hf : Integrable (fun ω ↦ max (Y ω-K) 0) μ := by
    apply hi.mono' ((hY.sub_const K).max measurable_const).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) (hY0 ω)
  rw [hf.integral_eq_integral_meas_lt (Eventually.of_forall (fun _ ↦ le_max_right _ _))]
  have hg : IntegrableOn (fun t : ℝ ↦ (A*Real.exp (-c*K))*Real.exp (-c*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -c < 0) 0).const_mul _
  have hb : (fun t ↦ μ.real {ω | t < max (Y ω-K) 0}) ≤ᵐ[volume.restrict (Ioi 0)]
      (fun t ↦ (A*Real.exp (-c*K))*Real.exp (-c*t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have he : {ω | t < max (Y ω-K) 0} = {ω | t+K < Y ω} := by
      ext ω
      simp only [mem_setOf_eq, lt_max_iff]
      constructor
      · intro h; rcases h with h | h <;> linarith [ht]
      · intro h; exact Or.inl (by linarith)
    rw [he]
    calc
      _ ≤ A*Real.exp (-c*(t+K)) := htail (t+K) (by linarith [ht])
      _ = _ := by rw [show -c*(t+K) = -c*K + -c*t by ring, Real.exp_add]; ring
  have hh := integral_mono_of_nonneg (μ := volume.restrict (Ioi 0))
    (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) hg hb
  apply hh.trans_eq
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -c < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  ring

omit [IsProbabilityMeasure μ] in
/-- Large-value expectations tend uniformly to zero under a common exponential tail. -/
theorem exponential_tail_truncation_bound (Y : Ω → ℝ) (hY : Measurable Y)
    (hi : Integrable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (A c : ℝ) (hc : 0 < c)
    (htail : ∀ t, 0 ≤ t → μ.real {ω | t < Y ω} ≤ A*Real.exp (-c*t))
    (K : ℝ) (hK : 0 ≤ K) :
    (∫ ω, {ω | K ≤ Y ω}.indicator Y ω ∂μ) ≤
      (2*A/c)*Real.exp (-c*(K/2)) := by
  have hi' : Integrable (fun ω ↦ max (Y ω-K/2) 0) μ := by
    apply hi.mono' ((hY.sub_const (K/2)).max measurable_const).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) (hY0 ω)
  have hbound : ∀ ω, {ω | K ≤ Y ω}.indicator Y ω ≤ 2*max (Y ω-K/2) 0 := by
    intro ω
    by_cases h : K ≤ Y ω
    · rw [indicator_of_mem (show ω ∈ {ω | K ≤ Y ω} from h), max_eq_left (by linarith)]
      linarith
    · rw [indicator_of_notMem (show ω ∉ {ω | K ≤ Y ω} from h)]
      positivity
  have hh := integral_mono (hi.indicator (measurableSet_le measurable_const hY))
    (hi'.const_mul 2) hbound
  rw [integral_const_mul] at hh
  have ht := exponential_tail_excess_bound Y hY hi hY0 A c hc htail (K/2) (by positivity)
  calc
    _ ≤ 2*(A/c*Real.exp (-c*(K/2))) := hh.trans (mul_le_mul_of_nonneg_left ht (by norm_num))
    _ = _ := by ring


/-- A common exponential tail implies uniform integrability for nonnegative integrable variables. -/
theorem uniformIntegrable_of_exponential_tail {ι : Type*} (Y : ι → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hi : ∀ i, Integrable (Y i) μ)
    (hY0 : ∀ i ω, 0 ≤ Y i ω) (A c : ℝ) (hc : 0 < c)
    (htail : ∀ i t, 0 ≤ t → μ.real {ω | t < Y i ω} ≤ A*Real.exp (-c*t)) :
    UniformIntegrable Y 1 μ := by
  apply uniformIntegrable_of (by norm_num) (by norm_num) (fun i ↦ (hY i).aestronglyMeasurable)
  intro ε hε
  have hl : Tendsto (fun K : ℝ ↦ (2*A/c)*Real.exp ((-c/2)*K)) atTop (nhds 0) := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (by linarith : -c/2 < 0) tendsto_id)
    simpa using he.const_mul (2*A/c)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hl.eventually (gt_mem_nhds hε))
  let C : NNReal := ⟨max K 0, le_max_right _ _⟩
  refine ⟨C, fun i ↦ ?_⟩
  have hset : {ω | C ≤ ‖Y i ω‖₊} = {ω | (C : ℝ) ≤ Y i ω} := by
    ext ω
    change C ≤ ‖Y i ω‖₊ ↔ (C : ℝ) ≤ Y i ω
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (hY0 i ω)]
  rw [hset, eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm ((hi i).indicator (measurableSet_le measurable_const (hY i)))]
  have hn (ω : Ω) : ‖{ω | (C : ℝ) ≤ Y i ω}.indicator (Y i) ω‖ =
      {ω | (C : ℝ) ≤ Y i ω}.indicator (Y i) ω := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact indicator_nonneg (fun ω _ ↦ hY0 i ω) _
  simp_rw [hn]
  apply ENNReal.ofReal_le_ofReal
  have hb := exponential_tail_truncation_bound (Y i) (hY i) (hi i) (hY0 i)
    A c hc (htail i) C C.coe_nonneg
  have hsmall := hK (C : ℝ) (le_max_left K 0)
  have he : -c*((C : ℝ)/2) = (-c/2)*(C : ℝ) := by ring
  rw [he] at hb
  exact hb.trans hsmall.le

omit [IsProbabilityMeasure μ] in
/-- Squaring a variable with a Gaussian tail gives an exponential tail. -/
theorem gaussian_tail_square_tail (Z : Ω → ℝ) (m : ℝ)
    (htail : ∀ y, 0 ≤ y → μ.real {ω | y < |Z ω|} ≤ 2*Real.exp (-2*y^2/m))
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t < (Z ω)^2} ≤ 2*Real.exp (-(2/m)*t) := by
  have he : {ω | t < (Z ω)^2} = {ω | Real.sqrt t < |Z ω|} := by
    ext ω
    simp only [mem_setOf_eq]
    have hs := Real.sq_sqrt ht
    have hsn := Real.sqrt_nonneg t
    have ha := abs_nonneg (Z ω)
    have hsq := sq_abs (Z ω)
    constructor <;> (intro h; nlinarith)
  rw [he]
  have hh := htail (Real.sqrt t) (Real.sqrt_nonneg t)
  rw [Real.sq_sqrt ht] at hh
  have he' : -(2/m)*t = -2*t/m := by ring
  rwa [he']


noncomputable def normalizedPooledQuantile {m : ℕ} (U : ℕ → Ω → Fin m → ℝ)
    (b : ℕ) (k : Fin (b*m)) (ω : Ω) : ℝ :=
  Real.sqrt (b*m : ℕ) * (sampleQuantile (pooledSample U b ω) k -
    ((k.val+1 : ℕ) : ℝ)/((b*m : ℕ)+1))

omit [IsProbabilityMeasure μ] in
lemma measurable_normalizedPooledQuantile {m : ℕ} (U : ℕ → Ω → Fin m → ℝ)
    (hU : ∀ j, Measurable (U j)) (b : ℕ) (k : Fin (b*m)) :
    Measurable (normalizedPooledQuantile U b k) := by
  have hC : Measurable (fun ω ↦ sampleQuantile (pooledSample U b ω) k) :=
    measurable_sampleQuantile (fun i ω ↦ pooledSample U b ω i)
      (fun i ↦ (measurable_pi_apply _).comp (hU _)) k
  exact (hC.sub_const _).const_mul _

lemma normalizedPooledQuantile_memLp {m : ℕ} (U : ℕ → Ω → Fin m → ℝ)
    (hU : ∀ j, Measurable (U j))
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (b : ℕ) (k : Fin (b*m)) : MemLp (normalizedPooledQuantile U b k) 2 μ := by
  have hC : Measurable (fun ω ↦ sampleQuantile (pooledSample U b ω) k) :=
    measurable_sampleQuantile (fun i ω ↦ pooledSample U b ω i)
      (fun i ↦ (measurable_pi_apply _).comp (hU _)) k
  have hc := memLp_of_bounded (pooled_quantile_support U hU hunif b k) hC.aestronglyMeasurable 2
  exact (hc.sub (memLp_const _)).const_mul _

/-- Squared normalized quantile errors are uniformly integrable across all sample sizes and ranks. -/
theorem pooled_quantile_square_uniformIntegrable {m : ℕ} (hm : 0 < m)
    (U : ℕ → Ω → Fin m → ℝ) (hU : ∀ j, Measurable (U j)) (hindep : iIndepFun U μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (b : ℕ → ℕ) (k : ∀ n, Fin (b n*m)) :
    UniformIntegrable (fun n ω ↦ (normalizedPooledQuantile U (b n) (k n) ω)^2) 1 μ := by
  apply uniformIntegrable_of_exponential_tail _
    (fun n ↦ (measurable_normalizedPooledQuantile U hU (b n) (k n)).pow_const 2)
    (fun n ↦ (normalizedPooledQuantile_memLp U hU hunif (b n) (k n)).integrable_sq)
    (fun _ _ ↦ sq_nonneg _) 2 (2/(m : ℝ)) (by positivity)
  intro n t ht
  exact gaussian_tail_square_tail _ _ (normalized_pooled_quantile_tail U hU hindep hunif (b n) (k n)) t ht

/-- The second moment is bounded uniformly; this does not yet identify its limit. -/
theorem pooled_quantile_second_moment_bound {m : ℕ} (hm : 0 < m)
    (U : ℕ → Ω → Fin m → ℝ) (hU : ∀ j, Measurable (U j)) (hindep : iIndepFun U μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (b : ℕ) (k : Fin (b*m)) :
    (∫ ω, (normalizedPooledQuantile U b k ω)^2 ∂μ) ≤ (m : ℝ) := by
  have hi := (normalizedPooledQuantile_memLp U hU hunif b k).integrable_sq
  have ht := exponential_tail_excess_bound (fun ω ↦ (normalizedPooledQuantile U b k ω)^2)
    ((measurable_normalizedPooledQuantile U hU b k).pow_const 2) hi (fun _ ↦ sq_nonneg _)
    2 (2/(m : ℝ)) (by positivity)
    (gaussian_tail_square_tail _ _ (normalized_pooled_quantile_tail U hU hindep hunif b k)) 0 le_rfl
  have he : (2 : ℝ)/(2/(m : ℝ)) = (m : ℝ) := by field_simp
  simpa only [sub_zero, max_eq_left (sq_nonneg _), mul_zero, Real.exp_zero, mul_one, he] using ht

/-- Explicit large-value control used in the uniform-integrability proof. -/
theorem pooled_quantile_square_truncation_bound {m : ℕ} (hm : 0 < m)
    (U : ℕ → Ω → Fin m → ℝ) (hU : ∀ j, Measurable (U j)) (hindep : iIndepFun U μ)
    (hunif : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t)
    (b : ℕ) (k : Fin (b*m)) (K : ℝ) (hK : 0 ≤ K) :
    (∫ ω, {ω | K ≤ (normalizedPooledQuantile U b k ω)^2}.indicator
      (fun ω ↦ (normalizedPooledQuantile U b k ω)^2) ω ∂μ) ≤
      2*(m : ℝ)*Real.exp (-K/(m : ℝ)) := by
  have ht := exponential_tail_truncation_bound (fun ω ↦ (normalizedPooledQuantile U b k ω)^2)
    ((measurable_normalizedPooledQuantile U hU b k).pow_const 2)
    (normalizedPooledQuantile_memLp U hU hunif b k).integrable_sq (fun _ ↦ sq_nonneg _)
    2 (2/(m : ℝ)) (by positivity)
    (gaussian_tail_square_tail _ _ (normalized_pooled_quantile_tail U hU hindep hunif b k)) K hK
  convert ht using 1
  congr 1 <;> field_simp


/-- Uniform integrability on the true coverage scale follows from the original score model. -/
theorem continuous_score_coverage_square_uniformIntegrable {m : ℕ} (hm : 0 < m)
    (S : ℕ → Ω → Fin m → ℝ) (hS : ∀ j, Measurable (S j)) (hindep : iIndepFun S μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ j i t, μ.real {ω | S j ω i ≤ t} = F t)
    (b : ℕ → ℕ) (k : ∀ n, Fin (b n*m)) :
    UniformIntegrable (fun n ω ↦ (Real.sqrt (b n*m : ℕ) *
      (F (sampleQuantile (pooledSample S (b n) ω) (k n)) -
        (((k n).val+1 : ℕ) : ℝ)/((b n*m : ℕ)+1)))^2) 1 μ := by
  let T : (Fin m → ℝ) → (Fin m → ℝ) := fun u i ↦ F (u i)
  have hT : Measurable T := measurable_pi_lambda _ (fun i ↦ hF.measurable.comp (measurable_pi_apply i))
  let U : ℕ → Ω → Fin m → ℝ := fun j ω i ↦ F (S j ω i)
  have hU (j : ℕ) : Measurable (U j) := hT.comp (hS j)
  have hi : iIndepFun U μ := hindep.comp (fun _ ↦ T) (fun _ ↦ hT)
  have hu : ∀ j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U j ω i ≤ t} = t := by
    intro j i t ht0 ht1
    exact continuous_cdf_transform (fun ω ↦ S j ω i) F hF hmono h0 h1 (hCDF j i) t ht0 ht1
  have ht := pooled_quantile_square_uniformIntegrable hm U hU hi hu b k
  have he (n : ℕ) (ω : Ω) : sampleQuantile (pooledSample U (b n) ω) (k n) =
      F (sampleQuantile (pooledSample S (b n) ω) (k n)) :=
    sampleQuantile_monotone_map (pooledSample S (b n) ω) (k n) F hmono
  simpa only [normalizedPooledQuantile, he] using ht

end Exceedance
#print axioms Exceedance.exponential_tail_excess_bound
#print axioms Exceedance.exponential_tail_truncation_bound

#print axioms Exceedance.uniformIntegrable_of_exponential_tail
#print axioms Exceedance.gaussian_tail_square_tail

#print axioms Exceedance.pooled_quantile_square_uniformIntegrable
#print axioms Exceedance.pooled_quantile_second_moment_bound
#print axioms Exceedance.pooled_quantile_square_truncation_bound

#print axioms Exceedance.continuous_score_coverage_square_uniformIntegrable
