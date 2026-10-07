import EstimatorConsistency

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Pooled row fractions converge to the size-weighted population target under iid clusters.
The two coordinates are cluster size and the within-cluster fraction below a fixed threshold. -/
theorem iid_row_target_limit (Y : ℕ → Ω → ℝ × ℝ) (hY : ∀ j, Measurable (Y j))
    (hi : iIndepFun Y μ) (hid : ∀ j, IdentDistrib (Y j) (Y 0) μ μ)
    (hM : Integrable (fun ω ↦ (Y 0 ω).1) μ)
    (hpos : 0 < ∫ ω, (Y 0 ω).1 ∂μ)
    (hsize : ∀ᵐ ω ∂μ, 0 ≤ (Y 0 ω).1)
    (hG : ∀ᵐ ω ∂μ, (Y 0 ω).2 ∈ Icc 0 1) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (∑ j ∈ Finset.range n, (Y j ω).1*(Y j ω).2)/
      (∑ j ∈ Finset.range n, (Y j ω).1)) atTop
      (nhds ((∫ ω, (Y 0 ω).1*(Y 0 ω).2 ∂μ)/(∫ ω, (Y 0 ω).1 ∂μ))) := by
  let f : ℝ × ℝ → ℝ := fun z ↦ z.1*z.2
  have hf : Measurable f := measurable_fst.mul measurable_snd
  have hfi : Integrable (fun ω ↦ f (Y 0 ω)) μ := by
    apply hM.mono' (hf.comp (hY 0)).aestronglyMeasurable
    filter_upwards [hsize,hG] with ω hm hg
    change ‖(Y 0 ω).1*(Y 0 ω).2‖ ≤ (Y 0 ω).1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hm hg.1)]
    nlinarith [hg.2]
  have hin := hi.comp (fun _ ↦ f) (fun _ ↦ hf)
  have him := hi.comp (fun _ ↦ Prod.fst) (fun _ ↦ measurable_fst)
  have hs1 := strong_law_ae_real (fun j ω ↦ f (Y j ω)) hfi
    (fun i j hij ↦ hin.indepFun hij) (fun j ↦ (hid j).comp hf)
  have hs2 := strong_law_ae_real (fun j ω ↦ (Y j ω).1) hM
    (fun i j hij ↦ him.indepFun hij) (fun j ↦ (hid j).comp measurable_fst)
  filter_upwards [hs1,hs2] with ω h1 h2
  apply (h1.div h2 hpos.ne').congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp [f]
  field_simp

/-- The row target differs from the cluster target by covariance divided by mean size.
Only first moments and the integrable product are required. -/
theorem row_target_covariance_difference (M G : Ω → ℝ)
    (hM : Integrable M μ) (hG : Integrable G μ)
    (hMG : Integrable (fun ω ↦ M ω*G ω) μ) (hm : (∫ ω, M ω ∂μ) ≠ 0) :
    (∫ ω, M ω*G ω ∂μ)/(∫ ω, M ω ∂μ) - (∫ ω, G ω ∂μ) =
      cov[M,G;μ]/(∫ ω, M ω ∂μ) := by
  have hc : cov[M,G;μ] = (∫ ω, M ω*G ω ∂μ) - (∫ ω, M ω ∂μ)*(∫ ω, G ω ∂μ) := by
    unfold covariance
    have he (ω : Ω) : (M ω-μ[M])*(G ω-μ[G]) =
        (M ω*G ω - M ω*μ[G])-(μ[M]*G ω-μ[M]*μ[G]) := by ring
    simp_rw [he]
    have hi1 : Integrable (fun ω ↦ M ω*G ω-M ω*μ[G]) μ := hMG.sub (hM.mul_const _)
    have hi2 : Integrable (fun ω ↦ μ[M]*G ω-μ[M]*μ[G]) μ :=
      (hG.const_mul _).sub (integrable_const _)
    rw [integral_sub hi1 hi2,
      integral_sub hMG (hM.mul_const _), integral_sub (hG.const_mul _) (integrable_const _),
      integral_mul_const, integral_const_mul, integral_const, probReal_univ, one_smul]
    ring
  rw [hc]
  field_simp

end Exceedance
#print axioms Exceedance.iid_row_target_limit
#print axioms Exceedance.row_target_covariance_difference
