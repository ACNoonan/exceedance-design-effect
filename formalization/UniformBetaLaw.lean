import UniformCountLaw
import BetaOrderPolynomial

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

lemma unitUniform_ae_open : ∀ᵐ x ∂unitUniform, x ∈ Ioo (0:ℝ) 1 := by
  have h0 : ∀ᵐ x ∂unitUniform, x ≠ 0 := by simp [ae_iff]
  have h1 : ∀ᵐ x ∂unitUniform, x ≠ 1 := by simp [ae_iff]
  filter_upwards [unitUniform_ae,h0,h1] with x hx hx0 hx1
  exact ⟨lt_of_le_of_ne hx.1 hx0.symm, lt_of_le_of_ne hx.2 hx1⟩

lemma beta_ae_open (a b : ℝ) : ∀ᵐ x ∂betaMeasure a b, x ∈ Ioo (0:ℝ) 1 := by
  rw [ae_iff]
  change (betaMeasure a b) (Ioo (0:ℝ) 1)ᶜ = 0
  rw [betaMeasure, withDensity_apply _ measurableSet_Ioo.compl]
  apply setLIntegral_eq_zero measurableSet_Ioo.compl
  intro x hx
  have hh : ¬ (0 < x ∧ x < 1) := hx
  simp [betaPDF, betaPDFReal, hh]

lemma probability_eq_of_interior_cdf {ν ξ : Measure ℝ}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    (hn : ∀ᵐ x ∂ν, x ∈ Ioo (0:ℝ) 1) (hx : ∀ᵐ x ∂ξ, x ∈ Ioo (0:ℝ) 1)
    (he : ∀ p ∈ Ioo (0:ℝ) 1, ν.real (Iic p) = ξ.real (Iic p)) : ν = ξ := by
  apply Measure.eq_of_cdf
  ext p
  rw [cdf_eq_real, cdf_eq_real]
  by_cases h0 : p ≤ 0
  · have hz (η : Measure ℝ) (hη : ∀ᵐ x ∂η, x ∈ Ioo (0:ℝ) 1) : η (Iic p) = 0 := by
      have hnot : ∀ᵐ x ∂η, ¬ x ≤ p := hη.mono (fun x h ↦ by linarith [h.1])
      simpa only [ae_iff, not_not, Iic] using hnot
    simp [measureReal_def,hz ν hn,hz ξ hx]
  by_cases h1 : 1 ≤ p
  · have ho (η : Measure ℝ) [IsProbabilityMeasure η]
        (hη : ∀ᵐ x ∂η, x ∈ Ioo (0:ℝ) 1) : η.real (Iic p) = 1 := by
      rw [measureReal_def, (mem_ae_iff_prob_eq_one measurableSet_Iic).mp
        (hη.mono (fun x h ↦ h.2.le.trans h1)), ENNReal.toReal_one]
    rw [ho ν hn, ho ξ hx]
  exact he p ⟨lt_of_not_ge h0,lt_of_not_ge h1⟩

/-- The exact Beta law of an iid uniform order statistic. -/
theorem uniform_orderStatistic_beta_law {n : ℕ} (k : Fin n) :
    (Measure.pi (fun _ : Fin n ↦ unitUniform)).map (fun x ↦ sampleQuantile x k) =
      betaMeasure (k.val+1) (n-k.val) := by
  let P := Measure.pi (fun _ : Fin n ↦ unitUniform)
  let Q := fun x : Fin n → ℝ ↦ sampleQuantile x k
  have hQ : Measurable Q := measurable_sampleQuantile _ measurable_pi_apply k
  letI : IsProbabilityMeasure (P.map Q) := Measure.isProbabilityMeasure_map hQ.aemeasurable
  letI : IsProbabilityMeasure (betaMeasure (k.val+1) (n-k.val)) :=
    isProbabilityMeasureBeta (by positivity) (sub_pos.mpr (by exact_mod_cast k.isLt))
  have hsupport : ∀ᵐ x ∂P, Q x ∈ Ioo (0:ℝ) 1 := by
    have hall : ∀ᵐ x ∂P, ∀ i, x i ∈ Ioo (0:ℝ) 1 := by
      apply ae_all_iff.mpr
      intro i
      exact (measurePreserving_eval (fun _ : Fin n ↦ unitUniform) i).quasiMeasurePreserving.ae unitUniform_ae_open
    filter_upwards [hall] with x hx
    exact hx _
  apply probability_eq_of_interior_cdf
    ((ae_map_iff hQ.aemeasurable (measurableSet_Ioo)).mpr hsupport) (beta_ae_open _ _)
  intro p hp
  rw [map_measureReal_apply hQ measurableSet_Iic, beta_order_cdf_interior n k.val k.isLt p hp]
  have hs := uniform_orderStatistic_survival k p ⟨hp.1.le,hp.2.le⟩
  have hcompl : {x : Fin n → ℝ | p < sampleQuantile x k} =
      {x | sampleQuantile x k ≤ p}ᶜ := by ext x; simp
  rw [hcompl, measureReal_compl (measurableSet_le hQ measurable_const), probReal_univ] at hs
  rw [binomialSurvivalPolynomial_eval]
  change P.real {x | Q x ≤ p} = _
  dsimp [P,Q] at *
  linarith

/-- The exact law transfers to any measurable independent uniform sample. -/
theorem iid_uniform_orderStatistic_beta_law {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hi : iIndepFun X μ) (hu : ∀ i, μ.map (X i) = unitUniform) (k : Fin n) :
    μ.map (fun ω ↦ sampleQuantile (fun i ↦ X i ω) k) = betaMeasure (k.val+1) (n-k.val) := by
  have hm := hi.map_fun_eq_pi_map (fun i ↦ (hX i).aemeasurable)
  simp_rw [hu] at hm
  have hq : Measurable (fun x : Fin n → ℝ ↦ sampleQuantile x k) :=
    measurable_sampleQuantile _ measurable_pi_apply k
  rw [show (fun ω ↦ sampleQuantile (fun i ↦ X i ω) k) =
      (fun x ↦ sampleQuantile x k) ∘ (fun ω i ↦ X i ω) from rfl,
    ← Measure.map_map hq (measurable_pi_lambda _ hX), hm, uniform_orderStatistic_beta_law]

end Exceedance
#print axioms Exceedance.uniform_orderStatistic_beta_law
#print axioms Exceedance.iid_uniform_orderStatistic_beta_law
