import OrderStatisticRanks

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

/-- The actual uniform probability measure on the unit interval. -/
noncomputable def unitUniform : Measure ℝ := volume.restrict (Icc 0 1)

instance unitUniform_probability : IsProbabilityMeasure unitUniform := by
  constructor
  simp [unitUniform]

instance unitUniform_nullSingleton : NullSingletonClass unitUniform := by
  unfold unitUniform
  infer_instance

lemma unitUniform_cdf (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    unitUniform.real (Iic t) = t := by
  have he : Iic t ∩ Icc (0:ℝ) 1 = Icc 0 t := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · intro h; exact ⟨h.2.1, h.1⟩
    · intro h; exact ⟨h.2, h.1, h.2.trans ht1⟩
  simp only [measureReal_def, unitUniform, Measure.restrict_apply measurableSet_Iic, he,
    Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal ht0]

lemma unitUniform_ae : ∀ᵐ x ∂unitUniform, x ∈ Icc (0:ℝ) 1 :=
  ae_restrict_mem measurableSet_Icc

lemma uniform_quantile_ae {n : ℕ} (k : Fin n) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n ↦ unitUniform), sampleQuantile x k ∈ Icc (0:ℝ) 1 := by
  have hall : ∀ᵐ x ∂Measure.pi (fun _ : Fin n ↦ unitUniform), ∀ i, x i ∈ Icc (0:ℝ) 1 := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin n ↦ unitUniform) i).quasiMeasurePreserving.ae unitUniform_ae
  filter_upwards [hall] with x hx
  exact hx (Tuple.sort x k)

/-- The expected rank-r order statistic of n independent uniforms is r/(n+1). -/
theorem uniform_orderStatistic_expectation {n : ℕ} (k : Fin n) :
    (∫ x, sampleQuantile x k ∂Measure.pi (fun _ : Fin n ↦ unitUniform)) =
      (k.val+1 : ℝ)/(n+1) := by
  let P := Measure.pi (fun _ : Fin n ↦ unitUniform)
  let Q := Measure.pi (fun _ : Fin (n+1) ↦ unitUniform)
  let A : Set (ℝ × (Fin n → ℝ)) := {z | z.1 ≤ sampleQuantile z.2 k}
  have hq : Measurable (fun x : Fin n → ℝ ↦ sampleQuantile x k) :=
    measurable_sampleQuantile _ measurable_pi_apply k
  have hA : MeasurableSet A := measurableSet_le measurable_fst (hq.comp measurable_snd)
  have hi : Integrable (indicator A) (unitUniform.prod P) :=
    (indicator_memLp hA).integrable (by norm_num)
  have hmean : (∫ z, indicator A z ∂unitUniform.prod P) =
      ∫ x, sampleQuantile x k ∂P := by
    rw [integral_prod_symm _ hi]
    apply integral_congr_ae
    filter_upwards [uniform_quantile_ae k] with x hx
    have he : (fun u ↦ indicator A (u,x)) = indicator (Iic (sampleQuantile x k)) := rfl
    rw [he, indicator_mean measurableSet_Iic, unitUniform_cdf _ hx.1 hx.2]
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ ℝ) 0
  have hp : MeasurePreserving e Q (unitUniform.prod P) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ unitUniform) 0
  have he : (fun x ↦ indicator A (e x)) =
      indicator {x : Fin (n+1) → ℝ | x 0 ≤ sampleQuantile x k.castSucc} := by
    funext x
    simp only [indicator, Set.indicator, A, Set.mem_setOf_eq]
    congr 1
    exact propext (heldout_rank_identity x k)
  rw [← hmean, ← hp.integral_comp' (indicator A), he,
    indicator_mean (measurableSet_le (measurable_pi_apply 0)
      (measurable_sampleQuantile _ measurable_pi_apply k.castSucc))]
  simpa [Q, Nat.cast_add, Nat.cast_one] using iid_rank_probability unitUniform k.castSucc 0

/-- Transfer the canonical uniform expectation to any independent measurable uniform sample. -/
theorem iid_uniform_orderStatistic_expectation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hi : iIndepFun X μ) (hu : ∀ i, μ.map (X i) = unitUniform) (k : Fin n) :
    (∫ ω, sampleQuantile (fun i ↦ X i ω) k ∂μ) = (k.val+1 : ℝ)/(n+1) := by
  have hmap := hi.map_fun_eq_pi_map (fun i ↦ (hX i).aemeasurable)
  simp_rw [hu] at hmap
  have hq : Measurable (fun x : Fin n → ℝ ↦ sampleQuantile x k) :=
    measurable_sampleQuantile _ measurable_pi_apply k
  rw [← integral_map (measurable_pi_lambda _ hX).aemeasurable hq.aestronglyMeasurable,
    hmap, uniform_orderStatistic_expectation]

end Exceedance
#print axioms Exceedance.uniform_orderStatistic_expectation
#print axioms Exceedance.iid_uniform_orderStatistic_expectation
