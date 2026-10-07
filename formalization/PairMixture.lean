import UniformOrderStatistic

open MeasureTheory ProbabilityTheory Set
namespace Exceedance

/-- A pair is identical with weight q, and independently uniform with weight 1-q. -/
noncomputable def uniformPairMixture (q : NNReal) : Measure (ℝ × ℝ) :=
  q • unitUniform.map (fun x ↦ (x,x)) + (1-q) • unitUniform.prod unitUniform

lemma uniformPairMixture_probability (q : NNReal) (hq : q ≤ 1) :
    IsProbabilityMeasure (uniformPairMixture q) := by
  letI : IsProbabilityMeasure (unitUniform.map (fun x : ℝ ↦ (x,x))) :=
    Measure.isProbabilityMeasure_map (measurable_id.prodMk measurable_id).aemeasurable
  constructor
  simp only [uniformPairMixture, Measure.add_apply, Measure.smul_apply,
    measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one]
  exact_mod_cast add_tsub_cancel_of_le hq

/-- The diagonal probability is proved from the mixture measure. -/
theorem uniformPairMixture_diagonal (q : NNReal) (hq : q ≤ 1)
    (p : ℝ) (hp : p ∈ Icc 0 1) :
    (uniformPairMixture q).real {z | z.1 ≤ p ∧ z.2 ≤ p} = q*p+(1-(q:ℝ))*p^2 := by
  have hm : MeasurableSet {z : ℝ × ℝ | z.1 ≤ p ∧ z.2 ≤ p} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_snd measurable_const)
  letI : IsProbabilityMeasure (unitUniform.map (fun x : ℝ ↦ (x,x))) :=
    Measure.isProbabilityMeasure_map (measurable_id.prodMk measurable_id).aemeasurable
  rw [uniformPairMixture, measureReal_add_apply, measureReal_nnreal_smul_apply,
    measureReal_nnreal_smul_apply, map_measureReal_apply (show Measurable (fun x : ℝ ↦ (x,x)) from measurable_id.prodMk measurable_id) hm]
  have he : (fun x : ℝ ↦ (x,x)) ⁻¹' {z | z.1 ≤ p ∧ z.2 ≤ p} = Iic p := by ext x; simp
  have hpSet : {z : ℝ × ℝ | z.1 ≤ p ∧ z.2 ≤ p} = Iic p ×ˢ Iic p := rfl
  rw [he, hpSet, measureReal_def, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul,
    ← measureReal_def, unitUniform_cdf p hp.1 hp.2, NNReal.coe_sub hq, NNReal.coe_one]
  ring

/-- Both marginals of the mixture remain uniform. -/
theorem uniformPairMixture_marginals (q : NNReal) (hq : q ≤ 1)
    (p : ℝ) (hp : p ∈ Icc 0 1) :
    (uniformPairMixture q).real {z | z.1 ≤ p} = p ∧
    (uniformPairMixture q).real {z | z.2 ≤ p} = p := by
  letI : IsProbabilityMeasure (unitUniform.map (fun x : ℝ ↦ (x,x))) :=
    Measure.isProbabilityMeasure_map (measurable_id.prodMk measurable_id).aemeasurable
  have hf : {z : ℝ × ℝ | z.1 ≤ p} = Iic p ×ˢ univ := by ext z; simp
  have hs : {z : ℝ × ℝ | z.2 ≤ p} = univ ×ˢ Iic p := by ext z; simp
  constructor
  all_goals
    rw [uniformPairMixture, measureReal_add_apply, measureReal_nnreal_smul_apply,
      measureReal_nnreal_smul_apply, map_measureReal_apply (show Measurable (fun x : ℝ ↦ (x,x)) from measurable_id.prodMk measurable_id) (by measurability)]
    change (q : ℝ)*unitUniform.real (Iic p) + _ = p
  · rw [hf, measureReal_def, measureReal_def, Measure.prod_prod, measure_univ, mul_one, ← measureReal_def,
      unitUniform_cdf p hp.1 hp.2, NNReal.coe_sub hq, NNReal.coe_one]
    ring
  · rw [hs, measureReal_def, measureReal_def, Measure.prod_prod, measure_univ, one_mul, ← measureReal_def,
      unitUniform_cdf p hp.1 hp.2, NNReal.coe_sub hq, NNReal.coe_one]
    ring

/-- Indicator correlation is the mixing weight at every interior level. -/
theorem uniformPairMixture_indicator_correlation (q : NNReal) (hq : q ≤ 1)
    (p : ℝ) (hp : p ∈ Ioo 0 1) :
    ((uniformPairMixture q).real {z | z.1 ≤ p ∧ z.2 ≤ p}-p^2)/(p*(1-p)) = q := by
  rw [uniformPairMixture_diagonal q hq p ⟨hp.1.le,hp.2.le⟩]
  have h0 : p ≠ 0 := hp.1.ne'
  have h1 : 1-p ≠ 0 := (sub_pos.mpr hp.2).ne'
  field_simp
  <;> ring

end Exceedance
#print axioms Exceedance.uniformPairMixture_probability
#print axioms Exceedance.uniformPairMixture_marginals
#print axioms Exceedance.uniformPairMixture_indicator_correlation
