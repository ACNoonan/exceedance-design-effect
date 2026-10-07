import PairMixture
import ExactCoverageLaws
import IndicatorVariance
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory ProbabilityTheory Set
namespace Exceedance

noncomputable def reflectionMixture (q : NNReal) : Measure (ℝ × ℝ) :=
  q • unitUniform.map (fun x ↦ (x,x)) + (1-q) • unitUniform.map (fun x ↦ (x,1-x))

lemma reflectionMixture_probability (q : NNReal) (hq : q ≤ 1) :
    IsProbabilityMeasure (reflectionMixture q) := by
  letI : IsProbabilityMeasure (unitUniform.map (fun x : ℝ ↦ (x,x))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (unitUniform.map (fun x : ℝ ↦ (x,1-x))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  constructor
  simp only [reflectionMixture,Measure.add_apply,Measure.smul_apply,measure_univ,
    ENNReal.smul_def,smul_eq_mul,mul_one]
  exact_mod_cast add_tsub_cancel_of_le hq

lemma unitUniform_reflected_cdf (p : ℝ) (hp : p ∈ Icc 0 1) :
    unitUniform.real {x | 1-x ≤ p} = p := by
  have he : {x : ℝ | 1-x ≤ p} ∩ Icc 0 1 = Icc (1-p) 1 := by
    ext x
    simp only [mem_inter_iff,mem_setOf_eq,mem_Icc]
    constructor
    · rintro ⟨h1,h0,h2⟩; exact ⟨by linarith,h2⟩
    · rintro ⟨h1,h2⟩; exact ⟨by linarith,by linarith [hp.2],h2⟩
  rw [measureReal_def,unitUniform,Measure.restrict_apply (by measurability),he,Real.volume_Icc]
  simp only [sub_sub_cancel,ENNReal.toReal_ofReal hp.1]

lemma unitUniform_reflected_diagonal (p : ℝ) (hp : p ∈ Icc (1/2) 1) :
    unitUniform.real {x | x ≤ p ∧ 1-x ≤ p} = 2*p-1 := by
  have he : {x : ℝ | x ≤ p ∧ 1-x ≤ p} ∩ Icc 0 1 = Icc (1-p) p := by
    ext x
    simp only [mem_inter_iff,mem_setOf_eq,mem_Icc]
    constructor
    · rintro ⟨⟨h1,h2⟩,h3⟩; exact ⟨by linarith,h1⟩
    · rintro ⟨h1,h2⟩; exact ⟨⟨h2,by linarith⟩,by linarith [hp.2],by linarith [hp.2]⟩
  rw [measureReal_def,unitUniform,Measure.restrict_apply (by measurability),he,Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (by linarith [hp.1])]
  ring

theorem reflectionMixture_marginals (q : NNReal) (hq : q ≤ 1) (p : ℝ) (hp : p ∈ Icc 0 1) :
    (reflectionMixture q).real {z | z.1 ≤ p} = p ∧
      (reflectionMixture q).real {z | z.2 ≤ p} = p := by
  letI : IsProbabilityMeasure (unitUniform.map (fun x : ℝ ↦ (x,x))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (unitUniform.map (fun x : ℝ ↦ (x,1-x))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  constructor
  all_goals
    rw [reflectionMixture,measureReal_add_apply,measureReal_nnreal_smul_apply,
      measureReal_nnreal_smul_apply,map_measureReal_apply (show Measurable (fun x : ℝ ↦ (x,x)) by fun_prop) (by measurability),
      map_measureReal_apply (show Measurable (fun x : ℝ ↦ (x,1-x)) by fun_prop) (by measurability)]
    simp only [preimage_setOf_eq,NNReal.coe_sub hq,NNReal.coe_one]
  · change (q:ℝ)*unitUniform.real (Iic p)+(1-(q:ℝ))*unitUniform.real (Iic p)=p
    rw [unitUniform_cdf p hp.1 hp.2]; ring
  · change (q:ℝ)*unitUniform.real (Iic p)+(1-(q:ℝ))*unitUniform.real {x | 1-x≤p}=p
    rw [unitUniform_cdf p hp.1 hp.2,unitUniform_reflected_cdf p hp]; ring

theorem reflectionMixture_diagonal (q : NNReal) (hq : q ≤ 1) (p : ℝ) (hp : p ∈ Icc (1/2) 1) :
    (reflectionMixture q).real {z | z.1 ≤ p ∧ z.2 ≤ p} = q*p+(1-(q:ℝ))*(2*p-1) := by
  letI : IsProbabilityMeasure (unitUniform.map (fun x : ℝ ↦ (x,x))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (unitUniform.map (fun x : ℝ ↦ (x,1-x))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [reflectionMixture,measureReal_add_apply,measureReal_nnreal_smul_apply,
    measureReal_nnreal_smul_apply,map_measureReal_apply (show Measurable (fun x : ℝ ↦ (x,x)) by fun_prop) (by measurability),
    map_measureReal_apply (show Measurable (fun x : ℝ ↦ (x,1-x)) by fun_prop) (by measurability)]
  simp only [preimage_setOf_eq,and_self,NNReal.coe_sub hq,NNReal.coe_one]
  change (q:ℝ)*unitUniform.real (Iic p)+(1-(q:ℝ))*unitUniform.real {x | x≤p ∧ 1-x≤p}=_
  rw [unitUniform_cdf p (by linarith [hp.1]) hp.2,unitUniform_reflected_diagonal p hp]

lemma unitUniform_integrable_continuous (g : ℝ → ℝ) (hg : Continuous g) : Integrable g unitUniform :=
  hg.continuousOn.integrableOn_Icc

lemma reflectionMixture_integral (q : NNReal) (g : ℝ × ℝ → ℝ) (hg : Continuous g) :
    (∫ z, g z ∂reflectionMixture q) =
      (q:ℝ)*(∫ x, g (x,x) ∂unitUniform)+((1-q:NNReal):ℝ)*(∫ x, g (x,1-x) ∂unitUniform) := by
  have h1 : Integrable g (unitUniform.map (fun x : ℝ ↦ (x,x))) :=
    (integrable_map_measure hg.aestronglyMeasurable (by fun_prop)).mpr
      (unitUniform_integrable_continuous _ (by fun_prop))
  have h2 : Integrable g (unitUniform.map (fun x : ℝ ↦ (x,1-x))) :=
    (integrable_map_measure hg.aestronglyMeasurable (by fun_prop)).mpr
      (unitUniform_integrable_continuous _ (by fun_prop))
  rw [reflectionMixture,integral_add_measure h1.smul_measure_nnreal h2.smul_measure_nnreal,
    integral_smul_nnreal_measure,integral_smul_nnreal_measure,
    integral_map (show AEMeasurable (fun x : ℝ ↦ (x,x)) unitUniform by fun_prop) hg.aestronglyMeasurable,
    integral_map (show AEMeasurable (fun x : ℝ ↦ (x,1-x)) unitUniform by fun_prop) hg.aestronglyMeasurable]
  rfl

lemma unitUniform_mean : (∫ x, x ∂unitUniform) = (1/2:ℝ) := by
  rw [unitUniform,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_id]
  norm_num

lemma unitUniform_second_moment : (∫ x, x^2 ∂unitUniform) = (1/3:ℝ) := by
  rw [unitUniform,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_pow]
  norm_num


lemma reflectionMixture_integrable (q : NNReal) (g : ℝ × ℝ → ℝ) (hg : Continuous g) :
    Integrable g (reflectionMixture q) := by
  apply Integrable.add_measure
  all_goals
    apply Integrable.smul_measure_nnreal
    apply (integrable_map_measure hg.aestronglyMeasurable (by fun_prop)).mpr
    exact unitUniform_integrable_continuous _ (by fun_prop)

/-- The mixture's raw moments come from its two actual component measures. -/
theorem reflectionMixture_moments (q : NNReal) (hq : q ≤ 1) :
    (∫ z, z.1 ∂reflectionMixture q) = (1/2:ℝ) ∧
    (∫ z, z.2 ∂reflectionMixture q) = (1/2:ℝ) ∧
    (∫ z, z.1^2 ∂reflectionMixture q) = (1/3:ℝ) ∧
    (∫ z, z.2^2 ∂reflectionMixture q) = (1/3:ℝ) ∧
    (∫ z, z.1*z.2 ∂reflectionMixture q) = ((q:ℝ)+1)/6 := by
  have hi := unitUniform_integrable_continuous (fun x : ℝ ↦ x) continuous_id
  have hi2 := unitUniform_integrable_continuous (fun x : ℝ ↦ x^2) (by fun_prop)
  have hneg : (∫ x, 1-x ∂unitUniform) = (1/2:ℝ) := by
    rw [integral_sub (integrable_const _) hi,integral_const,probReal_univ,one_smul,unitUniform_mean]
    norm_num
  have hneg2 : (∫ x, (1-x)^2 ∂unitUniform) = (1/3:ℝ) := by
    have he : (fun x : ℝ ↦ (1-x)^2) = (fun x ↦ 1-2*x+x^2) := by funext x; ring
    have hil : Integrable (fun x : ℝ ↦ 1-2*x) unitUniform := (integrable_const _).sub (hi.const_mul _)
    rw [he,integral_add hil hi2,
      integral_sub (integrable_const _) (hi.const_mul _),integral_const,probReal_univ,one_smul,
      integral_const_mul,unitUniform_mean,unitUniform_second_moment]
    norm_num
  have hcross : (∫ x, x*(1-x) ∂unitUniform) = (1/6:ℝ) := by
    have he : (fun x : ℝ ↦ x*(1-x)) = (fun x ↦ x-x^2) := by funext x; ring
    rw [he,integral_sub hi hi2,unitUniform_mean,unitUniform_second_moment]; norm_num
  have hmul : (∫ x, x*x ∂unitUniform) = (1/3:ℝ) := by simpa only [←sq] using unitUniform_second_moment
  repeat' constructor
  all_goals
    rw [reflectionMixture_integral q _ (by fun_prop),NNReal.coe_sub hq,NNReal.coe_one]
    simp only [unitUniform_mean,unitUniform_second_moment,hneg,hneg2,hcross,hmul]
    <;> ring

/-- Score correlation and indicator correlation disagree in the explicit reflection mixture. -/
theorem reflectionMixture_correlations (q : NNReal) (hq : q ≤ 1)
    (p : ℝ) (hp : p ∈ Ico (1/2) 1) :
    cov[Prod.fst,Prod.snd;reflectionMixture q]/
        Real.sqrt (Var[Prod.fst;reflectionMixture q]*Var[Prod.snd;reflectionMixture q]) = 2*(q:ℝ)-1 ∧
    ((reflectionMixture q).real {z | z.1 ≤ p ∧ z.2 ≤ p}-p^2)/(p*(1-p)) = ((q:ℝ)-(1-p))/p := by
  letI := reflectionMixture_probability q hq
  have h1 : MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 (reflectionMixture q) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (reflectionMixture_integrable q _ (by fun_prop))
  have h2 : MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 (reflectionMixture q) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (reflectionMixture_integrable q _ (by fun_prop))
  obtain ⟨hm1,hm2,hs1,hs2,hc⟩ := reflectionMixture_moments q hq
  constructor
  · rw [covariance_eq_sub h1 h2,variance_eq_sub h1,variance_eq_sub h2]
    change ((∫ z, z.1*z.2 ∂reflectionMixture q)-(∫ z, z.1 ∂reflectionMixture q)*(∫ z, z.2 ∂reflectionMixture q)) /
      Real.sqrt (((∫ z, z.1^2 ∂reflectionMixture q)-(∫ z, z.1 ∂reflectionMixture q)^2)*
        ((∫ z, z.2^2 ∂reflectionMixture q)-(∫ z, z.2 ∂reflectionMixture q)^2)) = _
    rw [hm1,hm2,hs1,hs2,hc]
    norm_num
    ring
  · rw [reflectionMixture_diagonal q hq p ⟨hp.1,hp.2.le⟩]
    have hp0 : p≠0 := by linarith [hp.1]
    have hp1 : 1-p≠0 := by linarith [hp.2]
    field_simp
    <;> ring

/-- The paper's zero-score-correlation example has indicator design effect 13/9. -/
theorem zero_score_correlation_counterexample :
    cov[Prod.fst,Prod.snd;reflectionMixture (1/2)]/
      Real.sqrt (Var[Prod.fst;reflectionMixture (1/2)]*Var[Prod.snd;reflectionMixture (1/2)]) = 0 ∧
    ((reflectionMixture (1/2)).real {z | z.1 ≤ 9/10 ∧ z.2 ≤ 9/10}-(9/10)^2)/((9/10)*(1-9/10)) = 4/9 ∧
    1+((reflectionMixture (1/2)).real {z | z.1 ≤ 9/10 ∧ z.2 ≤ 9/10}-(9/10)^2)/((9/10)*(1-9/10)) = 13/9 := by
  have hh := reflectionMixture_correlations (1/2) (by norm_num) (9/10) (by constructor <;> norm_num)
  norm_num at hh ⊢
  exact ⟨hh.1,hh.2,by linarith [hh.2]⟩


/-- Swapping the coordinates preserves the constructed pair law. -/
theorem reflectionMixture_exchangeable (q : NNReal) :
    (reflectionMixture q).map Prod.swap = reflectionMixture q := by
  have hu : unitUniform.map (fun x : ℝ ↦ 1-x) = unitUniform :=
    uniform_marginal_law _ (by fun_prop) (fun t ht0 ht1 ↦ unitUniform_reflected_cdf t ⟨ht0,ht1⟩)
  have he : (unitUniform.map (fun x : ℝ ↦ (x,1-x))).map Prod.swap =
      unitUniform.map (fun x : ℝ ↦ (x,1-x)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have hh : (fun x : ℝ ↦ (1-x,x)) = (fun x ↦ (x,1-x)) ∘ (fun x ↦ 1-x) := by
      funext x; simp only [Function.comp_apply]; congr 1; ring
    change unitUniform.map (fun x : ℝ ↦ (1-x,x))=_
    rw [hh,← Measure.map_map (by fun_prop) (by fun_prop),hu]
  rw [reflectionMixture,Measure.map_add _ _ (by fun_prop),Measure.map_smul,Measure.map_smul,he,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end Exceedance
#print axioms Exceedance.reflectionMixture_diagonal

#print axioms Exceedance.zero_score_correlation_counterexample

#print axioms Exceedance.reflectionMixture_exchangeable
