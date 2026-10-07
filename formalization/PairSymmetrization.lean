import DuplicatedPairs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory ProbabilityTheory
namespace Exceedance

/-- A bijection preserves the uniform distribution on a finite type. -/
theorem uniform_pmf_equiv {α : Type*} [Fintype α] [Nonempty α] (e : Equiv.Perm α) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype α := by
  classical
  ext a
  rw [PMF.map_apply]
  have he (b : α) : a = e b ↔ b = e.symm a := by
    constructor
    · intro h; exact (e.symm_apply_eq.mpr h).symm
    · intro h; rw [h, e.apply_symm_apply]
  simp_rw [he]
  simp [PMF.uniformOfFintype_apply]

/-- Draw one of the 24 coordinate permutations uniformly and apply it to a fixed four-vector. -/
noncomputable def symmetrizedFour (x : Fin 4 → ℝ) : PMF (Fin 4 → ℝ) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin 4))).map (fun σ i ↦ x (σ i))

/-- The actual finite probability law is invariant under every coordinate permutation. -/
theorem symmetrizedFour_exchangeable (x : Fin 4 → ℝ) (τ : Equiv.Perm (Fin 4)) :
    (symmetrizedFour x).map (fun v i ↦ v (τ i)) = symmetrizedFour x := by
  let e : Equiv.Perm (Equiv.Perm (Fin 4)) := Equiv.mulRight τ
  have hu := uniform_pmf_equiv e
  unfold symmetrizedFour
  rw [PMF.map_comp]
  calc
    _ = ((PMF.uniformOfFintype (Equiv.Perm (Fin 4))).map e).map (fun σ i ↦ x (σ i)) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by rw [hu]

/-- Uniform coordinate symmetrization preserves the duplicated-pair count exactly. -/
theorem symmetrized_pair_count_law (u v t : ℝ) :
    (symmetrizedFour ![u,u,v,v]).map (thresholdCount t) =
      PMF.pure (2*((if u ≤ t then 1 else 0)+(if v ≤ t then 1 else 0))) := by
  unfold symmetrizedFour
  rw [PMF.map_comp]
  have he : (thresholdCount t) ∘ (fun σ : Equiv.Perm (Fin 4) ↦ fun i ↦ ![u,u,v,v] (σ i)) =
      Function.const (Equiv.Perm (Fin 4)) (2*((if u ≤ t then 1 else 0)+(if v ≤ t then 1 else 0))) := by
    funext σ
    exact duplicated_pair_count u v t σ
  rw [he, PMF.map_const]


section ProductModel
local instance : MeasurableSpace (Equiv.Perm (Fin 4)) := ⊤

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Draw a coordinate permutation independently of the underlying random vector. -/
noncomputable def symmetrizedFourLaw (X : Ω → Fin 4 → ℝ) (μ : Measure Ω) : Measure (Fin 4 → ℝ) :=
  ((PMF.uniformOfFintype (Equiv.Perm (Fin 4))).toMeasure.prod μ).map
    (fun z : Equiv.Perm (Fin 4) × Ω ↦ fun i ↦ X z.2 (z.1 i))

lemma measurable_random_permutation (X : Ω → Fin 4 → ℝ) (hX : Measurable X) :
    Measurable (fun z : Equiv.Perm (Fin 4) × Ω ↦ fun i ↦ X z.2 (z.1 i)) := by
  apply measurable_from_prod_countable_right
  intro σ
  exact measurable_pi_lambda _ (fun i ↦ (measurable_pi_apply (σ i)).comp hX)

theorem symmetrizedFourLaw_probability (X : Ω → Fin 4 → ℝ) (hX : Measurable X) :
    IsProbabilityMeasure (symmetrizedFourLaw X μ) :=
  Measure.isProbabilityMeasure_map (measurable_random_permutation X hX).aemeasurable

/-- The symmetrized probability measure is exchangeable for every underlying vector law. -/
theorem symmetrizedFourLaw_exchangeable (X : Ω → Fin 4 → ℝ) (hX : Measurable X)
    (τ : Equiv.Perm (Fin 4)) :
    (symmetrizedFourLaw X μ).map (fun x i ↦ x (τ i)) = symmetrizedFourLaw X μ := by
  let P := (PMF.uniformOfFintype (Equiv.Perm (Fin 4))).toMeasure
  let e : Equiv.Perm (Equiv.Perm (Fin 4)) := Equiv.mulRight τ
  have he : Measurable e := measurable_of_finite e
  have hP : P.map e = P := by
    rw [PMF.toMeasure_map e _ he, uniform_pmf_equiv]
  have hp : (P.prod μ).map (Prod.map e id) = P.prod μ := by
    rw [← Measure.map_prod_map P μ he measurable_id, hP, Measure.map_id]
  have hR : Measurable (fun x : Fin 4 → ℝ ↦ fun i ↦ x (τ i)) :=
    measurable_pi_lambda _ (fun i ↦ measurable_pi_apply (τ i))
  let Y := fun z : Equiv.Perm (Fin 4) × Ω ↦ fun i ↦ X z.2 (z.1 i)
  have hY : Measurable Y := measurable_random_permutation X hX
  unfold symmetrizedFourLaw
  rw [Measure.map_map hR hY]
  change (P.prod μ).map ((fun x : Fin 4 → ℝ ↦ fun i ↦ x (τ i)) ∘ Y) = (P.prod μ).map Y
  calc
    _ = (P.prod μ).map (Y ∘ Prod.map e id) := rfl
    _ = ((P.prod μ).map (Prod.map e id)).map Y := by
      rw [Measure.map_map hY (he.prodMap measurable_id)]
    _ = _ := by rw [hp]

/-- Independent symmetrization preserves the full duplicated-pair threshold-count law. -/
theorem symmetrized_pair_measure_count_law (U V : Ω → ℝ)
    (hU : Measurable U) (hV : Measurable V) (t : ℝ) :
    (symmetrizedFourLaw (fun ω ↦ ![U ω,U ω,V ω,V ω]) μ).map (thresholdCount t) =
      μ.map (fun ω ↦ 2*((if U ω ≤ t then 1 else 0)+(if V ω ≤ t then 1 else 0))) := by
  let X : Ω → Fin 4 → ℝ := fun ω ↦ ![U ω,U ω,V ω,V ω]
  have hX : Measurable X := by
    apply measurable_pi_lambda
    intro i
    fin_cases i <;> first | simpa [X] using hU | simpa [X] using hV
  let g := fun ω ↦ 2*((if U ω ≤ t then (1:ℝ) else 0)+(if V ω ≤ t then 1 else 0))
  have hg : Measurable g := by
    exact ((measurable_const.ite (measurableSet_le hU measurable_const) measurable_const).add
      (measurable_const.ite (measurableSet_le hV measurable_const) measurable_const)).const_mul 2
  unfold symmetrizedFourLaw
  rw [Measure.map_map (measurable_thresholdCount t) (measurable_random_permutation X hX)]
  have he : (thresholdCount t) ∘ (fun z : Equiv.Perm (Fin 4) × Ω ↦ fun i ↦ X z.2 (z.1 i)) =
      g ∘ Prod.snd := by
    funext z
    exact duplicated_pair_count (U z.2) (V z.2) t z.1
  rw [he, ← Measure.map_map hg measurable_snd, Measure.map_snd_prod]
  simp [g]

/-- Independent symmetrization preserves a common coordinate distribution. -/
theorem symmetrizedFourLaw_marginal (X : Ω → Fin 4 → ℝ) (hX : Measurable X)
    (ν : Measure ℝ) (hν : ∀ i, μ.map (fun ω ↦ X ω i) = ν) (i : Fin 4) :
    (symmetrizedFourLaw X μ).map (fun x ↦ x i) = ν := by
  let Y := fun z : Equiv.Perm (Fin 4) × Ω ↦ fun j ↦ X z.2 (z.1 j)
  have hY : Measurable Y := measurable_random_permutation X hX
  unfold symmetrizedFourLaw
  rw [Measure.map_map (measurable_pi_apply i) hY]
  ext s hs
  rw [Measure.map_apply ((measurable_pi_apply i).comp hY) hs,
    Measure.prod_apply (((measurable_pi_apply i).comp hY) hs)]
  have he (σ : Equiv.Perm (Fin 4)) :
      μ {ω | X ω (σ i) ∈ s} = ν s := by
    rw [← hν (σ i)]
    exact (Measure.map_apply
      (show Measurable (fun ω ↦ X ω (σ i)) from (measurable_pi_apply (σ i)).comp hX) hs).symm
  change (∫⁻ σ : Equiv.Perm (Fin 4), μ {ω | X ω (σ i) ∈ s}
    ∂(PMF.uniformOfFintype (Equiv.Perm (Fin 4))).toMeasure) = ν s
  simp_rw [he]
  simp

end ProductModel

end Exceedance
#print axioms Exceedance.uniform_pmf_equiv
#print axioms Exceedance.symmetrizedFour_exchangeable
#print axioms Exceedance.symmetrized_pair_count_law

#print axioms Exceedance.symmetrizedFourLaw_probability
#print axioms Exceedance.symmetrizedFourLaw_exchangeable
#print axioms Exceedance.symmetrized_pair_measure_count_law
#print axioms Exceedance.symmetrizedFourLaw_marginal
