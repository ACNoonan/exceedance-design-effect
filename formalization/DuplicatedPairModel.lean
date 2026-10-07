import UniformOrderStatistic
import PairSymmetrization
import ClusterSample
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

local instance : MeasurableSpace (Equiv.Perm (Fin 4)) := ⊤

abbrev PairSource := Equiv.Perm (Fin 4) × (Fin 2 → ℝ)
abbrev PairSequence := ℕ → PairSource

noncomputable def pairUniform : Measure (Fin 2 → ℝ) := Measure.pi (fun _ ↦ unitUniform)
noncomputable def pairSourceLaw : Measure PairSource :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin 4))).toMeasure.prod pairUniform
noncomputable def pairSequenceLaw : Measure PairSequence :=
  Measure.infinitePi (fun _ : ℕ ↦ pairSourceLaw)

instance : IsProbabilityMeasure pairUniform := by unfold pairUniform; infer_instance
instance : IsProbabilityMeasure pairSourceLaw := by unfold pairSourceLaw; infer_instance
instance : IsProbabilityMeasure pairSequenceLaw := by unfold pairSequenceLaw; infer_instance

def pairVector (x : Fin 2 → ℝ) : Fin 4 → ℝ := ![x 0,x 0,x 1,x 1]
def randomPairVector (z : PairSource) (i : Fin 4) : ℝ := pairVector z.2 (z.1 i)
def pairCluster (j : ℕ) (ω : PairSequence) : Fin 4 → ℝ := randomPairVector (ω j)
def pairLatent (a : ℕ × Fin 2) (ω : PairSequence) : ℝ := (ω a.1).2 a.2

def pairBaseSample (b : ℕ) (ω : PairSequence) (i : Fin (b*2)) : ℝ :=
  pairLatent ((finProdFinEquiv.symm i).1.val, (finProdFinEquiv.symm i).2) ω

lemma measurable_pairVector : Measurable pairVector := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> first | simpa [pairVector] using (show Measurable (fun x : Fin 2 → ℝ ↦ x 0) from measurable_pi_apply 0) | simpa [pairVector] using (show Measurable (fun x : Fin 2 → ℝ ↦ x 1) from measurable_pi_apply 1)

lemma measurable_randomPairVector : Measurable randomPairVector :=
  measurable_random_permutation pairVector measurable_pairVector

lemma measurable_pairCluster (j : ℕ) : Measurable (pairCluster j) :=
  measurable_randomPairVector.comp (measurable_pi_apply j)

lemma measurable_pairLatent (a : ℕ × Fin 2) : Measurable (pairLatent a) :=
  (measurable_pi_apply a.2).comp (measurable_snd.comp (measurable_pi_apply a.1))

lemma pairSource_snd_law : pairSourceLaw.map Prod.snd = pairUniform := by
  unfold pairSourceLaw
  rw [Measure.map_snd_prod]
  simp

lemma pairLatent_law (a : ℕ × Fin 2) : pairSequenceLaw.map (pairLatent a) = unitUniform := by
  change pairSequenceLaw.map ((fun z : PairSource ↦ z.2 a.2) ∘ (fun ω ↦ ω a.1)) = _
  rw [← Measure.map_map (show Measurable (fun z : PairSource ↦ z.2 a.2) from (measurable_pi_apply a.2).comp measurable_snd) (measurable_pi_apply a.1)]
  unfold pairSequenceLaw
  rw [Measure.infinitePi_map_eval]
  change pairSourceLaw.map ((fun x : Fin 2 → ℝ ↦ x a.2) ∘ Prod.snd) = _
  rw [← Measure.map_map (measurable_pi_apply a.2) measurable_snd, pairSource_snd_law]
  exact (measurePreserving_eval (fun _ : Fin 2 ↦ unitUniform) a.2).map_eq

lemma pairLatent_joint_law :
    pairSequenceLaw.map (fun ω a ↦ pairLatent a ω) =
      Measure.infinitePi (fun _ : ℕ × Fin 2 ↦ unitUniform) := by
  let Y := fun ω : PairSequence ↦ fun j : ℕ ↦ (ω j).2
  have hY : Measurable Y := measurable_pi_lambda _ (fun j ↦ measurable_snd.comp (measurable_pi_apply j))
  have hm : pairSequenceLaw.map Y = Measure.infinitePi (fun _ : ℕ ↦ pairUniform) := by
    change (Measure.infinitePi (fun _ : ℕ ↦ pairSourceLaw)).map (fun ω j ↦ Prod.snd (ω j)) = _
    rw [Measure.infinitePi_map_pi _ (fun _ ↦ measurable_snd)]
    simp_rw [pairSource_snd_law]
  have hc := Measure.infinitePi_map_curry_symm (fun (_ : ℕ) (_ : Fin 2) ↦ unitUniform)
  simp only [Measure.infinitePi_eq_pi] at hc
  change (Measure.infinitePi (fun _ : ℕ ↦ pairUniform)).map
    (MeasurableEquiv.curry ℕ (Fin 2) ℝ).symm = _ at hc
  change pairSequenceLaw.map ((MeasurableEquiv.curry ℕ (Fin 2) ℝ).symm ∘ Y) = _
  rw [← Measure.map_map (MeasurableEquiv.curry ℕ (Fin 2) ℝ).symm.measurable hY, hm, hc]

theorem pairLatent_independent : iIndepFun pairLatent pairSequenceLaw := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map measurable_pairLatent).mpr
  simp_rw [pairLatent_joint_law, pairLatent_law]

theorem pairCluster_independent : iIndepFun pairCluster pairSequenceLaw :=
  iIndepFun_infinitePi (fun _ ↦ measurable_randomPairVector)

lemma pairCluster_law (j : ℕ) : pairSequenceLaw.map (pairCluster j) =
    symmetrizedFourLaw pairVector pairUniform := by
  change pairSequenceLaw.map (randomPairVector ∘ (fun ω ↦ ω j)) = _
  unfold pairSequenceLaw
  rw [← Measure.map_map measurable_randomPairVector (measurable_pi_apply j), Measure.infinitePi_map_eval]
  rfl

theorem pairCluster_identDistrib (j : ℕ) : IdentDistrib (pairCluster j) (pairCluster 0)
    pairSequenceLaw pairSequenceLaw :=
  ⟨(measurable_pairCluster j).aemeasurable, (measurable_pairCluster 0).aemeasurable,
    (pairCluster_law j).trans (pairCluster_law 0).symm⟩

theorem pairCluster_exchangeable (j : ℕ) (σ : Equiv.Perm (Fin 4)) :
    (pairSequenceLaw.map (pairCluster j)).map (fun x i ↦ x (σ i)) =
      pairSequenceLaw.map (pairCluster j) := by
  rw [pairCluster_law]
  exact symmetrizedFourLaw_exchangeable pairVector measurable_pairVector σ

theorem pairCluster_marginal (j : ℕ) (i : Fin 4) :
    pairSequenceLaw.map (fun ω ↦ pairCluster j ω i) = unitUniform := by
  change pairSequenceLaw.map ((fun x : Fin 4 → ℝ ↦ x i) ∘ pairCluster j) = _
  rw [← Measure.map_map (measurable_pi_apply i) (measurable_pairCluster j), pairCluster_law]
  apply symmetrizedFourLaw_marginal pairVector measurable_pairVector unitUniform
  intro l
  have h0 := (measurePreserving_eval (fun _ : Fin 2 ↦ unitUniform) (0 : Fin 2)).map_eq
  have h1 := (measurePreserving_eval (fun _ : Fin 2 ↦ unitUniform) (1 : Fin 2)).map_eq
  fin_cases l <;> first | simpa [pairVector, pairUniform, Function.eval] using h0 | simpa [pairVector, pairUniform, Function.eval] using h1

lemma pairBaseSample_independent (b : ℕ) :
    iIndepFun (fun i ω ↦ pairBaseSample b ω i) pairSequenceLaw := by
  apply pairLatent_independent.precomp
  intro i j hij
  apply finProdFinEquiv.symm.injective
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst hij)
  · exact congrArg (fun a : ℕ × Fin 2 ↦ a.2) hij

lemma pairBaseSample_expectation (b : ℕ) (k : Fin (b*2)) :
    (∫ ω, sampleQuantile (pairBaseSample b ω) k ∂pairSequenceLaw) =
      (k.val+1 : ℝ)/(b*2+1) := by
  have h := iid_uniform_orderStatistic_expectation
    (fun i ω ↦ pairBaseSample b ω i)
    (fun i ↦ measurable_pairLatent _) (pairBaseSample_independent b)
    (fun i ↦ pairLatent_law _) k
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

end Exceedance
#print axioms Exceedance.pairLatent_independent
#print axioms Exceedance.pairCluster_independent
#print axioms Exceedance.pairCluster_identDistrib
#print axioms Exceedance.pairCluster_exchangeable
#print axioms Exceedance.pairCluster_marginal
#print axioms Exceedance.pairBaseSample_expectation
