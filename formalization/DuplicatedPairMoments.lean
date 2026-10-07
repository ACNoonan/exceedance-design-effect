import DuplicatedPairModel

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

local instance : MeasurableSpace (Equiv.Perm (Fin 4)) := ⊤

lemma uniform_map_cdf {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Ω → ℝ) (hX : Measurable X) (hu : μ.map X = unitUniform)
    (p : ℝ) (hp : p ∈ Icc 0 1) : μ.real {ω | X ω ≤ p} = p := by
  have hh := map_measureReal_apply (μ := μ) hX (measurableSet_Iic (a := p))
  rw [hu, unitUniform_cdf p hp.1 hp.2] at hh
  exact hh.symm

theorem pairCluster_cdf (j : ℕ) (i : Fin 4) (p : ℝ) (hp : p ∈ Icc 0 1) :
    pairSequenceLaw.real {ω | pairCluster j ω i ≤ p} = p :=
  uniform_map_cdf _ ((measurable_pi_apply i).comp (measurable_pairCluster j))
    (pairCluster_marginal j i) p hp

theorem pairCluster_count_variance (j : ℕ) (p : ℝ) (hp : p ∈ Icc 0 1) :
    Var[fun ω ↦ thresholdCount p (pairCluster j ω); pairSequenceLaw] = 8*p*(1-p) := by
  exact duplicated_pair_count_variance (pairLatent (j,0)) (pairLatent (j,1))
    (measurable_pairLatent _) (measurable_pairLatent _)
    (pairLatent_independent.indepFun (by simp)) p p
    (uniform_map_cdf _ (measurable_pairLatent _) (pairLatent_law _) p hp)
    (uniform_map_cdf _ (measurable_pairLatent _) (pairLatent_law _) p hp)
    (fun ω ↦ (ω j).1)

lemma pair_position_permutation (i j : Fin 4) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by
  have h0 : Function.Injective (![0,1] : Fin 2 → Fin 4) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have h1 : Function.Injective (![i,j] : Fin 2 → Fin 4) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [Ne.symm hij]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair ![0,1] ![i,j] h0 h1
  exact ⟨σ, hσ 0, hσ 1⟩

lemma pairCluster_common_pair_probability (j : ℕ) (p : ℝ) (i l : Fin 4) (hil : i ≠ l) :
    pairSequenceLaw.real {ω | pairCluster j ω i ≤ p ∧ pairCluster j ω l ≤ p} =
      pairSequenceLaw.real {ω | pairCluster j ω 0 ≤ p ∧ pairCluster j ω 1 ≤ p} := by
  obtain ⟨σ, hσ0, hσ1⟩ := pair_position_permutation i l hil
  let L := pairSequenceLaw.map (pairCluster j)
  let A : Set (Fin 4 → ℝ) := {x | x 0 ≤ p ∧ x 1 ≤ p}
  have hA : MeasurableSet A :=
    (measurableSet_le (measurable_pi_apply 0) measurable_const).inter
      (measurableSet_le (measurable_pi_apply 1) measurable_const)
  have hR : Measurable (fun x : Fin 4 → ℝ ↦ fun a ↦ x (σ a)) :=
    measurable_pi_lambda _ (fun a ↦ measurable_pi_apply (σ a))
  have hh := congrArg (fun M : Measure (Fin 4 → ℝ) ↦ M.real A)
    (pairCluster_exchangeable j σ)
  rw [map_measureReal_apply hR hA] at hh
  rw [map_measureReal_apply (measurable_pairCluster j) (hR hA),
    map_measureReal_apply (measurable_pairCluster j) hA] at hh
  simpa only [Set.preimage_setOf_eq, hσ0, hσ1, A] using hh

/-- Actual joint threshold probabilities under the constructed iid cluster model. -/
theorem pairCluster_pair_probability (j : ℕ) (p : ℝ) (hp : p ∈ Icc 0 1)
    (i l : Fin 4) (hil : i ≠ l) :
    pairSequenceLaw.real {ω | pairCluster j ω i ≤ p ∧ pairCluster j ω l ≤ p} =
      p/3 + 2*p^2/3 := by
  let A := fun i : Fin 4 ↦ {ω | pairCluster j ω i ≤ p}
  let δ := pairSequenceLaw.real (A 0 ∩ A 1)
  have hA (i : Fin 4) : MeasurableSet (A i) :=
    measurableSet_le ((measurable_pi_apply i).comp (measurable_pairCluster j)) measurable_const
  have hm (i : Fin 4) : pairSequenceLaw.real (A i) = p := pairCluster_cdf j i p hp
  have hd (i l : Fin 4) (hil : i ≠ l) : pairSequenceLaw.real (A i ∩ A l) = δ :=
    pairCluster_common_pair_probability j p i l hil
  have hv := cluster_indicator_variance A hA p δ hm hd
  have hv' := pairCluster_count_variance j p hp
  rw [thresholdCount_comp] at hv'
  change Var[fun ω ↦ ∑ i, indicator (A i) ω; pairSequenceLaw] = _ at hv'
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hv
  rw [pairCluster_common_pair_probability j p i l hil]
  change δ = _
  nlinarith

/-- The indicator correlation is exactly 1/3 at every interior target. -/
theorem pairCluster_indicator_correlation (j : ℕ) (p : ℝ) (hp : p ∈ Ioo 0 1)
    (i l : Fin 4) (hil : i ≠ l) :
    (pairSequenceLaw.real {ω | pairCluster j ω i ≤ p ∧ pairCluster j ω l ≤ p} - p^2) /
      (p*(1-p)) = 1/3 := by
  rw [pairCluster_pair_probability j p ⟨hp.1.le,hp.2.le⟩ i l hil]
  have hpos : 0 < p*(1-p) := mul_pos hp.1 (by linarith [hp.2])
  apply (div_eq_iff hpos.ne').mpr
  ring

end Exceedance
#print axioms Exceedance.pairCluster_count_variance
#print axioms Exceedance.pairCluster_pair_probability
#print axioms Exceedance.pairCluster_indicator_correlation
