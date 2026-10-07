import RaggedLimit

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Proposition 2 for continuous original scores. R3 is expressed through the equivalent uniform-scale indicators. -/
theorem ragged_continuous_score_ceil_coverage_certificate
    (b : ℕ → ℕ) (m : (n : ℕ) → Fin (b n) → ℕ)
    (S : (n : ℕ) → (j : Fin (b n)) → Ω → Fin (m n j) → ℝ)
    (hS : ∀ n j, Measurable (S n j)) (hindep : ∀ n, iIndepFun (S n) μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ n j i t, μ.real {ω | S n j ω i ≤ t} = F t)
    (hb : ∀ n, 0 < b n) (hm : ∀ n j, 0 < m n j)
    (M : ℝ) (hM : 0 < M) (hsize : ∀ n j, (m n j : ℝ) ≤ M)
    (hbt : Tendsto b atTop atTop) (rho : ℝ → ℝ)
    (hpairs : ∀ n j t, t ∈ Icc 0 1 →
      (∑ i : Fin (m n j), ∑ l ∈ Finset.univ.erase i,
        cov[indicator {ω | F (S n j ω i) ≤ t}, indicator {ω | F (S n j ω l) ≤ t}; μ]) =
        (m n j : ℝ)*((m n j : ℝ)-1)*(t*(1-t)*rho t))
    (sizeLimit : ℝ)
    (hsizeLimit : Tendsto (fun n ↦ (∑ j, (m n j : ℝ)^2)/(raggedSize (m n) : ℝ)) atTop (nhds sizeLimit))
    (p : ℝ) (hp : p ∈ Ioo 0 1) (k : ∀ n, Fin (raggedSize (m n)))
    (hceil : ∀ᶠ n in atTop, (k n).val+1 = Nat.ceil (((raggedSize (m n) : ℝ)+1)*p)) :
    let v := p*(1-p)*(1+(sizeLimit-1)*rho p)
    0 ≤ v ∧
    (∀ x : ℝ, v.toNNReal ≠ 0 ∨ x ≠ 0 →
      Tendsto (fun n ↦ μ.real {ω | Real.sqrt (raggedSize (m n)) *
        (F (sampleQuantile (raggedSample (m n) (S n) ω) (k n))-
          ((k n).val+1 : ℝ)/((raggedSize (m n) : ℝ)+1)) ≤ x})
        atTop (nhds (cdf (gaussianReal 0 v.toNNReal) x))) ∧
    Tendsto (fun n ↦ (raggedSize (m n) : ℝ)*
      Var[fun ω ↦ F (sampleQuantile (raggedSample (m n) (S n) ω) (k n)); μ]) atTop (nhds v) := by
  let T := fun n j (u : Fin (m n j) → ℝ) i ↦ F (u i)
  have hT (n : ℕ) (j : Fin (b n)) : Measurable (T n j) :=
    measurable_pi_lambda _ (fun i ↦ hF.measurable.comp (measurable_pi_apply i))
  let U := fun n j ω i ↦ F (S n j ω i)
  have hU (n : ℕ) (j : Fin (b n)) : Measurable (U n j) := (hT n j).comp (hS n j)
  have hu : ∀ n j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U n j ω i ≤ t} = t := by
    intro n j i t ht0 ht1
    exact continuous_cdf_transform (fun ω ↦ S n j ω i) F hF hmono h0 h1 (hCDF n j i) t ht0 ht1
  let G : RaggedUniformModel Ω μ := {
    b := b, m := m, U := U, measurable := hU
    independent := fun n ↦ (hindep n).comp (T n) (hT n)
    uniform := hu, nonempty := hb, positive_size := hm, M := M, M_pos := hM,
    size_le := hsize, grows := hbt, rho := rho, mean_pair := hpairs,
    sizeLimit := sizeLimit, sizeLimit_tendsto := hsizeLimit }
  have he (n : ℕ) (ω : Ω) : sampleQuantile (raggedSample (m n) (U n) ω) (k n) =
      F (sampleQuantile (raggedSample (m n) (S n) ω) (k n)) :=
    sampleQuantile_monotone_map (raggedSample (m n) (S n) ω) (k n) F hmono
  have hh := G.ceil_coverage_certificate p hp k hceil
  refine ⟨G.varianceLimit_nonneg p hp, ?_⟩
  simpa only [RaggedUniformModel.varianceLimit, RaggedUniformModel.N, G, normalizedRaggedQuantile, he] using hh

end Exceedance
#print axioms Exceedance.ragged_continuous_score_ceil_coverage_certificate
