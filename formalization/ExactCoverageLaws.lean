import UniformBetaLaw
import CoverageMoments

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma uniform_marginal_law (X : Ω → ℝ) (hX : Measurable X)
    (hu : ∀ t, 0 ≤ t → t ≤ 1 → μ.real {ω | X ω ≤ t} = t) : μ.map X = unitUniform := by
  letI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hnot (a : ℝ) : ∀ᵐ ω ∂μ, X ω ≠ a := by
    simpa only [ae_iff, not_not] using uniform_marginal_no_atoms X hX hu a
  have hs : ∀ᵐ ω ∂μ, X ω ∈ Ioo 0 1 := by
    filter_upwards [uniform_marginal_support X hX hu,hnot 0,hnot 1] with ω hω h0 h1
    exact ⟨lt_of_le_of_ne hω.1 h0.symm, lt_of_le_of_ne hω.2 h1⟩
  apply probability_eq_of_interior_cdf ((ae_map_iff hX.aemeasurable measurableSet_Ioo).mpr hs) unitUniform_ae_open
  intro p hp
  rw [map_measureReal_apply hX measurableSet_Iic, unitUniform_cdf p hp.1.le hp.2.le]
  exact hu p hp.1.le hp.2.le

/-- Exact coverage law under independent continuous scores, including flat CDF regions. -/
theorem iid_continuous_score_beta_law {n : ℕ}
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ i t, μ.real {ω | X i ω ≤ t} = F t) (k : Fin n) :
    μ.map (fun ω ↦ F (sampleQuantile (fun i ↦ X i ω) k)) = betaMeasure (k.val+1) (n-k.val) := by
  have hu (i : Fin n) : μ.map (fun ω ↦ F (X i ω)) = unitUniform :=
    uniform_marginal_law _ (hF.measurable.comp (hX i))
      (continuous_cdf_transform (X i) F hF hmono h0 h1 (hCDF i))
  have hh := iid_uniform_orderStatistic_beta_law (fun i ω ↦ F (X i ω))
    (fun i ↦ hF.measurable.comp (hX i)) (hi.comp (fun _ ↦ F) (fun _ ↦ hF.measurable)) hu k
  have he (ω : Ω) : sampleQuantile (fun i ↦ F (X i ω)) k = F (sampleQuantile (fun i ↦ X i ω) k) :=
    sampleQuantile_monotone_map _ k F hmono
  simpa only [he] using hh

/-- Repeat each value m times, as in identical-member clusters. -/
def replicatedSample {b : ℕ} (m : ℕ) (x : Fin b → ℝ) (i : Fin (b*m)) : ℝ :=
  x (finProdFinEquiv.symm i).1

lemma replicatedSample_count {b : ℕ} (m : ℕ) (x : Fin b → ℝ) (t : ℝ) :
    (Finset.univ.filter (fun i ↦ replicatedSample m x i ≤ t)).card =
      m*(Finset.univ.filter (fun i ↦ x i ≤ t)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  have he := Equiv.sum_comp (finProdFinEquiv : Fin b × Fin m ≃ Fin (b*m))
    (fun i ↦ if replicatedSample m x i ≤ t then (1:ℕ) else 0)
  rw [← he, Fintype.sum_prod_type]
  simp only [replicatedSample, Equiv.symm_apply_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]
  norm_cast

lemma replicatedSample_quantile {b : ℕ} (m : ℕ) (hm : 0 < m) (x : Fin b → ℝ) (k : Fin (b*m)) :
    sampleQuantile (replicatedSample m x) k =
      sampleQuantile x ⟨k.val/m, (Nat.div_lt_iff_lt_mul hm).mpr k.isLt⟩ := by
  have he (t : ℝ) : sampleQuantile (replicatedSample m x) k ≤ t ↔
      sampleQuantile x ⟨k.val/m, (Nat.div_lt_iff_lt_mul hm).mpr k.isLt⟩ ≤ t := by
    rw [sampleQuantile_le_iff, sampleQuantile_le_iff, replicatedSample_count]
    simp only [← Nat.lt_iff_add_one_le]
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hm).symm
  exact le_antisymm ((he _).mpr le_rfl) ((he _).mp le_rfl)

/-- The exact Beta law for identical-member clusters, at the actual pooled rank. -/
theorem identical_cluster_score_beta_law {b : ℕ}
    (X : Fin b → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (F : ℝ → ℝ) (hF : Continuous F) (hmono : Monotone F)
    (h0 : Tendsto F atBot (nhds 0)) (h1 : Tendsto F atTop (nhds 1))
    (hCDF : ∀ i t, μ.real {ω | X i ω ≤ t} = F t)
    (m : ℕ) (hm : 0 < m) (k : Fin (b*m)) :
    μ.map (fun ω ↦ F (sampleQuantile (replicatedSample m (fun i ↦ X i ω)) k)) =
      betaMeasure ((k.val/m:ℕ)+1) (b-(k.val/m:ℕ)) := by
  simp_rw [replicatedSample_quantile m hm]
  exact iid_continuous_score_beta_law X hX hi F hF hmono h0 h1 hCDF _

end Exceedance
#print axioms Exceedance.iid_continuous_score_beta_law
#print axioms Exceedance.identical_cluster_score_beta_law
