import RandomSizeLimit
import RandomSizeSlutsky
import Mathlib.Probability.StrongLaw

open MeasureTheory ProbabilityTheory Filter Set
open scoped Function
namespace Exceedance

lemma pooledSize_cast {M : ℕ} (z : ℕ → SizedCluster M) (b : ℕ) :
    (pooledSize z b : ℝ) = ∑ j ∈ Finset.range b, ((z j).1 : ℝ) := by
  unfold pooledSize
  push_cast
  rfl

/-- Every cluster has at least one row, so `b ≤ n`. -/
lemma le_pooledSize {M : ℕ} (z : ℕ → SizedCluster M) (hz : ∀ j, 1 ≤ (z j).1) (b : ℕ) :
    b ≤ pooledSize z b := by
  have hh := Finset.sum_le_sum (s := Finset.range b) (fun j _ ↦ hz j)
  unfold pooledSize
  simpa using hh

namespace RandomSizeModel
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {M : ℕ}
variable (G : RandomSizeModel Ω μ M)

/-- The law of large numbers for the random sample size: `√(n/b) → √μ` in probability. -/
theorem sqrt_size_ratio_tendsto (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun b : ℕ ↦ μ.real {ω | δ <
      |√((pooledSize (fun j ↦ G.Z j ω) b : ℝ)/b) - √G.meanSize|}) atTop (nhds 0) := by
  let X : ℕ → Ω → ℝ := fun i ω ↦ ((G.Z i ω).1 : ℝ)
  have hφ : Measurable (fun z : SizedCluster M ↦ (z.1 : ℝ)) :=
    measurable_from_nat.comp measurable_fst
  have hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X) := by
    intro i j hij
    exact (G.independent.indepFun hij).comp hφ hφ
  have hident (i : ℕ) : IdentDistrib (X i) (X 0) μ μ :=
    G.identDistrib_comp (fun z ↦ (z.1 : ℝ)) hφ (fun _ ↦ rfl) i
  have hae := strong_law_ae X (G.size_integrable 0) hindep hident
  let f : ℕ → Ω → ℝ := fun b ω ↦ √((pooledSize (fun j ↦ G.Z j ω) b : ℝ)/b)
  have hf (b : ℕ) : Measurable (f b) := by
    have he : f b = fun ω ↦ √((∑ j ∈ Finset.range b, X j ω)/b) := by
      funext ω
      dsimp [f]
      rw [pooledSize_cast]
    rw [he]
    exact ((Finset.measurable_sum _ (fun j _ ↦ G.measurable_size j)).div_const _).sqrt
  have hae' : ∀ᵐ ω ∂μ, Tendsto (fun b ↦ f b ω) atTop (nhds (√G.meanSize)) := by
    filter_upwards [hae] with ω hω
    have hh := (Real.continuous_sqrt.tendsto _).comp hω
    apply hh.congr
    intro b
    dsimp [f]
    rw [pooledSize_cast, div_eq_inv_mul]
  have him := tendstoInMeasure_of_tendsto_ae (fun b ↦ (hf b).aestronglyMeasurable) hae'
  have hr := tendstoInMeasure_iff_measureReal_norm.mp him δ hδ
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hr
  intro b
  refine measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)
  have h' : δ < |f b ω - √G.meanSize| := hω
  rw [mem_setOf_eq, Real.norm_eq_abs]
  exact h'.le

/-- Proposition 3, first conclusion: `√n (C - p_n) ⇒ N(0, v(p₀))` with `v(p₀) = σ²/μ`,
    the random sample size `n`, and the random rank level `p_n = ⌈(n+1)p₀⌉/(n+1)`.
    The limit is a CDF limit at every continuity point, and zero variance is included. -/
theorem row_scale_cdf (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (x : ℝ)
    (hx : (G.residualVariance p0/G.meanSize).toNNReal ≠ 0 ∨ x ≠ 0) :
    Tendsto (fun b : ℕ ↦ μ.real {ω | √(pooledSize (fun j ↦ G.Z j ω) b : ℝ) *
      (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b -
        (pooledRank p0 (fun j ↦ G.Z j ω) b : ℝ)/((pooledSize (fun j ↦ G.Z j ω) b : ℝ)+1)) ≤ x})
      atTop (nhds (cdf (gaussianReal 0 (G.residualVariance p0/G.meanSize).toNNReal) x)) := by
  have hm := G.meanSize_pos
  let a := √G.meanSize
  have ha : 0 < a := Real.sqrt_pos.mpr hm
  let v : NNReal := (G.residualVariance p0/G.meanSize^2).toNNReal
  let w : NNReal := (G.residualVariance p0/G.meanSize).toNNReal
  have hw : (w:ℝ) = a^2 * v := by
    rw [Real.coe_toNNReal _ (div_nonneg (G.residualVariance_nonneg p0) hm.le),
      Real.coe_toNNReal _ (div_nonneg (G.residualVariance_nonneg p0) (sq_nonneg _)),
      Real.sq_sqrt hm.le]
    field_simp
  have hvx : v ≠ 0 ∨ x/a ≠ 0 := by
    rcases hx with hw0 | hx0
    · left
      intro hv0
      apply hw0
      apply NNReal.eq
      change (w:ℝ) = 0
      rw [hw, hv0]
      simp
    · exact Or.inr (div_ne_zero hx0 ha.ne')
  let T : ℕ → Ω → ℝ := fun b ω ↦ √(b:ℝ) * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0)
  let A : ℕ → Ω → ℝ := fun b ω ↦ √((pooledSize (fun j ↦ G.Z j ω) b : ℝ)/b)
  let r : ℕ → Ω → ℝ := fun b ω ↦ √(pooledSize (fun j ↦ G.Z j ω) b : ℝ) *
    ((pooledRank p0 (fun j ↦ G.Z j ω) b : ℝ)/((pooledSize (fun j ↦ G.Z j ω) b : ℝ)+1) - p0)
  let W : ℕ → Ω → ℝ := fun b ω ↦ √(pooledSize (fun j ↦ G.Z j ω) b : ℝ) *
      (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b -
        (pooledRank p0 (fun j ↦ G.Z j ω) b : ℝ)/((pooledSize (fun j ↦ G.Z j ω) b : ℝ)+1))
  have hT : ∀ᶠ y in nhds (x/a), Tendsto (fun b ↦ μ.real {ω | T b ω ≤ y}) atTop
      (nhds (cdf (gaussianReal 0 v) y)) := by
    rcases hvx with hv | hxa
    · exact Eventually.of_forall (fun y ↦ G.coverage_cdf p0 hp y (Or.inl hv))
    · filter_upwards [isOpen_ne.mem_nhds hxa] with y hy
      exact G.coverage_cdf p0 hp y (Or.inr hy)
  have hε : Tendsto (fun b : ℕ ↦ 1/√(b:ℝ)) atTop (nhds 0) := by
    have hh := tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa only [one_div, Function.comp_def] using hh
  have hr : ∀ᶠ b in atTop, ∀ ω, 0 ≤ r b ω ∧ r b ω ≤ 1/√(b:ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with b hb ω
    have hbpos : (0:ℝ) < b := by exact_mod_cast hb
    have hbn : (b:ℝ) ≤ (pooledSize (fun j ↦ G.Z j ω) b : ℝ) := by
      exact_mod_cast le_pooledSize (fun j ↦ G.Z j ω) (fun j ↦ G.size_pos j ω) b
    dsimp only [r, pooledRank]
    generalize (pooledSize (fun j ↦ G.Z j ω) b : ℝ) = n at hbn ⊢
    have hn0 : 0 ≤ n := hbpos.le.trans hbn
    have hn1 : 0 < n+1 := by linarith
    have hk1 : (n+1)*p0 ≤ (Nat.ceil ((n+1)*p0) : ℝ) := Nat.le_ceil _
    have hk2 : (Nat.ceil ((n+1)*p0) : ℝ) < (n+1)*p0 + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hn1.le hp.1.le)
    have hd : (Nat.ceil ((n+1)*p0) : ℝ)/(n+1) - p0 = ((Nat.ceil ((n+1)*p0) : ℝ) - (n+1)*p0)/(n+1) := by
      field_simp
    have hd0 : 0 ≤ (Nat.ceil ((n+1)*p0) : ℝ)/(n+1) - p0 := by
      rw [hd]; exact div_nonneg (by linarith) hn1.le
    have hd1 : (Nat.ceil ((n+1)*p0) : ℝ)/(n+1) - p0 ≤ 1/(n+1) := by
      rw [hd]; exact div_le_div_of_nonneg_right (by linarith) hn1.le
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) hd0, ?_⟩
    have hsb : 0 < √(b:ℝ) := Real.sqrt_pos.mpr hbpos
    calc
      _ ≤ √n * (1/(n+1)) := mul_le_mul_of_nonneg_left hd1 (Real.sqrt_nonneg _)
      _ ≤ 1/√(b:ℝ) := by
        rw [mul_one_div, div_le_div_iff₀ hn1 hsb]
        nlinarith [Real.sqrt_nonneg n, Real.mul_self_sqrt hn0, Real.sqrt_le_sqrt hbn,
          Real.sqrt_nonneg (b:ℝ)]
  have hW : ∀ᶠ b in atTop, ∀ ω, W b ω = A b ω * T b ω - r b ω := by
    filter_upwards [eventually_ge_atTop 1] with b hb ω
    have hbpos : (0:ℝ) < b := by exact_mod_cast hb
    have hsb : √(b:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hbpos).ne'
    dsimp only [W, A, T, r]
    rw [Real.sqrt_div (Nat.cast_nonneg _)]
    field_simp
    ring
  have hmain := cdf_limit_scaled_shifted T A r W (cdf (gaussianReal 0 v)) a ha x
    (centered_gaussian_cdf_continuousAt v _ hvx) hT (G.sqrt_size_ratio_tendsto) _ hε hr hW
  rw [centered_gaussian_cdf_scale v w a ha hw x] at hmain
  exact hmain

end RandomSizeModel
end Exceedance

#print axioms Exceedance.RandomSizeModel.sqrt_size_ratio_tendsto
#print axioms Exceedance.RandomSizeModel.row_scale_cdf
