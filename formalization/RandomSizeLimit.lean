import RandomSizeModel

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

/-- Assumptions (S1)–(S2) of Section 4.4. Cluster `j` is `Z j = (M_j, slots)`.
    Independence and identical distribution are required of the observed clusters only,
    that is, of the size together with the active rows. `F` is the row-weighted CDF. -/
structure RandomSizeModel (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (M : ℕ) where
  Z : ℕ → Ω → SizedCluster M
  measurable : ∀ j, Measurable (Z j)
  independent : iIndepFun (fun j ω ↦ activeCluster (Z j ω)) μ
  identical : ∀ j, IdentDistrib (fun ω ↦ activeCluster (Z j ω))
    (fun ω ↦ activeCluster (Z 0 ω)) μ μ
  size_pos : ∀ j ω, 1 ≤ (Z j ω).1
  size_le : ∀ j ω, (Z j ω).1 ≤ M
  F : ℝ → ℝ
  continuous : Continuous F
  row_cdf : ∀ t, F t = (∫ ω, sizedCount id t (Z 0 ω) ∂μ)/(∫ ω, ((Z 0 ω).1 : ℝ) ∂μ)

namespace RandomSizeModel
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {M : ℕ}
variable (G : RandomSizeModel Ω μ M)

/-- The mean cluster size `μ = E M_j`. -/
noncomputable def meanSize : ℝ := ∫ ω, ((G.Z 0 ω).1 : ℝ) ∂μ

/-- `σ² = Var R_j(p₀)`. -/
noncomputable def residualVariance (p0 : ℝ) : ℝ :=
  Var[fun ω ↦ sizedResidual G.F p0 p0 (G.Z 0 ω); μ]

lemma measurable_size (j : ℕ) : Measurable (fun ω ↦ ((G.Z j ω).1 : ℝ)) :=
  measurable_from_nat.comp (measurable_fst.comp (G.measurable j))

lemma size_integrable (j : ℕ) : Integrable (fun ω ↦ ((G.Z j ω).1 : ℝ)) μ := by
  apply Integrable.of_bound (G.measurable_size j).aestronglyMeasurable (M:ℝ)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast G.size_le j ω

lemma meanSize_ge_one : 1 ≤ G.meanSize := by
  have hh := integral_mono (μ := μ) (integrable_const (1:ℝ)) (G.size_integrable 0)
    (fun ω ↦ show (1:ℝ) ≤ ((G.Z 0 ω).1 : ℝ) from by exact_mod_cast G.size_pos 0 ω)
  rw [integral_const, probReal_univ, one_smul] at hh
  exact hh

lemma meanSize_pos : 0 < G.meanSize := lt_of_lt_of_le zero_lt_one G.meanSize_ge_one

lemma count_measurable (H : ℝ → ℝ) (hH : Measurable H) (t : ℝ) (j : ℕ) :
    Measurable (fun ω ↦ sizedCount H t (G.Z j ω)) :=
  (measurable_sizedCount H hH t).comp (G.measurable j)

lemma count_integrable (H : ℝ → ℝ) (hH : Measurable H) (t : ℝ) (j : ℕ) :
    Integrable (fun ω ↦ sizedCount H t (G.Z j ω)) μ := by
  apply Integrable.of_bound (G.count_measurable H hH t j).aestronglyMeasurable (M:ℝ)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sizedCount_nonneg _ _ _)]
  exact (sizedCount_le_size H t _ (G.size_le j ω)).trans (by exact_mod_cast G.size_le j ω)

lemma count_mean_le (H : ℝ → ℝ) (hH : Measurable H) (t : ℝ) :
    (∫ ω, sizedCount H t (G.Z 0 ω) ∂μ) ≤ G.meanSize :=
  integral_mono (G.count_integrable H hH t 0) (G.size_integrable 0)
    (fun ω ↦ sizedCount_le_size H t _ (G.size_le 0 ω))

lemma rawCount_mean (x : ℝ) : (∫ ω, sizedCount id x (G.Z 0 ω) ∂μ) = G.meanSize * G.F x := by
  rw [G.row_cdf x]
  change _ = G.meanSize * (_ / G.meanSize)
  field_simp [G.meanSize_pos.ne']

/-- The row-weighted CDF is nondecreasing. -/
lemma monotone_F : Monotone G.F := by
  intro s t hst
  rw [G.row_cdf s, G.row_cdf t]
  apply div_le_div_of_nonneg_right _ G.meanSize_pos.le
  exact integral_mono (G.count_integrable id measurable_id s 0)
    (G.count_integrable id measurable_id t 0)
    (fun ω ↦ sizedCount_mono id id s t (fun u hu ↦ le_trans hu hst) _)

lemma F_tendsto_atTop : Tendsto G.F atTop (nhds 1) := by
  have h : Tendsto (fun x ↦ ∫ ω, sizedCount id x (G.Z 0 ω) ∂μ) atTop (nhds G.meanSize) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (M:ℝ))
    · exact Eventually.of_forall (fun x ↦ (G.count_measurable id measurable_id x 0).aestronglyMeasurable)
    · refine Eventually.of_forall (fun x ↦ Eventually.of_forall (fun ω ↦ ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (sizedCount_nonneg _ _ _)]
      exact (sizedCount_le_size id x _ (G.size_le 0 ω)).trans (by exact_mod_cast G.size_le 0 ω)
    · exact integrable_const _
    · refine Eventually.of_forall (fun ω ↦ ?_)
      rw [← slotCount_eq (G.size_le 0 ω)]
      unfold sizedCount
      apply tendsto_finsetSum
      intro r _
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ((G.Z 0 ω).2 r)] with x hx
      by_cases h : r.val < (G.Z 0 ω).1 <;> simp [h, hx]
  have hd := h.div_const G.meanSize
  rw [div_self G.meanSize_pos.ne'] at hd
  exact hd.congr (fun x ↦ (G.row_cdf x).symm)

lemma F_tendsto_atBot : Tendsto G.F atBot (nhds 0) := by
  have h : Tendsto (fun x ↦ ∫ ω, sizedCount id x (G.Z 0 ω) ∂μ) atBot (nhds (∫ _ω, (0:ℝ) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (M:ℝ))
    · exact Eventually.of_forall (fun x ↦ (G.count_measurable id measurable_id x 0).aestronglyMeasurable)
    · refine Eventually.of_forall (fun x ↦ Eventually.of_forall (fun ω ↦ ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (sizedCount_nonneg _ _ _)]
      exact (sizedCount_le_size id x _ (G.size_le 0 ω)).trans (by exact_mod_cast G.size_le 0 ω)
    · exact integrable_const _
    · refine Eventually.of_forall (fun ω ↦ ?_)
      have hz : (0:ℝ) = ∑ _r : Fin M, (0:ℝ) := by simp
      rw [hz]
      unfold sizedCount
      apply tendsto_finsetSum
      intro r _
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_lt_atBot ((G.Z 0 ω).2 r)] with x hx
      simp [not_le.mpr hx]
  have hd := h.div_const G.meanSize
  simp only [integral_zero, zero_div] at hd
  exact hd.congr (fun x ↦ (G.row_cdf x).symm)

/-- (S2) makes the row-weighted average of the transformed scores uniform:
    `E X_j(t) = μ t` at interior levels, although individual rows need not be uniform. -/
theorem count_mean (t : ℝ) (ht : t ∈ Ioo 0 1) :
    (∫ ω, sizedCount G.F t (G.Z 0 ω) ∂μ) = G.meanSize * t := by
  have hFm := G.continuous.measurable
  have hm := G.meanSize_pos
  apply le_antisymm
  · by_contra hle
    have hlt : G.meanSize * t < ∫ ω, sizedCount G.F t (G.Z 0 ω) ∂μ := lt_of_not_ge hle
    have hub := G.count_mean_le G.F hFm t
    let g := (∫ ω, sizedCount G.F t (G.Z 0 ω) ∂μ)/G.meanSize
    have hg : G.meanSize * g = ∫ ω, sizedCount G.F t (G.Z 0 ω) ∂μ := by
      dsimp [g]; field_simp
    have htg : t < g := by
      have : G.meanSize * t < G.meanSize * g := by rw [hg]; exact hlt
      exact lt_of_mul_lt_mul_left this hm.le
    have hg1 : g ≤ 1 := by
      have : G.meanSize * g ≤ G.meanSize * 1 := by rw [hg, mul_one]; exact hub
      exact le_of_mul_le_mul_left this hm
    let u := (t+g)/2
    obtain ⟨x, hx⟩ := continuous_cdf_hits_interior G.F G.continuous G.F_tendsto_atBot
      G.F_tendsto_atTop u (by dsimp [u]; linarith [ht.1]) (by dsimp [u]; linarith [ht.2])
    have hmono := integral_mono (G.count_integrable G.F hFm t 0)
      (G.count_integrable id measurable_id x 0)
      (fun ω ↦ sizedCount_mono G.F id t x (fun s hs ↦ by
        by_contra hn
        have hh := G.monotone_F (le_of_lt (lt_of_not_ge hn))
        rw [hx] at hh
        dsimp [u] at hh
        linarith) (G.Z 0 ω))
    rw [G.rawCount_mean x, hx, ← hg] at hmono
    have : g ≤ u := le_of_mul_le_mul_left hmono hm
    dsimp [u] at this
    linarith
  · obtain ⟨x, hx⟩ := continuous_cdf_hits_interior G.F G.continuous G.F_tendsto_atBot
      G.F_tendsto_atTop t ht.1 ht.2
    have hmono := integral_mono (G.count_integrable id measurable_id x 0)
      (G.count_integrable G.F hFm t 0)
      (fun ω ↦ sizedCount_mono id G.F x t (fun s hs ↦ by
        have hh := G.monotone_F (show s ≤ x from hs)
        rw [hx] at hh
        exact hh) (G.Z 0 ω))
    rw [G.rawCount_mean x, hx] at hmono
    exact hmono

/-- Functions of the observed cluster have the same law in every cluster. -/
lemma identDistrib_comp (g : SizedCluster M → ℝ) (hg : Measurable g)
    (hga : ∀ z, g (activeCluster z) = g z) (j : ℕ) :
    IdentDistrib (fun ω ↦ g (G.Z j ω)) (fun ω ↦ g (G.Z 0 ω)) μ μ := by
  have hh := (G.identical j).comp hg
  simpa only [Function.comp_def, hga] using hh

lemma residual_measurable (p0 t : ℝ) (j : ℕ) :
    Measurable (fun ω ↦ sizedResidual G.F p0 t (G.Z j ω)) :=
  (measurable_sizedResidual G.F G.continuous.measurable p0 t).comp (G.measurable j)

lemma residual_abs_le (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (t : ℝ) (j : ℕ) (ω : Ω) :
    |sizedResidual G.F p0 t (G.Z j ω)| ≤ M :=
  sizedResidual_abs_le G.F p0 t ⟨hp.1.le, hp.2.le⟩ _ (G.size_le j ω)

lemma residual_memLp (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (t : ℝ) (j : ℕ) :
    MemLp (fun ω ↦ sizedResidual G.F p0 t (G.Z j ω)) 2 μ :=
  MemLp.of_bound (G.residual_measurable p0 t j).aestronglyMeasurable (M:ℝ)
    (Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs]; exact G.residual_abs_le p0 hp t j ω))

lemma residual_mean (p0 : ℝ) (_hp : p0 ∈ Ioo 0 1) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    (∫ ω, sizedResidual G.F p0 t (G.Z 0 ω) ∂μ) = G.meanSize * (t-p0) := by
  unfold sizedResidual
  rw [integral_sub (G.count_integrable G.F G.continuous.measurable t 0)
    ((G.size_integrable 0).const_mul p0), integral_const_mul, G.count_mean t ht]
  change G.meanSize * t - p0 * G.meanSize = _
  ring

/-- The mean absolute increment of the cluster count is `μ |t - s|`. -/
lemma count_increment_abs (s t : ℝ) (hs : s ∈ Ioo 0 1) (ht : t ∈ Ioo 0 1) :
    (∫ ω, |sizedCount G.F t (G.Z 0 ω) - sizedCount G.F s (G.Z 0 ω)| ∂μ) =
      G.meanSize * |t-s| := by
  have hFm := G.continuous.measurable
  rcases le_total s t with hst | hts
  · have he : (fun ω ↦ |sizedCount G.F t (G.Z 0 ω) - sizedCount G.F s (G.Z 0 ω)|) =
        (fun ω ↦ sizedCount G.F t (G.Z 0 ω) - sizedCount G.F s (G.Z 0 ω)) := by
      funext ω
      exact abs_of_nonneg (sub_nonneg.mpr
        (sizedCount_mono G.F G.F s t (fun u hu ↦ le_trans hu hst) _))
    rw [he, integral_sub (G.count_integrable G.F hFm t 0) (G.count_integrable G.F hFm s 0),
      G.count_mean t ht, G.count_mean s hs, abs_of_nonneg (sub_nonneg.mpr hst)]
    ring
  · have he : (fun ω ↦ |sizedCount G.F t (G.Z 0 ω) - sizedCount G.F s (G.Z 0 ω)|) =
        (fun ω ↦ sizedCount G.F s (G.Z 0 ω) - sizedCount G.F t (G.Z 0 ω)) := by
      funext ω
      rw [abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr
        (sizedCount_mono G.F G.F t s (fun u hu ↦ le_trans hu hts) _))
    rw [he, integral_sub (G.count_integrable G.F hFm s 0) (G.count_integrable G.F hFm t 0),
      G.count_mean t ht, G.count_mean s hs, abs_of_nonpos (sub_nonpos.mpr hts)]
    ring

lemma residual_second_moment_bound (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    |(∫ ω, (sizedResidual G.F p0 t (G.Z 0 ω))^2 ∂μ) -
      ∫ ω, (sizedResidual G.F p0 p0 (G.Z 0 ω))^2 ∂μ| ≤ 2*M*(G.meanSize * |t-p0|) := by
  have hFm := G.continuous.measurable
  have hit := (G.residual_memLp p0 hp t 0).integrable_sq
  have hip := (G.residual_memLp p0 hp p0 0).integrable_sq
  have hid : Integrable (fun ω ↦ |sizedCount G.F t (G.Z 0 ω) - sizedCount G.F p0 (G.Z 0 ω)|) μ :=
    ((G.count_integrable G.F hFm t 0).sub (G.count_integrable G.F hFm p0 0)).abs
  rw [← integral_sub hit hip, ← G.count_increment_abs p0 t hp ht, ← integral_const_mul]
  apply (abs_integral_le_integral_abs).trans
  apply integral_mono (hit.sub hip).abs (hid.const_mul _)
  intro ω
  have ha := abs_le.mp (G.residual_abs_le p0 hp t 0 ω)
  have hb := abs_le.mp (G.residual_abs_le p0 hp p0 0 ω)
  have hd : sizedResidual G.F p0 t (G.Z 0 ω) - sizedResidual G.F p0 p0 (G.Z 0 ω) =
      sizedCount G.F t (G.Z 0 ω) - sizedCount G.F p0 (G.Z 0 ω) := by
    unfold sizedResidual; ring
  change |(sizedResidual G.F p0 t (G.Z 0 ω))^2 - (sizedResidual G.F p0 p0 (G.Z 0 ω))^2| ≤
    2*M*|sizedCount G.F t (G.Z 0 ω) - sizedCount G.F p0 (G.Z 0 ω)|
  rw [← hd, show (sizedResidual G.F p0 t (G.Z 0 ω))^2 - (sizedResidual G.F p0 p0 (G.Z 0 ω))^2 =
    (sizedResidual G.F p0 t (G.Z 0 ω) + sizedResidual G.F p0 p0 (G.Z 0 ω)) *
    (sizedResidual G.F p0 t (G.Z 0 ω) - sizedResidual G.F p0 p0 (G.Z 0 ω)) by ring, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  exact abs_le.mpr ⟨by linarith [ha.1, hb.1], by linarith [ha.2, hb.2]⟩

/-- The variance of `Y_j(t)` is continuous at `t = p₀`. -/
theorem residual_variance_tendsto (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (nhds p0)) :
    Tendsto (fun n ↦ Var[fun ω ↦ sizedResidual G.F p0 (τ n) (G.Z 0 ω); μ]) atTop
      (nhds (G.residualVariance p0)) := by
  have hev : ∀ᶠ n in atTop, τ n ∈ Ioo 0 1 := hτ.eventually (Ioo_mem_nhds hp.1 hp.2)
  have hd : Tendsto (fun n ↦ |τ n - p0|) atTop (nhds 0) := by
    have hh := (hτ.sub_const p0).abs
    simpa using hh
  have h2 : Tendsto (fun n ↦ ∫ ω, (sizedResidual G.F p0 (τ n) (G.Z 0 ω))^2 ∂μ) atTop
      (nhds (∫ ω, (sizedResidual G.F p0 p0 (G.Z 0 ω))^2 ∂μ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun n ↦ 2*M*(G.meanSize * |τ n - p0|)) atTop (nhds 0) := by
      have hh := (hd.const_mul G.meanSize).const_mul (2*(M:ℝ))
      simpa using hh
    apply squeeze_zero' (Eventually.of_forall (fun n ↦ norm_nonneg _)) _ hb
    filter_upwards [hev] with n hn
    rw [Real.norm_eq_abs]
    exact G.residual_second_moment_bound p0 hp (τ n) hn
  have h1 : Tendsto (fun n ↦ (G.meanSize * (τ n - p0))^2) atTop (nhds 0) := by
    have hh := ((hτ.sub_const p0).const_mul G.meanSize).pow 2
    simpa using hh
  have hh := h2.sub h1
  have hv0 : G.residualVariance p0 = (∫ ω, (sizedResidual G.F p0 p0 (G.Z 0 ω))^2 ∂μ) - 0 := by
    unfold residualVariance
    have hv := variance_eq_sub (G.residual_memLp p0 hp p0 0)
    simp only [Pi.pow_apply] at hv
    rw [hv, G.residual_mean p0 hp p0 hp]
    simp
  rw [hv0]
  apply hh.congr'
  filter_upwards [hev] with n hn
  have hv := variance_eq_sub (G.residual_memLp p0 hp (τ n) 0)
  simp only [Pi.pow_apply] at hv
  rw [hv, G.residual_mean p0 hp (τ n) hn]

lemma residualVariance_nonneg (p0 : ℝ) : 0 ≤ G.residualVariance p0 := variance_nonneg _ _

/-- Proposition 3, cluster scale: `√b (C - p₀) ⇒ N(0, σ²/μ²)` for the actual pooled order
    statistic with ceiling rank and infinite cutoff, as a CDF limit at every continuity point.
    Zero variance is included. -/
theorem coverage_cdf (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (x : ℝ)
    (hx : (G.residualVariance p0/G.meanSize^2).toNNReal ≠ 0 ∨ x ≠ 0) :
    Tendsto (fun b : ℕ ↦ μ.real {ω | √(b:ℝ) *
      (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0) ≤ x}) atTop
      (nhds (cdf (gaussianReal 0 (G.residualVariance p0/G.meanSize^2).toNNReal) x)) := by
  have hm := G.meanSize_pos
  let v : NNReal := (G.residualVariance p0/G.meanSize^2).toNNReal
  have hv : (v:ℝ) = G.residualVariance p0/G.meanSize^2 :=
    Real.coe_toNNReal _ (div_nonneg (G.residualVariance_nonneg p0) (sq_nonneg _))
  let s : ℕ → ℝ := fun n ↦ √((n:ℝ)+1)
  have hs (n : ℕ) : 0 < s n := Real.sqrt_pos.mpr (by positivity)
  have hs2 (n : ℕ) : (s n)^2 = (n:ℝ)+1 := Real.sq_sqrt (by positivity)
  have hNt : Tendsto (fun n : ℕ ↦ (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n ↦ (s n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hNt)
  let τ : ℕ → ℝ := fun n ↦ p0 + x/s n
  have hτ : Tendsto τ atTop (nhds p0) := by
    have hh := (hi.const_mul x).const_add p0
    simpa only [mul_zero, add_zero, ← div_eq_mul_inv] using hh
  have hev : ∀ᶠ n in atTop, τ n ∈ Ioo 0 1 := hτ.eventually (Ioo_mem_nhds hp.1 hp.2)
  let c : ℕ → ℝ := fun n ↦ ∫ ω, sizedResidual G.F p0 (τ n) (G.Z 0 ω) ∂μ
  let g : ℕ → SizedCluster M → ℝ := fun n z ↦ G.meanSize⁻¹ * (sizedResidual G.F p0 (τ n) z - c n)
  have hg (n : ℕ) : Measurable (g n) :=
    ((measurable_sizedResidual G.F G.continuous.measurable p0 (τ n)).sub_const _).const_mul _
  have hga (n : ℕ) (z : SizedCluster M) : g n (activeCluster z) = g n z := by
    dsimp [g]; rw [sizedResidual_activeCluster]
  let A : (n : ℕ) → Fin (n+1) → Ω → ℝ := fun n j ω ↦ g n (G.Z j ω)
  have hA (n : ℕ) (j : Fin (n+1)) : Measurable (A n j) := (hg n).comp (G.measurable j)
  have hindep (n : ℕ) : iIndepFun (A n) μ := by
    have h1 := (G.independent.precomp (Fin.val_injective (n := n+1))).comp
      (fun _ ↦ g n) (fun _ ↦ hg n)
    simpa only [Function.comp_def, hga] using h1
  have hmeanZ (n : ℕ) (j : ℕ) : (∫ ω, sizedResidual G.F p0 (τ n) (G.Z j ω) ∂μ) = c n :=
    (G.identDistrib_comp _ (measurable_sizedResidual G.F G.continuous.measurable p0 (τ n))
      (sizedResidual_activeCluster G.F p0 (τ n)) j).integral_eq
  have hmean (n : ℕ) (j : Fin (n+1)) : (∫ ω, A n j ω ∂μ) = 0 := by
    change (∫ ω, G.meanSize⁻¹ * (sizedResidual G.F p0 (τ n) (G.Z j ω) - c n) ∂μ) = 0
    rw [integral_const_mul, integral_sub ((G.residual_memLp p0 hp (τ n) j).integrable (by norm_num))
      (integrable_const _), hmeanZ n j]
    simp
  have hbound (n : ℕ) (j : Fin (n+1)) : ∀ᵐ ω ∂μ, |A n j ω| ≤ 2*M := by
    filter_upwards with ω
    have h1 := G.residual_abs_le p0 hp (τ n) j ω
    have hc : |c n| ≤ M := by
      apply (abs_integral_le_integral_abs).trans
      have hh := integral_mono (μ := μ)
        ((G.residual_memLp p0 hp (τ n) 0).integrable (by norm_num)).abs
        (integrable_const (M:ℝ)) (fun ω ↦ G.residual_abs_le p0 hp (τ n) 0 ω)
      rw [integral_const, probReal_univ, one_smul] at hh
      exact hh
    change |G.meanSize⁻¹ * (sizedResidual G.F p0 (τ n) (G.Z j ω) - c n)| ≤ 2*M
    rw [abs_mul, abs_of_pos (inv_pos.mpr hm)]
    have h2 : |sizedResidual G.F p0 (τ n) (G.Z j ω) - c n| ≤ 2*M :=
      (abs_sub _ _).trans (by linarith)
    have h3 : G.meanSize⁻¹ ≤ 1 := inv_le_one_of_one_le₀ G.meanSize_ge_one
    calc
      _ ≤ 1 * (2*(M:ℝ)) := mul_le_mul h3 h2 (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hvarA (n : ℕ) (j : Fin (n+1)) : Var[A n j; μ] =
      G.meanSize⁻¹^2 * Var[fun ω ↦ sizedResidual G.F p0 (τ n) (G.Z 0 ω); μ] := by
    change Var[fun ω ↦ G.meanSize⁻¹ * (sizedResidual G.F p0 (τ n) (G.Z j ω) - c n); μ] = _
    rw [variance_const_mul, variance_sub_const (G.residual_measurable p0 (τ n) j).aestronglyMeasurable]
    congr 1
    exact (G.identDistrib_comp _ (measurable_sizedResidual G.F G.continuous.measurable p0 (τ n))
      (sizedResidual_activeCluster G.F p0 (τ n)) j).variance_eq
  have hvar : Tendsto (fun n ↦ (∑ j, Var[A n j; μ])/((n:ℝ)+1)) atTop (nhds (v:ℝ)) := by
    have hh := (G.residual_variance_tendsto p0 hp τ hτ).const_mul (G.meanSize⁻¹^2)
    rw [hv]
    convert hh using 1
    · funext n
      simp only [hvarA, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn : ((n:ℝ)+1) ≠ 0 := by positivity
      push_cast
      field_simp
    · rw [inv_pow, div_eq_inv_mul]
  have hclt := bounded_array_sqrt_clt (μ := μ) (fun n ↦ n+1) A hA hindep hmean (2*M)
    (by positivity) hbound (fun n ↦ (n:ℝ)+1) (fun n ↦ by positivity)
    (fun n ↦ by push_cast; exact le_refl _) hNt v hvar
  let a : ℕ → ℝ := fun n ↦ p0/(G.meanSize * s n) - x
  have ha : Tendsto a atTop (nhds (-x)) := by
    have hh := (hi.const_mul (p0/G.meanSize)).sub_const x
    simp only [mul_zero, zero_sub] at hh
    convert hh using 1
    funext n
    dsimp [a]
    rw [div_mul_eq_div_div, div_eq_mul_inv]
  have hlim := probability_ge_moving_tendsto _ (id : ℝ → ℝ) hclt a (-x) ha
    (centered_gaussian_no_atom_at_continuity id v HasLaw.id x hx)
  rw [centered_gaussian_reflected_tail id v HasLaw.id x] at hlim
  have hshift : Tendsto (fun n : ℕ ↦ μ.real {ω | √(((n+1 : ℕ)):ℝ) *
      (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) (n+1) - p0) ≤ x}) atTop
      (nhds (cdf (gaussianReal 0 v) x)) := by
    apply hlim.congr'
    filter_upwards [hev] with n hn
    congr 1
    ext ω
    simp only [mem_setOf_eq]
    have hcn : c n = G.meanSize * (x/s n) := by
      dsimp [c]
      rw [G.residual_mean p0 hp (τ n) hn]
      dsimp [τ]
      ring
    have hsum : (∑ j : Fin (n+1), A n j ω) = G.meanSize⁻¹ *
        ((∑ j ∈ Finset.range (n+1), sizedResidual G.F p0 (τ n) (G.Z j ω)) - ((n:ℝ)+1)*c n) := by
      rw [Fin.sum_univ_eq_sum_range (fun j ↦ g n (G.Z j ω)) (n+1)]
      dsimp [g]
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      push_cast
      rfl
    have hW : (∑ j : Fin (n+1), A n j ω)/√((n:ℝ)+1) =
        (∑ j ∈ Finset.range (n+1), sizedResidual G.F p0 (τ n) (G.Z j ω))/(G.meanSize * s n) - x := by
      rw [hsum, hcn]
      change _ / s n = _
      have hsn := (hs n).ne'
      have hmn := hm.ne'
      field_simp
      rw [← hs2 n]
      ring
    have hcast : √(((n+1 : ℕ)):ℝ) = s n := by dsimp [s]; push_cast; rfl
    rw [hW, hcast]
    dsimp [a]
    rw [sub_le_sub_iff_right, div_le_div_iff_of_pos_right (mul_pos hm (hs n)),
      ← pooledCoverage_le_iff G.F G.monotone_F p0 hp (fun j ↦ G.Z j ω) (n+1) (τ n) hn.2]
    dsimp [τ]
    rw [mul_comm, ← le_div_iff₀ (hs n), sub_le_iff_le_add']
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

end RandomSizeModel
end Exceedance

#print axioms Exceedance.RandomSizeModel.monotone_F
#print axioms Exceedance.RandomSizeModel.count_mean
#print axioms Exceedance.RandomSizeModel.residual_variance_tendsto
#print axioms Exceedance.RandomSizeModel.coverage_cdf
