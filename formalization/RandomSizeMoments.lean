import RandomSizeRowScale
import Concentration
import CoverageMoments

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

/-- A CDF limit near a continuity point of the limit also holds for the strict event. -/
theorem strict_cdf_limit {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (Φ : ℝ → ℝ) (y : ℝ) (hΦ : ContinuousAt Φ y)
    (hX : ∀ᶠ u in nhds y, Tendsto (fun n ↦ μ.real {ω | X n ω ≤ u}) atTop (nhds (Φ u))) :
    Tendsto (fun n ↦ μ.real {ω | X n ω < y}) atTop (nhds (Φ y)) := by
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨η1, hη1, hc⟩ := Metric.continuousAt_iff.mp hΦ (e/2) (by positivity)
  obtain ⟨η2, hη2, ht⟩ := Metric.eventually_nhds_iff.mp hX
  let η := min η1 η2
  have hη : 0 < η := lt_min hη1 hη2
  let u := y - η/2
  have hu : dist u y < η := by
    rw [Real.dist_eq]; dsimp [u]
    rw [show y - η/2 - y = -(η/2) by ring, abs_neg, abs_of_pos (by positivity)]
    linarith
  have hΦu := hc (lt_of_lt_of_le hu (min_le_left _ _))
  have hTu := ht (lt_of_lt_of_le hu (min_le_right _ _))
  have hTy := ht (show dist y y < η2 by rw [dist_self]; exact hη2)
  rw [Real.dist_eq] at hΦu
  filter_upwards [Metric.tendsto_nhds.mp hTu (e/2) (by positivity),
    Metric.tendsto_nhds.mp hTy (e/2) (by positivity)] with n h1 h2
  have m1 : μ.real {ω | X n ω ≤ u} ≤ μ.real {ω | X n ω < y} :=
    measureReal_mono (fun ω (h : X n ω ≤ u) ↦ show X n ω < y by dsimp [u] at h; linarith)
  have m2 : μ.real {ω | X n ω < y} ≤ μ.real {ω | X n ω ≤ y} :=
    measureReal_mono (fun ω (h : X n ω < y) ↦ le_of_lt h)
  rw [Real.dist_eq] at h1 h2 ⊢
  have a1 := abs_lt.mp hΦu
  have a2 := abs_lt.mp h1
  have a3 := abs_lt.mp h2
  exact abs_lt.mpr ⟨by linarith [a1.1, a2.1], by linarith [a3.2]⟩

/-- A squared tail splits into the two one-sided tails; atoms are allowed. -/
lemma square_tail_split {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (t : ℝ) (ht : 0 < t) :
    μ.real {ω | t < (X ω)^2} =
      μ.real {ω | X ω < -Real.sqrt t} + (1-μ.real {ω | X ω ≤ Real.sqrt t}) := by
  have hs := Real.sqrt_pos.mpr ht
  have hsq := Real.sq_sqrt ht.le
  have he : {ω | t < (X ω)^2} =
      {ω | X ω < -Real.sqrt t} ∪ {ω | Real.sqrt t < X ω} := by
    ext ω
    simp only [mem_setOf_eq, mem_union]
    constructor
    · intro h
      by_cases hx : X ω < -Real.sqrt t
      · exact Or.inl hx
      · exact Or.inr (by nlinarith)
    · rintro (h | h) <;> nlinarith
  have hd : Disjoint {ω | X ω < -Real.sqrt t} {ω | Real.sqrt t < X ω} := by
    apply disjoint_left.mpr
    intro ω h1 h2
    dsimp only [mem_setOf_eq] at h1 h2
    linarith
  rw [he, measureReal_union₀ (measurableSet_lt measurable_const hX).nullMeasurableSet hd.aedisjoint,
    probability_gt_eq_one_sub_le X hX]

lemma pooledCoverage_mem_Icc {M : ℕ} (F : ℝ → ℝ) (hF0 : ∀ s, 0 ≤ F s) (hF1 : ∀ s, F s ≤ 1)
    (p0 : ℝ) (z : ℕ → SizedCluster M) (b : ℕ) :
    0 ≤ pooledCoverage F p0 z b ∧ pooledCoverage F p0 z b ≤ 1 := by
  unfold pooledCoverage
  cases pooledCutoff p0 z b with
  | none => simp
  | some q => simp [hF0 q, hF1 q]

namespace RandomSizeModel
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {M : ℕ}
variable (G : RandomSizeModel Ω μ M)

include G in
lemma M_ge_one : (1:ℝ) ≤ M := by
  have hh := integral_mono (μ := μ) (G.size_integrable 0) (integrable_const (M:ℝ))
    (fun ω ↦ show ((G.Z 0 ω).1 : ℝ) ≤ (M:ℝ) from by exact_mod_cast G.size_le 0 ω)
  rw [integral_const, probReal_univ, one_smul] at hh
  exact G.meanSize_ge_one.trans hh

lemma F_nonneg (s : ℝ) : 0 ≤ G.F s := by
  rw [G.row_cdf s]
  exact div_nonneg (integral_nonneg (fun ω ↦ sizedCount_nonneg _ _ _)) G.meanSize_pos.le

lemma F_le_one (s : ℝ) : G.F s ≤ 1 := by
  rw [G.row_cdf s]
  exact (div_le_one G.meanSize_pos).mpr (G.count_mean_le id measurable_id s)

lemma coverage_mem_Icc (p0 : ℝ) (b : ℕ) (ω : Ω) :
    0 ≤ pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b ∧
      pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b ≤ 1 :=
  pooledCoverage_mem_Icc G.F G.F_nonneg G.F_le_one p0 _ b

/-- The coverage of the actual pooled cutoff is a random variable. -/
theorem coverage_measurable (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (b : ℕ) :
    Measurable (fun ω ↦ pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b) := by
  apply measurable_of_Iic
  intro t
  by_cases ht : t < 1
  · have he : (fun ω ↦ pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b) ⁻¹' Iic t =
        {ω | p0 ≤ ∑ j ∈ Finset.range b, sizedResidual G.F p0 t (G.Z j ω)} := by
      ext ω
      exact pooledCoverage_le_iff G.F G.monotone_F p0 hp (fun j ↦ G.Z j ω) b t ht
    rw [he]
    exact measurableSet_le measurable_const
      (Finset.measurable_sum _ (fun j _ ↦ G.residual_measurable p0 t j))
  · have he : (fun ω ↦ pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b) ⁻¹' Iic t = univ := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (G.coverage_mem_Icc p0 b ω).2.trans (not_lt.mp ht)
    rw [he]
    exact MeasurableSet.univ

/-- The mean count bound extends to the left endpoint. -/
lemma count_mean_le_closed (t : ℝ) (ht : t ∈ Ico 0 1) :
    (∫ ω, sizedCount G.F t (G.Z 0 ω) ∂μ) ≤ G.meanSize * t := by
  have hFm := G.continuous.measurable
  have hm := G.meanSize_pos
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    rw [mul_zero]
    by_contra hn
    have hg : 0 < ∫ ω, sizedCount G.F 0 (G.Z 0 ω) ∂μ := lt_of_not_ge hn
    let s := min ((∫ ω, sizedCount G.F 0 (G.Z 0 ω) ∂μ)/(2*G.meanSize)) (1/2)
    have hs0 : 0 < s := lt_min (by positivity) (by norm_num)
    have hs1 : s < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hmono := integral_mono (G.count_integrable G.F hFm 0 0) (G.count_integrable G.F hFm s 0)
      (fun ω ↦ sizedCount_mono G.F G.F 0 s (fun u hu ↦ le_trans hu hs0.le) (G.Z 0 ω))
    rw [G.count_mean s ⟨hs0, hs1⟩] at hmono
    have hsle : s ≤ (∫ ω, sizedCount G.F 0 (G.Z 0 ω) ∂μ)/(2*G.meanSize) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at hsle
    nlinarith
  · exact le_of_eq (G.count_mean t ⟨h0, ht.2⟩)

lemma residual_mem_Icc (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (t : ℝ) (j : ℕ) (ω : Ω) :
    sizedResidual G.F p0 t (G.Z j ω) ∈ Icc (-p0*(M:ℝ)) ((1-p0)*M) := by
  have h0 := sizedCount_nonneg G.F t (G.Z j ω)
  have h1 := sizedCount_le_size G.F t (G.Z j ω) (G.size_le j ω)
  have hzM : ((G.Z j ω).1 : ℝ) ≤ M := by exact_mod_cast G.size_le j ω
  have hz0 : (0:ℝ) ≤ (G.Z j ω).1 := Nat.cast_nonneg _
  unfold sizedResidual
  constructor
  · nlinarith [hp.1]
  · nlinarith [hp.1, hp.2]

lemma residual_integral_eq (p0 t : ℝ) (j : ℕ) :
    (∫ ω, sizedResidual G.F p0 t (G.Z j ω) ∂μ) = ∫ ω, sizedResidual G.F p0 t (G.Z 0 ω) ∂μ :=
  (G.identDistrib_comp _ (measurable_sizedResidual G.F G.continuous.measurable p0 t)
    (sizedResidual_activeCluster G.F p0 t) j).integral_eq

lemma residual_iIndepFun (p0 t : ℝ) (b : ℕ) :
    iIndepFun (fun (j : Fin b) ω ↦ sizedResidual G.F p0 t (G.Z j ω)) μ := by
  have h1 := (G.independent.precomp (Fin.val_injective (n := b))).comp
    (fun _ ↦ sizedResidual G.F p0 t)
    (fun _ ↦ measurable_sizedResidual G.F G.continuous.measurable p0 t)
  simpa only [Function.comp_def, sizedResidual_activeCluster] using h1

omit [IsProbabilityMeasure μ] in
lemma hoeffding_denominator (M : ℕ) (p0 : ℝ) (b : ℕ) :
    (2 * ∑ _j : Fin b, (‖(1-p0)*(M:ℝ) - (-p0*(M:ℝ))‖/2)^2) = (b:ℝ)*(M:ℝ)^2/2 := by
  have hn : (1-p0)*(M:ℝ) - (-p0*(M:ℝ)) = M := by ring
  rw [hn, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Hoeffding's inequality for the centered residual sum, upper tail. -/
theorem residual_sum_upper (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (t : ℝ) (b : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ j ∈ Finset.range b, (sizedResidual G.F p0 t (G.Z j ω) -
      ∫ ω, sizedResidual G.F p0 t (G.Z 0 ω) ∂μ)} ≤
      Real.exp (-ε^2/((b:ℝ)*(M:ℝ)^2/2)) := by
  have hh := independent_bounded_sum_upper_tail (μ := μ)
    (fun (j : Fin b) ω ↦ sizedResidual G.F p0 t (G.Z j ω))
    (fun _ ↦ -p0*(M:ℝ)) (fun _ ↦ (1-p0)*M)
    (fun j ↦ (G.residual_measurable p0 t j).aemeasurable)
    (fun j ↦ Eventually.of_forall (fun ω ↦ G.residual_mem_Icc p0 hp t j ω))
    (G.residual_iIndepFun p0 t b) ε hε
  rw [hoeffding_denominator M p0 b] at hh
  simp only [G.residual_integral_eq p0 t] at hh
  have he : {ω | ε ≤ ∑ j : Fin b, (sizedResidual G.F p0 t (G.Z j ω) -
      ∫ ω, sizedResidual G.F p0 t (G.Z 0 ω) ∂μ)} =
      {ω | ε ≤ ∑ j ∈ Finset.range b, (sizedResidual G.F p0 t (G.Z j ω) -
      ∫ ω, sizedResidual G.F p0 t (G.Z 0 ω) ∂μ)} := by
    ext ω
    rw [mem_setOf_eq, mem_setOf_eq, Fin.sum_univ_eq_sum_range (fun j ↦
      sizedResidual G.F p0 t (G.Z j ω) - ∫ ω, sizedResidual G.F p0 t (G.Z 0 ω) ∂μ) b]
  rw [he] at hh
  exact hh

/-- Hoeffding's inequality for the centered residual sum, lower tail. -/
theorem residual_sum_lower (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (t : ℝ) (b : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ j ∈ Finset.range b, ((∫ ω, sizedResidual G.F p0 t (G.Z 0 ω) ∂μ) -
      sizedResidual G.F p0 t (G.Z j ω))} ≤
      Real.exp (-ε^2/((b:ℝ)*(M:ℝ)^2/2)) := by
  have hh := independent_bounded_sum_lower_tail (μ := μ)
    (fun (j : Fin b) ω ↦ sizedResidual G.F p0 t (G.Z j ω))
    (fun _ ↦ -p0*(M:ℝ)) (fun _ ↦ (1-p0)*M)
    (fun j ↦ (G.residual_measurable p0 t j).aemeasurable)
    (fun j ↦ Eventually.of_forall (fun ω ↦ G.residual_mem_Icc p0 hp t j ω))
    (G.residual_iIndepFun p0 t b) ε hε
  rw [hoeffding_denominator M p0 b] at hh
  simp only [G.residual_integral_eq p0 t] at hh
  have he : {ω | ε ≤ ∑ j : Fin b, ((∫ ω, sizedResidual G.F p0 t (G.Z 0 ω) ∂μ) -
      sizedResidual G.F p0 t (G.Z j ω))} =
      {ω | ε ≤ ∑ j ∈ Finset.range b, ((∫ ω, sizedResidual G.F p0 t (G.Z 0 ω) ∂μ) -
      sizedResidual G.F p0 t (G.Z j ω))} := by
    ext ω
    rw [mem_setOf_eq, mem_setOf_eq, Fin.sum_univ_eq_sum_range (fun j ↦
      (∫ ω, sizedResidual G.F p0 t (G.Z 0 ω) ∂μ) - sizedResidual G.F p0 t (G.Z j ω)) b]
  rw [he] at hh
  exact hh

/-- Appendix B.11's first Hoeffding tail: the coverage error is rarely far below zero. -/
theorem coverage_lower_tail (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (b : ℕ) (hb : 1 ≤ b)
    (y : ℝ) (hy : 0 < y) :
    μ.real {ω | √(b:ℝ) * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0) ≤ -y} ≤
      Real.exp (-2*y^2/(M:ℝ)^2) := by
  have hbpos : (0:ℝ) < b := by exact_mod_cast hb
  have hM := G.M_ge_one
  set s := √(b:ℝ) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hbpos
  have hs2 : s*s = b := Real.mul_self_sqrt hbpos.le
  let t := p0 - y/s
  have ht1 : t < 1 := by
    have : 0 < y/s := div_pos hy hs
    dsimp [t]; linarith [hp.2]
  have hinc : ∀ ω, s * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0) ≤ -y →
      pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b ≤ t := by
    intro ω h
    have h1 : pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0 ≤ -y/s := by
      rw [le_div_iff₀ hs]; linarith
    rw [neg_div] at h1
    dsimp [t]; linarith
  by_cases ht0 : t < 0
  · have he : {ω | s * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0) ≤ -y} = ∅ := by
      ext ω
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro h
      linarith [hinc ω h, (G.coverage_mem_Icc p0 b ω).1]
    rw [he, measureReal_empty]
    exact (Real.exp_pos _).le
  · have ht0' : 0 ≤ t := not_lt.mp ht0
    let c := ∫ ω, sizedResidual G.F p0 t (G.Z 0 ω) ∂μ
    have hc : c ≤ -(y/s) := by
      have h1 := G.count_mean_le_closed t ⟨ht0', ht1⟩
      have h2 : c = (∫ ω, sizedCount G.F t (G.Z 0 ω) ∂μ) - p0 * G.meanSize := by
        dsimp [c]
        unfold sizedResidual
        rw [integral_sub (G.count_integrable G.F G.continuous.measurable t 0)
          ((G.size_integrable 0).const_mul p0), integral_const_mul]
        rfl
      have h3 : G.meanSize * t - p0 * G.meanSize = -(G.meanSize * (y/s)) := by dsimp [t]; ring
      have h4 : y/s ≤ G.meanSize * (y/s) :=
        le_mul_of_one_le_left (div_pos hy hs).le G.meanSize_ge_one
      linarith
    have hbc : (b:ℝ) * c ≤ -(s*y) := by
      have h1 : (b:ℝ) * c ≤ (b:ℝ) * (-(y/s)) := mul_le_mul_of_nonneg_left hc hbpos.le
      have h2 : (b:ℝ) * (-(y/s)) = -(s*y) := by
        rw [← hs2]; field_simp
      linarith
    have hε : 0 ≤ p0 + s*y := by nlinarith [hp.1]
    have hsub : {ω | s * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0) ≤ -y} ⊆
        {ω | p0 + s*y ≤ ∑ j ∈ Finset.range b, (sizedResidual G.F p0 t (G.Z j ω) - c)} := by
      intro ω h
      have h1 := (pooledCoverage_le_iff G.F G.monotone_F p0 hp (fun j ↦ G.Z j ω) b t ht1).mp
        (hinc ω h)
      change p0 + s*y ≤ ∑ j ∈ Finset.range b, (sizedResidual G.F p0 t (G.Z j ω) - c)
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      linarith
    apply (measureReal_mono hsub (measure_ne_top _ _)).trans
    apply (G.residual_sum_upper p0 hp t b (p0 + s*y) hε).trans
    apply Real.exp_le_exp.mpr
    have hsq : (b:ℝ)*y^2 ≤ (p0 + s*y)^2 := by
      have : (s*y)^2 = (b:ℝ)*y^2 := by rw [← hs2]; ring
      nlinarith [hp.1, mul_pos hs hy]
    have hMpos : (0:ℝ) < (M:ℝ)^2 := by positivity
    rw [div_le_div_iff₀ (by positivity) hMpos]
    nlinarith [mul_le_mul_of_nonneg_right hsq hMpos.le]

/-- Appendix B.11's second Hoeffding tail: the coverage error is rarely far above zero. -/
theorem coverage_upper_tail (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (b : ℕ) (hb : 1 ≤ b)
    (y : ℝ) (hy : 2 ≤ y) :
    μ.real {ω | y < √(b:ℝ) * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0)} ≤
      Real.exp (-y^2/(2*(M:ℝ)^2)) := by
  have hbpos : (0:ℝ) < b := by exact_mod_cast hb
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hM := G.M_ge_one
  have hy0 : 0 < y := by linarith
  set s := √(b:ℝ) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hbpos
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hb1
  have hs2 : s*s = b := Real.mul_self_sqrt hbpos.le
  let t := p0 + y/s
  have htp : p0 < t := by
    have : 0 < y/s := div_pos hy0 hs
    dsimp [t]; linarith
  have hinc : ∀ ω, y < s * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0) →
      t < pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b := by
    intro ω h
    have h1 : y/s < pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0 := by
      rw [div_lt_iff₀ hs]; linarith
    dsimp [t]; linarith
  by_cases ht1 : 1 ≤ t
  · have he : {ω | y < s * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0)} = ∅ := by
      ext ω
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro h
      linarith [hinc ω h, (G.coverage_mem_Icc p0 b ω).2]
    rw [he, measureReal_empty]
    exact (Real.exp_pos _).le
  · have ht1' : t < 1 := not_le.mp ht1
    have htI : t ∈ Ioo 0 1 := ⟨hp.1.trans htp, ht1'⟩
    let c := ∫ ω, sizedResidual G.F p0 t (G.Z 0 ω) ∂μ
    have hc : c = G.meanSize * (y/s) := by
      dsimp [c]
      rw [G.residual_mean p0 hp t htI]
      dsimp [t]; ring
    have hbc : s*y ≤ (b:ℝ) * c := by
      have h4 : y/s ≤ G.meanSize * (y/s) :=
        le_mul_of_one_le_left (div_pos hy0 hs).le G.meanSize_ge_one
      have h1 : (b:ℝ) * (y/s) ≤ (b:ℝ) * c := by
        rw [hc]; exact mul_le_mul_of_nonneg_left h4 hbpos.le
      have h2 : (b:ℝ) * (y/s) = s*y := by
        rw [← hs2]; field_simp
      linarith
    have hsy : 2 ≤ s*y := by nlinarith
    have hε : 0 ≤ s*y/2 := by positivity
    have hsub : {ω | y < s * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0)} ⊆
        {ω | s*y/2 ≤ ∑ j ∈ Finset.range b, (c - sizedResidual G.F p0 t (G.Z j ω))} := by
      intro ω h
      have h1 := hinc ω h
      have h2 : ¬ p0 ≤ ∑ j ∈ Finset.range b, sizedResidual G.F p0 t (G.Z j ω) := by
        intro hcon
        have := (pooledCoverage_le_iff G.F G.monotone_F p0 hp (fun j ↦ G.Z j ω) b t ht1').mpr hcon
        linarith
      change s*y/2 ≤ ∑ j ∈ Finset.range b, (c - sizedResidual G.F p0 t (G.Z j ω))
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      linarith [not_le.mp h2, hp.2]
    apply (measureReal_mono hsub (measure_ne_top _ _)).trans
    apply (G.residual_sum_lower p0 hp t b (s*y/2) hε).trans
    apply Real.exp_le_exp.mpr
    have hsq : (s*y/2)^2 = (b:ℝ)*y^2/4 := by rw [← hs2]; ring
    rw [hsq]
    apply le_of_eq
    have hMne : (M:ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- A sub-Gaussian tail for the normalized coverage error, uniform in the number of clusters. -/
theorem coverage_abs_tail (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (b : ℕ) (hb : 1 ≤ b)
    (y : ℝ) (hy : 0 < y) :
    μ.real {ω | y < |√(b:ℝ) * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0)|} ≤
      2*Real.exp (2/(M:ℝ)^2) * Real.exp (-(1/(2*(M:ℝ)^2))*y^2) := by
  have hM := G.M_ge_one
  have hMpos : (0:ℝ) < (M:ℝ)^2 := by positivity
  by_cases hy2 : y < 2
  · apply (measureReal_le_one).trans
    rw [mul_assoc, ← Real.exp_add]
    have : (0:ℝ) ≤ 2/(M:ℝ)^2 + -(1/(2*(M:ℝ)^2))*y^2 := by
      have h1 : 2/(M:ℝ)^2 + -(1/(2*(M:ℝ)^2))*y^2 = (4 - y^2)/(2*(M:ℝ)^2) := by
        field_simp; ring
      rw [h1]
      exact div_nonneg (by nlinarith) (by positivity)
    have := Real.one_le_exp this
    linarith
  · have hy2' : 2 ≤ y := not_lt.mp hy2
    have hsub : {ω | y < |√(b:ℝ) * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0)|} ⊆
        {ω | √(b:ℝ) * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0) ≤ -y} ∪
        {ω | y < √(b:ℝ) * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0)} := by
      intro ω h
      have h' : y < |√(b:ℝ) * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0)| := h
      rcases lt_abs.mp h' with h1 | h1
      · exact Or.inr h1
      · exact Or.inl (show √(b:ℝ) * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0) ≤ -y by linarith)
    have h1 := G.coverage_lower_tail p0 hp b hb y hy
    have h2 := G.coverage_upper_tail p0 hp b hb y hy2'
    have h3 : Real.exp (-2*y^2/(M:ℝ)^2) ≤ Real.exp (-y^2/(2*(M:ℝ)^2)) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_div_iff₀ hMpos (by positivity)]
      nlinarith [sq_nonneg y, mul_nonneg (sq_nonneg y) hMpos.le]
    have h4 : -(1/(2*(M:ℝ)^2))*y^2 = -y^2/(2*(M:ℝ)^2) := by ring
    have h5 : (1:ℝ) ≤ Real.exp (2/(M:ℝ)^2) := Real.one_le_exp (by positivity)
    have h6 := Real.exp_pos (-y^2/(2*(M:ℝ)^2))
    rw [h4]
    calc
      _ ≤ _ := (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)
      _ ≤ 2*Real.exp (-y^2/(2*(M:ℝ)^2)) := by linarith
      _ ≤ _ := by nlinarith

/-- The cluster-scale coverage error `√b (C - p₀)`. -/
noncomputable def normalizedError (p0 : ℝ) (b : ℕ) (ω : Ω) : ℝ :=
  √(b:ℝ) * (pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0)

lemma normalizedError_measurable (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (b : ℕ) :
    Measurable (G.normalizedError p0 b) :=
  ((G.coverage_measurable p0 hp b).sub_const _).const_mul _

lemma normalizedError_abs_le (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (b : ℕ) (ω : Ω) :
    |G.normalizedError p0 b ω| ≤ √(b:ℝ) := by
  have h := G.coverage_mem_Icc p0 b ω
  unfold normalizedError
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 : |pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b - p0| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hp.2, h.1], by linarith [hp.1, h.2]⟩
  calc
    _ ≤ √(b:ℝ) * 1 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = _ := mul_one _

lemma normalizedError_memLp (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (b : ℕ) :
    MemLp (G.normalizedError p0 b) 2 μ :=
  MemLp.of_bound (G.normalizedError_measurable p0 hp b).aestronglyMeasurable (√(b:ℝ))
    (Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs]; exact G.normalizedError_abs_le p0 hp b ω))

lemma normalizedError_cdf (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | G.normalizedError p0 (n+1) ω ≤ x}) atTop
      (nhds (cdf (gaussianReal 0 (G.residualVariance p0/G.meanSize^2).toNNReal) x)) :=
  (G.coverage_cdf p0 hp x (Or.inr hx)).comp (tendsto_add_atTop_nat 1)

lemma normalizedError_strict_cdf (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | G.normalizedError p0 (n+1) ω < x}) atTop
      (nhds (cdf (gaussianReal 0 (G.residualVariance p0/G.meanSize^2).toNNReal) x)) := by
  apply strict_cdf_limit (fun n ↦ G.normalizedError p0 (n+1)) _ x
    (centered_gaussian_cdf_continuousAt _ x (Or.inr hx))
  filter_upwards [isOpen_ne.mem_nhds hx] with u hu
  exact G.normalizedError_cdf p0 hp u hu

/-- The second moment of the normalized coverage error converges to `σ²/μ²`. -/
theorem second_moment_limit (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) :
    Tendsto (fun n : ℕ ↦ ∫ ω, (G.normalizedError p0 (n+1) ω)^2 ∂μ) atTop
      (nhds (G.residualVariance p0/G.meanSize^2)) := by
  have hM := G.M_ge_one
  let v : NNReal := (G.residualVariance p0/G.meanSize^2).toNNReal
  have hvc : (v:ℝ) = G.residualVariance p0/G.meanSize^2 :=
    Real.coe_toNNReal _ (div_nonneg (G.residualVariance_nonneg p0) (sq_nonneg _))
  let ν := gaussianReal 0 v
  let Z : ℕ → Ω → ℝ := fun n ↦ G.normalizedError p0 (n+1)
  have hz (n : ℕ) : Measurable (Z n) := G.normalizedError_measurable p0 hp (n+1)
  have ht (t : ℝ) (ht : 0 < t) : Tendsto (fun n ↦ μ.real {ω | t < (Z n ω)^2}) atTop
      (nhds (ν.real {z : ℝ | t < z^2})) := by
    have hsq := Real.sqrt_pos.mpr ht
    have ha : ν {z : ℝ | z = -Real.sqrt t} = 0 :=
      centered_gaussian_no_atom_at_continuity id v HasLaw.id _ (Or.inr hsq.ne')
    have hv := square_tail_cdf_identity (μ := ν) id measurable_id t ht ha
    simp only [id_eq] at hv
    have he (n : ℕ) := square_tail_split (μ := μ) (Z n) (hz n) t ht
    simp_rw [he]
    rw [hv]
    have e1 : ν.real {z : ℝ | z ≤ -Real.sqrt t} = cdf ν (-Real.sqrt t) := by
      rw [cdf_eq_real]; rfl
    have e2 : ν.real {z : ℝ | z ≤ Real.sqrt t} = cdf ν (Real.sqrt t) := by
      rw [cdf_eq_real]; rfl
    rw [e1, e2]
    exact (G.normalizedError_strict_cdf p0 hp _ (neg_ne_zero.mpr hsq.ne')).add
      (tendsto_const_nhds.sub (G.normalizedError_cdf p0 hp _ hsq.ne'))
  have hiW : Integrable (fun z : ℝ ↦ z^2) ν :=
    (memLp_id_gaussianReal' 2 (by norm_num)).integrable_sq
  have hcpos : (0:ℝ) < 1/(2*(M:ℝ)^2) := by positivity
  have hB : IntegrableOn (fun t : ℝ ↦ 2*Real.exp (2/(M:ℝ)^2) *
      Real.exp (-(1/(2*(M:ℝ)^2))*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hcpos) 0).const_mul _
  have hbound (n : ℕ) (t : ℝ) (ht : 0 < t) : μ.real {ω | t < (Z n ω)^2} ≤
      2*Real.exp (2/(M:ℝ)^2) * Real.exp (-(1/(2*(M:ℝ)^2))*t) := by
    have he : {ω | t < (Z n ω)^2} = {ω | Real.sqrt t < |Z n ω|} := by
      ext ω
      simp only [mem_setOf_eq]
      have hs := Real.sq_sqrt ht.le
      have hsn := Real.sqrt_nonneg t
      have ha := abs_nonneg (Z n ω)
      have hsq := sq_abs (Z n ω)
      constructor <;> (intro h; nlinarith)
    rw [he]
    have hh := G.coverage_abs_tail p0 hp (n+1) (by omega) (Real.sqrt t) (Real.sqrt_pos.mpr ht)
    rw [Real.sq_sqrt ht.le] at hh
    exact hh
  have hl := nonnegative_expectation_limit_of_tail_limit (ν := ν)
    (fun n ω ↦ (Z n ω)^2) (fun z : ℝ ↦ z^2)
    (fun n ↦ (G.normalizedError_memLp p0 hp (n+1)).integrable_sq) hiW
    (fun _ _ ↦ sq_nonneg _) (fun _ ↦ sq_nonneg _) _ hB hbound ht
  have hv : (∫ z : ℝ, z^2 ∂ν) = (v : ℝ) := by
    have hh := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
    rw [variance_eq_integral (X := fun z : ℝ ↦ z) (by fun_prop)] at hh
    simpa only [integral_id_gaussianReal, sub_zero] using hh
  rw [hv, hvc] at hl
  exact hl

/-- The normalized coverage error has vanishing mean. -/
theorem mean_limit (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) :
    Tendsto (fun n : ℕ ↦ ∫ ω, G.normalizedError p0 (n+1) ω ∂μ) atTop (nhds 0) := by
  have hM := G.M_ge_one
  let v : NNReal := (G.residualVariance p0/G.meanSize^2).toNNReal
  let ν := gaussianReal 0 v
  let Z : ℕ → Ω → ℝ := fun n ↦ G.normalizedError p0 (n+1)
  have hz (n : ℕ) : Measurable (Z n) := G.normalizedError_measurable p0 hp (n+1)
  have hp' (t : ℝ) (ht : 0 < t) : Tendsto (fun n ↦ μ.real {ω | t < Z n ω}) atTop
      (nhds (ν.real {z : ℝ | t < z})) := by
    have he (n : ℕ) := probability_gt_eq_one_sub_le (μ := μ) (Z n) (hz n) t
    simp_rw [he]
    rw [probability_gt_eq_one_sub_le (μ := ν) (fun z : ℝ ↦ z) (by fun_prop) t]
    have e : ν.real {z : ℝ | z ≤ t} = cdf ν t := by rw [cdf_eq_real]; rfl
    rw [e]
    exact tendsto_const_nhds.sub (G.normalizedError_cdf p0 hp t ht.ne')
  have hn' (t : ℝ) (ht : 0 < t) : Tendsto (fun n ↦ μ.real {ω | t < -Z n ω}) atTop
      (nhds (ν.real {z : ℝ | t < -z})) := by
    have he (n : ℕ) : μ.real {ω | t < -Z n ω} = μ.real {ω | Z n ω < -t} := by
      have hh : {ω | t < -Z n ω} = {ω | Z n ω < -t} := by
        ext ω; simp only [mem_setOf_eq]; constructor <;> intro h <;> linarith
      rw [hh]
    have hv : ν.real {z : ℝ | t < -z} = cdf ν (-t) := by
      have hh : {z : ℝ | t < -z} = {z : ℝ | z < -t} := by
        ext z; simp only [mem_setOf_eq]; constructor <;> intro h <;> linarith
      have h5 := probability_lt_eq_le (μ := ν) id (-t)
        (centered_gaussian_no_atom_at_continuity id v HasLaw.id t (Or.inr ht.ne'))
      simp only [id_eq] at h5
      rw [hh, h5, cdf_eq_real]
      rfl
    simp_rw [he]
    rw [hv]
    exact G.normalizedError_strict_cdf p0 hp _ (neg_ne_zero.mpr ht.ne')
  have hcpos : (0:ℝ) < 1/(2*(M:ℝ)^2) := by positivity
  have hB : IntegrableOn (fun t : ℝ ↦ 2*Real.exp (2/(M:ℝ)^2) *
      Real.exp (-(1/(2*(M:ℝ)^2))*t^2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq hcpos).integrableOn.const_mul _
  have hb (n : ℕ) (t : ℝ) (ht : 0 < t) : μ.real {ω | t < |Z n ω|} ≤
      2*Real.exp (2/(M:ℝ)^2) * Real.exp (-(1/(2*(M:ℝ)^2))*t^2) :=
    G.coverage_abs_tail p0 hp (n+1) (by omega) t ht
  have hl := expectation_limit_of_two_tail_limits (ν := ν) Z id hz measurable_id
    (fun n ↦ (G.normalizedError_memLp p0 hp (n+1)).integrable (by norm_num))
    ((memLp_id_gaussianReal' 2 (by norm_num)).integrable (by norm_num)) _ hB hb hp' hn'
  simpa only [id_eq, ν, integral_id_gaussianReal] using hl

/-- Proposition 3, cluster scale: `b Var(C) → σ²/μ²` for the actual pooled cutoff. -/
theorem coverage_variance_limit (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) :
    Tendsto (fun b : ℕ ↦ (b:ℝ) * Var[fun ω ↦ pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b; μ])
      atTop (nhds (G.residualVariance p0/G.meanSize^2)) := by
  have ht := (G.second_moment_limit p0 hp).sub ((G.mean_limit p0 hp).pow 2)
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), sub_zero] at ht
  have he (n : ℕ) : (∫ ω, (G.normalizedError p0 (n+1) ω)^2 ∂μ) -
      (∫ ω, G.normalizedError p0 (n+1) ω ∂μ)^2 =
      ((n+1 : ℕ) : ℝ) * Var[fun ω ↦ pooledCoverage G.F p0 (fun j ↦ G.Z j ω) (n+1); μ] := by
    have hv := variance_eq_sub (G.normalizedError_memLp p0 hp (n+1))
    simp only [Pi.pow_apply] at hv
    rw [← hv]
    unfold normalizedError
    rw [variance_const_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
    congr 1
    exact variance_sub_const (G.coverage_measurable p0 hp (n+1)).aestronglyMeasurable _
  simp_rw [he] at ht
  exact (tendsto_add_atTop_iff_nat 1).mp ht

/-- The expected sample size is `E[n] = b μ`. -/
lemma pooledSize_mean (b : ℕ) :
    (∫ ω, (pooledSize (fun j ↦ G.Z j ω) b : ℝ) ∂μ) = b * G.meanSize := by
  simp_rw [pooledSize_cast]
  rw [integral_finsetSum _ (fun j _ ↦ G.size_integrable j)]
  have h (j : ℕ) : (∫ ω, ((G.Z j ω).1 : ℝ) ∂μ) = G.meanSize :=
    (G.identDistrib_comp (fun z ↦ (z.1 : ℝ)) (measurable_from_nat.comp measurable_fst)
      (fun _ ↦ rfl) j).integral_eq
  simp only [h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Proposition 3, second conclusion: `E[n] Var(C) → v(p₀) = σ²/μ`. -/
theorem expected_size_variance_limit (p0 : ℝ) (hp : p0 ∈ Ioo 0 1) :
    Tendsto (fun b : ℕ ↦ (∫ ω, (pooledSize (fun j ↦ G.Z j ω) b : ℝ) ∂μ) *
      Var[fun ω ↦ pooledCoverage G.F p0 (fun j ↦ G.Z j ω) b; μ])
      atTop (nhds (G.residualVariance p0/G.meanSize)) := by
  have hm := G.meanSize_pos.ne'
  have hh := (G.coverage_variance_limit p0 hp).const_mul G.meanSize
  have e : G.meanSize * (G.residualVariance p0/G.meanSize^2) =
      G.residualVariance p0/G.meanSize := by field_simp
  rw [e] at hh
  apply hh.congr
  intro b
  rw [G.pooledSize_mean b]
  ring

end RandomSizeModel
end Exceedance

#print axioms Exceedance.RandomSizeModel.coverage_measurable
#print axioms Exceedance.RandomSizeModel.coverage_lower_tail
#print axioms Exceedance.RandomSizeModel.coverage_upper_tail
#print axioms Exceedance.RandomSizeModel.coverage_abs_tail
#print axioms Exceedance.RandomSizeModel.second_moment_limit
#print axioms Exceedance.RandomSizeModel.mean_limit
#print axioms Exceedance.RandomSizeModel.coverage_variance_limit
#print axioms Exceedance.RandomSizeModel.expected_size_variance_limit
