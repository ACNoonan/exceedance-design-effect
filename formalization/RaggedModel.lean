import RaggedCoverage
import EstimatorConsistency
import BoundedArrayCLT

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The mean pair correlation, rather than equality of all pair correlations, determines count variance. -/
theorem thresholdCount_variance_mean_pair {m : ℕ} (U : Ω → Fin m → ℝ)
    (hU : Measurable U) (t rho : ℝ)
    (hmarg : ∀ i, μ.real {ω | U ω i ≤ t} = t)
    (hpairs : (∑ i : Fin m, ∑ j ∈ Finset.univ.erase i,
      cov[indicator {ω | U ω i ≤ t}, indicator {ω | U ω j ≤ t}; μ]) =
      (m:ℝ)*((m:ℝ)-1)*(t*(1-t)*rho)) :
    Var[fun ω ↦ thresholdCount t (U ω); μ] = (m:ℝ)*t*(1-t)*(1+((m:ℝ)-1)*rho) := by
  classical
  let A := fun i ↦ {ω | U ω i ≤ t}
  have hA (i : Fin m) : MeasurableSet (A i) := measurableSet_le ((measurable_pi_apply i).comp hU) measurable_const
  rw [thresholdCount_comp, variance_fun_sum (fun i ↦ indicator_memLp (hA i))]
  have he (i : Fin m) : (∑ j, cov[indicator (A i), indicator (A j); μ]) =
      t*(1-t) + ∑ j ∈ Finset.univ.erase i, cov[indicator (A i), indicator (A j); μ] := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), covariance_self (indicator_memLp (hA i)).aemeasurable,
      indicator_variance (hA i), hmarg i]
  change (∑ i, ∑ j, cov[indicator (A i), indicator (A j); μ]) = _
  simp_rw [he, Finset.sum_add_distrib]
  rw [hpairs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- R1–R4 on the uniform scale. The covariance sum is the definition of the common mean pair correlation. -/
structure RaggedUniformModel (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  b : ℕ → ℕ
  m : (n : ℕ) → Fin (b n) → ℕ
  U : (n : ℕ) → (j : Fin (b n)) → Ω → Fin (m n j) → ℝ
  measurable : ∀ n j, Measurable (U n j)
  independent : ∀ n, iIndepFun (U n) μ
  uniform : ∀ n j i t, 0 ≤ t → t ≤ 1 → μ.real {ω | U n j ω i ≤ t} = t
  nonempty : ∀ n, 0 < b n
  positive_size : ∀ n j, 0 < m n j
  M : ℝ
  M_pos : 0 < M
  size_le : ∀ n j, (m n j : ℝ) ≤ M
  grows : Tendsto b atTop atTop
  rho : ℝ → ℝ
  mean_pair : ∀ n j t, t ∈ Icc 0 1 →
    (∑ i : Fin (m n j), ∑ l ∈ Finset.univ.erase i,
      cov[indicator {ω | U n j ω i ≤ t}, indicator {ω | U n j ω l ≤ t}; μ]) =
      (m n j : ℝ)*((m n j : ℝ)-1)*(t*(1-t)*rho t)
  sizeLimit : ℝ
  sizeLimit_tendsto : Tendsto (fun n ↦ (∑ j, (m n j : ℝ)^2)/(raggedSize (m n) : ℝ))
    atTop (nhds sizeLimit)

namespace RaggedUniformModel
variable (G : RaggedUniformModel Ω μ)

noncomputable def N (n : ℕ) : ℕ := raggedSize (G.m n)
noncomputable def sizeBiased (n : ℕ) : ℝ := (∑ j, (G.m n j : ℝ)^2)/(G.N n : ℝ)
noncomputable def varianceLimit (p : ℝ) : ℝ := p*(1-p)*(1+(G.sizeLimit-1)*G.rho p)

lemma b_le_N (n : ℕ) : G.b n ≤ G.N n := by
  rw [N, raggedSize_eq_sum]
  calc
    _ = ∑ _j : Fin (G.b n), 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun j _ ↦ G.positive_size n j)

lemma N_pos (n : ℕ) : 0 < G.N n := (G.nonempty n).trans_le (G.b_le_N n)
lemma N_grows : Tendsto G.N atTop atTop := tendsto_atTop_mono G.b_le_N G.grows

lemma count_variance (n : ℕ) (j : Fin (G.b n)) (t : ℝ) (ht : t ∈ Icc 0 1) :
    Var[fun ω ↦ thresholdCount t (G.U n j ω); μ] =
      (G.m n j : ℝ)*t*(1-t)*(1+((G.m n j : ℝ)-1)*G.rho t) :=
  thresholdCount_variance_mean_pair _ (G.measurable n j) t (G.rho t)
    (fun i ↦ G.uniform n j i t ht.1 ht.2) (G.mean_pair n j t ht)

/-- Appendix B.5 for actual independent unequal clusters, with mean pair correlations. -/
theorem normalized_variance_sum (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    (∑ j, Var[fun ω ↦ thresholdCount t (G.U n j ω); μ])/(G.N n : ℝ) =
      t*(1-t)*(1+(G.sizeBiased n-1)*G.rho t) := by
  simp_rw [G.count_variance n _ t ht]
  have hn : (G.N n : ℝ) ≠ 0 := by exact_mod_cast (G.N_pos n).ne'
  have hsum : (∑ j, (G.m n j : ℝ)) = G.N n := by simp [N, raggedSize_eq_sum]
  have he (j : Fin (G.b n)) : (G.m n j : ℝ)*t*(1-t)*(1+((G.m n j : ℝ)-1)*G.rho t) =
      (G.m n j : ℝ)*(t*(1-t)*(1-G.rho t)) + (G.m n j : ℝ)^2*(t*(1-t)*G.rho t) := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hsum]
  dsimp [sizeBiased]
  field_simp
  <;> ring

lemma count_variance_continuousAt (n : ℕ) (j : Fin (G.b n)) (p : ℝ) :
    ContinuousAt (fun t ↦ Var[fun ω ↦ thresholdCount t (G.U n j ω); μ]) p := by
  have ha (i : Fin (G.m n j)) : μ {ω | G.U n j ω i = p} = 0 :=
    uniform_marginal_no_atoms _ ((measurable_pi_apply i).comp (G.measurable n j)) (G.uniform n j i) p
  have hf := thresholdCount_moment_continuousAt (G.U n j) (G.measurable n j) p ha 1
  have hs := thresholdCount_moment_continuousAt (G.U n j) (G.measurable n j) p ha 2
  simp only [pow_one] at hf
  have hh := hs.sub (hf.pow 2)
  convert hh using 1
  ext t
  exact variance_eq_sub (thresholdCount_memLp _ (G.measurable n j) t)

/-- R3 forces continuity of the common correlation whenever a nonsingleton cluster exists. -/
lemma rho_continuousAt (p : ℝ) (hp : p ∈ Ioo 0 1)
    (hpair : ∃ n j, 1 < G.m n j) : ContinuousAt G.rho p := by
  obtain ⟨n,j,hj⟩ := hpair
  let a : ℝ := G.m n j
  have ha : 1 < a := by dsimp [a]; exact_mod_cast hj
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hp0 : 0 < p := hp.1
  have hp1 : 0 < 1-p := sub_pos.mpr hp.2
  have hc := (((G.count_variance_continuousAt n j p).div
    ((continuousAt_const.mul continuousAt_id).mul (continuousAt_const.sub continuousAt_id))
    (show a*p*(1-p) ≠ 0 by positivity)).sub (show ContinuousAt (fun _ : ℝ ↦ (1:ℝ)) p from continuousAt_const)).div_const (a-1)
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hp.1 hp.2] with t ht
  have hct := G.count_variance n j t ⟨ht.1.le, ht.2.le⟩
  change G.rho t = (Var[fun ω ↦ thresholdCount t (G.U n j ω); μ]/(a*t*(1-t))-1)/(a-1)
  rw [hct]
  change G.rho t = (a*t*(1-t)*(1+(a-1)*G.rho t)/(a*t*(1-t))-1)/(a-1)
  have h0 : a*t*(1-t) ≠ 0 := mul_ne_zero (mul_ne_zero ha0.ne' ht.1.ne') (sub_pos.mpr ht.2).ne'
  have h1 : a-1 ≠ 0 := ne_of_gt (by linarith)
  field_simp [ha0.ne', ht.1.ne', (sub_pos.mpr ht.2).ne', h1]
  <;> ring

lemma variance_sum_limit (p : ℝ) (hp : p ∈ Ioo 0 1) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ Icc 0 1) (htp : Tendsto t atTop (nhds p)) :
    Tendsto (fun n ↦ (∑ j, Var[fun ω ↦ thresholdCount (t n) (G.U n j ω); μ])/(G.N n : ℝ))
      atTop (nhds (G.varianceLimit p)) := by
  simp_rw [G.normalized_variance_sum _ _ (ht _)]
  by_cases hpair : ∃ n j, 1 < G.m n j
  · have hr := (G.rho_continuousAt p hp hpair).tendsto.comp htp
    exact (htp.mul (tendsto_const_nhds.sub htp)).mul
      (tendsto_const_nhds.add ((G.sizeLimit_tendsto.sub_const 1).mul hr))
  · have hm (n : ℕ) (j : Fin (G.b n)) : G.m n j = 1 := by
      have hn : ¬1 < G.m n j := fun h ↦ hpair ⟨n,j,h⟩
      have hh := G.positive_size n j
      omega
    have hb (n : ℕ) : G.sizeBiased n = 1 := by
      have hbn : (G.b n : ℝ) ≠ 0 := by exact_mod_cast (G.nonempty n).ne'
      simp [sizeBiased, N, raggedSize_eq_sum, hm, hbn]
    have hl : G.sizeLimit = 1 := tendsto_nhds_unique G.sizeLimit_tendsto
      (show Tendsto G.sizeBiased atTop (nhds 1) by
        have he : G.sizeBiased = (fun _ : ℕ ↦ (1:ℝ)) := funext hb
        rw [he]
        exact tendsto_const_nhds)
    simp only [hb, hl, varianceLimit, sub_self, zero_mul, add_zero, mul_one]
    exact htp.mul (tendsto_const_nhds.sub htp)

lemma varianceLimit_nonneg (p : ℝ) (hp : p ∈ Ioo 0 1) : 0 ≤ G.varianceLimit p := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (G.variance_sum_limit p hp (fun _ ↦ p) (fun _ ↦ ⟨hp.1.le,hp.2.le⟩) tendsto_const_nhds)
  filter_upwards with n
  exact div_nonneg (Finset.sum_nonneg (fun j _ ↦ variance_nonneg _ _)) (Nat.cast_nonneg _)

/-- The actual unequal-size moving count has the R1–R4 Gaussian limit. -/
theorem moving_count_clt (p : ℝ) (hp : p ∈ Ioo 0 1) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ Icc 0 1) (htp : Tendsto t atTop (nhds p)) :
    TendstoInDistribution
      (fun n ω ↦ ((∑ j, thresholdCount (t n) (G.U n j ω))-(G.N n : ℝ)*t n)/Real.sqrt (G.N n))
      atTop (id : ℝ → ℝ) (fun _ ↦ μ) (gaussianReal 0 (G.varianceLimit p).toNNReal) := by
  let A := fun n j ω ↦ thresholdCount (t n) (G.U n j ω)-(G.m n j : ℝ)*t n
  have hA (n : ℕ) (j : Fin (G.b n)) : Measurable (A n j) :=
    ((measurable_thresholdCount (t n)).comp (G.measurable n j)).sub_const _
  have hmean (n : ℕ) (j : Fin (G.b n)) : (∫ ω, A n j ω ∂μ) = 0 := by
    rw [show A n j = (fun ω ↦ thresholdCount (t n) (G.U n j ω)-(G.m n j : ℝ)*t n) from rfl,
      integral_sub ((thresholdCount_memLp _ (G.measurable n j) (t n)).integrable (by norm_num)) (integrable_const _)]
    · rw [thresholdCount_mean _ (G.measurable n j) (t n)
        (fun i ↦ G.uniform n j i (t n) (ht n).1 (ht n).2)]
      simp
  have hb (n : ℕ) (j : Fin (G.b n)) : ∀ᵐ ω ∂μ, |A n j ω| ≤ G.M := by
    filter_upwards with ω
    have hh := thresholdCount_bounds (G.U n j ω) (t n)
    simp only [Fintype.card_fin] at hh
    have hmt0 : 0 ≤ (G.m n j : ℝ)*t n := mul_nonneg (Nat.cast_nonneg _) (ht n).1
    have hmt1 : (G.m n j : ℝ)*t n ≤ G.m n j := by nlinarith [(ht n).2, Nat.cast_nonneg (α := ℝ) (G.m n j)]
    apply (abs_le.mpr ⟨?_, ?_⟩ : |A n j ω| ≤ (G.m n j : ℝ)).trans (G.size_le n j)
    all_goals dsimp [A]; linarith [hh.1,hh.2]
  have hv : Tendsto (fun n ↦ (∑ j, Var[A n j; μ])/(G.N n : ℝ)) atTop
      (nhds ((G.varianceLimit p).toNNReal : ℝ)) := by
    rw [Real.coe_toNNReal _ (G.varianceLimit_nonneg p hp)]
    convert G.variance_sum_limit p hp t ht htp using 1
    ext n
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact variance_sub_const ((measurable_thresholdCount (t n)).comp (G.measurable n j)).aestronglyMeasurable _
  have hh := bounded_array_sqrt_clt G.b A hA
    (fun n ↦ (G.independent n).comp
      (fun j u ↦ thresholdCount (t n) u-(G.m n j : ℝ)*t n)
      (fun j ↦ (measurable_thresholdCount (t n)).sub_const _)) hmean G.M G.M_pos.le hb
    (fun n ↦ (G.N n : ℝ)) (fun n ↦ by exact_mod_cast G.N_pos n)
    (fun n ↦ by exact_mod_cast G.b_le_N n)
    (tendsto_natCast_atTop_atTop.comp G.N_grows) _ hv
  have he (n : ℕ) (ω : Ω) : (∑ j, A n j ω) =
      (∑ j, thresholdCount (t n) (G.U n j ω))-(G.N n : ℝ)*t n := by
    simp only [A, Finset.sum_sub_distrib, ← Finset.sum_mul, N, raggedSize_eq_sum, Nat.cast_sum]
  simpa only [he] using hh

/-- Interior target levels permit arbitrary finite initial moving thresholds. -/
theorem moving_count_interior_clt (p : ℝ) (hp : p ∈ Ioo 0 1) (t : ℕ → ℝ)
    (htp : Tendsto t atTop (nhds p)) :
    TendstoInDistribution
      (fun n ω ↦ ((∑ j, thresholdCount (t n) (G.U n j ω))-(G.N n : ℝ)*t n)/Real.sqrt (G.N n))
      atTop (id : ℝ → ℝ) (fun _ ↦ μ) (gaussianReal 0 (G.varianceLimit p).toNNReal) := by
  let t' := fun n ↦ if t n ∈ Icc 0 1 then t n else p
  have he : ∀ᶠ n in atTop, t' n = t n := by
    filter_upwards [htp.eventually (Ioo_mem_nhds hp.1 hp.2)] with n hn
    exact if_pos ⟨hn.1.le,hn.2.le⟩
  have ht' (n : ℕ) : t' n ∈ Icc 0 1 := by
    dsimp [t']; split_ifs with hn
    · exact hn
    · exact ⟨hp.1.le,hp.2.le⟩
  have hh := G.moving_count_clt p hp t' ht' (htp.congr' (he.mono (fun _ h ↦ h.symm)))
  apply distribution_limit_eventually_eq _ _ _ hh
  · intro n
    exact (((Finset.measurable_sum _ (fun j _ ↦ (measurable_thresholdCount (t n)).comp (G.measurable n j))).sub_const _).div_const _).aemeasurable
  · filter_upwards [he] with n hn
    rw [hn]

end RaggedUniformModel
end Exceedance
#print axioms Exceedance.thresholdCount_variance_mean_pair
#print axioms Exceedance.RaggedUniformModel.normalized_variance_sum
#print axioms Exceedance.RaggedUniformModel.rho_continuousAt

#print axioms Exceedance.RaggedUniformModel.moving_count_interior_clt
