import LocalCDFDerivative
import EstimatorConsistency

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Bahadur's representation for the actual pooled score quantile.
Only independent fixed-size clusters, a common CDF, and a positive derivative at the target are needed.
The rank hypothesis is deterministic and includes the prescribed ceiling rank. -/
theorem independent_cluster_bahadur {m : ℕ} (hm : 0 < m)
    (S : ℕ → Ω → Fin m → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (F : ℝ → ℝ) (hF : Monotone F)
    (hmarg : ∀ j i t, μ.real {ω | S j ω i ≤ t} = F t)
    (q f : ℝ) (hf : 0 < f) (hder : HasDerivAt F f q)
    (k : (n : ℕ) → Fin ((n+1)*m))
    (hrank : Tendsto (fun n ↦ (((k n).val+1:ℕ)-(n+1:ℝ)*m*F q)/
      Real.sqrt ((n+1:ℕ):ℝ)) atTop (nhds 0)) :
    TendstoInMeasure μ (fun n ω ↦
      Real.sqrt ((n+1:ℕ):ℝ)*(sampleQuantile (pooledSample S (n+1) ω) (k n)-q)+
        (normalizedCount S (n+1) q ω-Real.sqrt ((n+1:ℕ):ℝ)*m*F q)/(m*f))
      atTop (fun _ ↦ 0) := by
  classical
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hmf : 0 < (m:ℝ)*f := mul_pos hm' hf
  let a := fun n ↦ (((k n).val+1:ℕ)-(n+1:ℝ)*m*F q)/Real.sqrt ((n+1:ℕ):ℝ)
  let T := fun n t ↦ q+(t/((m:ℝ)*f))/Real.sqrt ((n+1:ℕ):ℝ)
  let A := fun n t ω ↦ normalizedCount S (n+1) (T n t) ω-normalizedCount S (n+1) q ω
  let Z := fun n ω ↦ (m:ℝ)*f*Real.sqrt ((n+1:ℕ):ℝ)*
    (sampleQuantile (pooledSample S (n+1) ω) (k n)-q)
  let B := fun n ω ↦ (((k n).val+1:ℕ):ℝ)/Real.sqrt ((n+1:ℕ):ℝ)-normalizedCount S (n+1) q ω
  have hs n : 0 < Real.sqrt ((n+1:ℕ):ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hsq n : (Real.sqrt ((n+1:ℕ):ℝ))^2=(n+1:ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using Real.sq_sqrt (show (0:ℝ)≤((n+1:ℕ):ℝ) by positivity)
  have hinvmean n : (Real.sqrt ((n+1:ℕ):ℝ))⁻¹*(n+1:ℝ)=Real.sqrt ((n+1:ℕ):ℝ) := by
    calc
      _ = (Real.sqrt ((n+1:ℕ):ℝ))⁻¹*(Real.sqrt ((n+1:ℕ):ℝ))^2 := congrArg _ (hsq n).symm
      _ = _ := by field_simp
  have hmean n : (∫ ω, normalizedCount S (n+1) q ω ∂μ) =
      Real.sqrt ((n+1:ℕ):ℝ)*m*F q := by
    rw [normalizedCount_cdf_mean S hS (n+1) q F (fun j i ↦ hmarg j i q)]
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one]
    have hh := hinvmean n
    simp only [Nat.cast_add,Nat.cast_one] at hh
    rw [hh]
  have htightB : ProbabilityTight B μ := by
    have hh := probabilityTight_neg_add _ a
      (bounded_variance_probability_tight (fun n ↦ normalizedCount S (n+1) q)
        (fun n ↦ normalizedCount_memLp S hS (n+1) q) ((m:ℝ)^2) (sq_nonneg _)
        (fun n ↦ by simpa using normalizedCount_variance_bound S hS hindep (n+1) q)) hrank
    have he : (fun n ω ↦ a n-(normalizedCount S (n+1) q ω-
        ∫ x, normalizedCount S (n+1) q x ∂μ)) = B := by
      funext n ω
      rw [hmean]
      dsimp [a,B]
      rw [← hsq n]
      field_simp
      <;> ring
    rwa [he] at hh
  have hmono : ∀ n ω, Monotone (fun t ↦ A n t ω) := by
    intro n ω t u htu
    apply sub_le_sub_right
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hs n).le)
    apply Finset.sum_le_sum
    intro j _
    apply thresholdCount_monotone
    dsimp [T]
    exact add_le_add_right (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right htu hmf.le) (hs n).le) q
  have hA : ∀ t, TendstoInMeasure μ (fun n ω ↦ A n t ω) atTop (fun _ ↦ t) := by
    intro t
    have ht : Tendsto (fun n ↦ T n t) atTop (nhds q) := by
      simpa only [T,div_eq_mul_inv,mul_zero,add_zero] using
        (sqrt_succ_inv_tendsto.const_mul (t/((m:ℝ)*f))).const_add q
    have hlocal := local_score_count_centered S hS hindep F hF hmarg q hder.continuousAt
      (fun n ↦ T n t) ht
    let d := fun n ↦ Real.sqrt ((n+1:ℕ):ℝ)*m*(F (T n t)-F q)
    have hd : Tendsto d atTop (nhds t) := by
      have hh := (local_cdf_derivative F q f (t/((m:ℝ)*f)) hder).const_mul (m:ℝ)
      have he : (m:ℝ)*(f*(t/((m:ℝ)*f)))=t := by field_simp
      rw [he] at hh
      convert hh using 1
      funext n; dsimp [d,T]; ring
    have hlocal' : TendstoInMeasure μ (fun n ω ↦ A n t ω-d n) atTop (fun _ ↦ 0) := by
      convert hlocal using 1
      funext n ω
      dsimp [A,d]
      simp only [Fintype.card_fin]
      rw [hinvmean]
    have hh := continuous_pair_tendstoInMeasure _ _ 0 t hlocal'
      (deterministic_tendstoInMeasure d t hd) (fun v ↦ v.1+v.2) (by fun_prop)
    simpa only [sub_add_cancel,zero_add] using hh
  have hinv : ∀ n ω t, Z n ω ≤ t ↔ B n ω ≤ A n t ω := by
    intro n ω t
    have hq : Z n ω ≤ t ↔ sampleQuantile (pooledSample S (n+1) ω) (k n) ≤ T n t := by
      dsimp [Z,T]
      have he : ((m:ℝ)*f*Real.sqrt ((n+1:ℕ):ℝ))*
          ((t/((m:ℝ)*f))/Real.sqrt ((n+1:ℕ):ℝ))=t := by
        field_simp
      constructor <;> intro hh <;> nlinarith [mul_pos hmf (hs n)]
    have hc := sampleQuantile_le_iff (pooledSample S (n+1) ω) (k n) (T n t)
    rw [hq,hc]
    have hcast : (k n).val+1 ≤ (Finset.univ.filter (fun i ↦ pooledSample S (n+1) ω i ≤ T n t)).card ↔
        (((k n).val+1:ℕ):ℝ) ≤ ((Finset.univ.filter (fun i ↦ pooledSample S (n+1) ω i ≤ T n t)).card:ℝ) := by
      exact_mod_cast Iff.rfl
    rw [hcast,pooledSample_count]
    dsimp [B,A,normalizedCount]
    rw [sub_le_sub_iff_right]
    rw [div_eq_mul_inv,mul_comm _ (Real.sqrt ((n+1:ℕ):ℝ))⁻¹,
      mul_le_mul_iff_right₀ (inv_pos.mpr (hs n))]
  have hlin := stochastic_inverse_linearization A Z B hmono hA hinv
    (inverse_probability_tight A Z B hA hinv htightB)
  have hh := continuous_pair_tendstoInMeasure _ _ 0 0 hlin
    (deterministic_tendstoInMeasure a 0 hrank) (fun v ↦ (v.1+v.2)/((m:ℝ)*f))
    (by fun_prop)
  simp only [zero_add,zero_div] at hh
  convert hh using 1
  funext n ω
  dsimp [Z,B,a]
  rw [← hsq n]
  field_simp
  <;> ring


lemma ceil_rank_count_centering (m : ℕ) (p : ℝ) (hp : p ∈ Ioo 0 1)
    (r : ℕ → ℕ)
    (hr : ∀ᶠ n in atTop, r n=Nat.ceil (((((n+1)*m:ℕ):ℝ)+1)*p)) :
    Tendsto (fun n ↦ ((r n:ℝ)-(n+1:ℝ)*m*p)/Real.sqrt ((n+1:ℕ):ℝ)) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun n : ℕ ↦ 2*(Real.sqrt ((n+1:ℕ):ℝ))⁻¹) atTop (nhds 0) by
      simpa using sqrt_succ_inv_tendsto.const_mul 2)
  · filter_upwards [hr] with n hn
    rw [hn]
    apply div_nonneg _ (Real.sqrt_nonneg _)
    have hl := Nat.le_ceil (((((n+1)*m:ℕ):ℝ)+1)*p)
    push_cast at hl ⊢
    nlinarith [hp.1]
  · filter_upwards [hr] with n hn
    rw [hn,← div_eq_mul_inv]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have hu := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (((((n+1)*m:ℕ):ℝ)+1)*p) from
      mul_nonneg (by positivity) hp.1.le)
    push_cast at hu ⊢
    nlinarith [hp.2]

/-- The paper's ceiling-rank Bahadur formula, with the total sample size and empirical CDF explicit. -/
theorem independent_cluster_ceil_bahadur {m : ℕ} (hm : 0 < m)
    (S : ℕ → Ω → Fin m → ℝ) (hS : ∀ j, Measurable (S j))
    (hindep : iIndepFun S μ) (F : ℝ → ℝ) (hF : Monotone F)
    (hmarg : ∀ j i t, μ.real {ω | S j ω i ≤ t} = F t)
    (q f : ℝ) (hf : 0 < f) (hder : HasDerivAt F f q) (hp : F q ∈ Ioo 0 1)
    (k : (n : ℕ) → Fin ((n+1)*m))
    (hceil : ∀ᶠ n in atTop, (k n).val+1=Nat.ceil (((((n+1)*m:ℕ):ℝ)+1)*F q)) :
    TendstoInMeasure μ (fun n ω ↦ Real.sqrt (((n+1)*m:ℕ):ℝ)*
      (sampleQuantile (pooledSample S (n+1) ω) (k n)-q+
        (((Finset.univ.filter (fun i ↦ pooledSample S (n+1) ω i ≤ q)).card:ℝ)/
          (((n+1)*m:ℕ):ℝ)-F q)/f)) atTop (fun _ ↦ 0) := by
  classical
  have hh := independent_cluster_bahadur hm S hS hindep F hF hmarg q f hf hder k
    (ceil_rank_count_centering m (F q) hp (fun n ↦ (k n).val+1) hceil)
  have hmul := continuous_pair_tendstoInMeasure _ _ 0 0 hh hh
    (fun v ↦ Real.sqrt (m:ℝ)*v.1) (by fun_prop)
  simp only [mul_zero] at hmul
  convert hmul using 1
  funext n ω
  rw [pooledSample_count]
  dsimp [normalizedCount]
  have hm' : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have hn' : ((n+1:ℕ):ℝ)≠0 := by positivity
  have hs : Real.sqrt ((n+1:ℕ):ℝ)≠0 := by positivity
  rw [Nat.cast_mul,Real.sqrt_mul (by positivity : (0:ℝ)≤((n+1:ℕ):ℝ))]
  field_simp
  rw [Real.sq_sqrt (show (0:ℝ)≤((n+1:ℕ):ℝ) by positivity)]
  <;> ring

end Exceedance
#print axioms Exceedance.independent_cluster_bahadur

#print axioms Exceedance.independent_cluster_ceil_bahadur
