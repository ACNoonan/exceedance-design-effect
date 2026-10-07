import ClusterCoverage

open Filter Set
namespace Exceedance

/-- The finite-profile identity uses population variance, with divisor b. -/
theorem size_biased_mean_cv {b : ℕ} (hb : 0 < b) (m : Fin b → ℝ)
    (hs : 0 < ∑ j, m j) :
    (∑ j, (m j)^2)/(∑ j, m j) =
      ((∑ j, m j)/(b : ℝ)) *
        (1 + ((∑ j, (m j-(∑ l, m l)/(b : ℝ))^2)/(b : ℝ)) /
          (((∑ j, m j)/(b : ℝ))^2)) := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hm : (∑ j, m j)/(b : ℝ) ≠ 0 := div_ne_zero hs.ne' hb'
  have he : (∑ j, (m j-(∑ l, m l)/(b : ℝ))^2) =
      (∑ j, (m j)^2)-2*((∑ l, m l)/(b : ℝ))*(∑ j, m j)+
        (b : ℝ)*((∑ l, m l)/(b : ℝ))^2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  field_simp
  <;> ring

/-- At fixed cluster count, the effective-size expression has the stated ceiling. -/
theorem effective_size_fixed_cluster_bound (b m rho : ℝ)
    (hb : 0 ≤ b) (hm : 0 < m) (hr : 0 < rho) (hr1 : rho ≤ 1) :
    b*m/(1+(m-1)*rho) ≤ b/rho := by
  have hd : 0 < 1+(m-1)*rho := by nlinarith
  apply (div_le_div_iff₀ hd hr).mpr
  nlinarith

/-- Ceiling ranks differ from the target by at most one divided by n+1. -/
theorem ceil_rank_level_error (N : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    |(Nat.ceil (((N : ℝ)+1)*p) : ℝ)/((N : ℝ)+1)-p| ≤ 1/((N : ℝ)+1) := by
  have hden : 0 < (N : ℝ)+1 := by positivity
  have hl := Nat.le_ceil (((N : ℝ)+1)*p)
  have hu := Nat.ceil_lt_add_one (show 0 ≤ ((N : ℝ)+1)*p by positivity)
  rw [abs_of_nonneg (by apply sub_nonneg.mpr; apply (le_div_iff₀ hden).mpr; nlinarith)]
  apply (le_div_iff₀ hden).mpr
  have he : (((Nat.ceil (((N : ℝ)+1)*p) : ℝ)/((N : ℝ)+1))-p)*((N : ℝ)+1) =
      (Nat.ceil (((N : ℝ)+1)*p) : ℝ)-p*((N : ℝ)+1) := by field_simp
  rw [he]
  nlinarith

/-- The ceiling correction vanishes even after multiplication by square root n. -/
theorem ceil_rank_sqrt_centering (N r : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (p : ℝ) (hp : 0 ≤ p)
    (hr : ∀ᶠ n in atTop, r n = Nat.ceil (((N n : ℝ)+1)*p)) :
    Tendsto (fun n ↦ Real.sqrt (N n)*|(r n : ℝ)/((N n : ℝ)+1)-p|) atTop (nhds 0) := by
  have hi : Tendsto (fun n ↦ (Real.sqrt (N n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hi
  · exact Eventually.of_forall (fun n ↦ by positivity)
  · filter_upwards [hr, (tendsto_atTop.1 hN) 1] with n hn hn1
    rw [hn]
    have hn0 : (0:ℝ) < N n := by exact_mod_cast hn1
    have hs := Real.sqrt_pos.mpr hn0
    calc
      _ ≤ Real.sqrt (N n)*(1/((N n : ℝ)+1)) :=
        mul_le_mul_of_nonneg_left (ceil_rank_level_error (N n) p hp) hs.le
      _ ≤ (Real.sqrt (N n : ℝ))⁻¹ := by
        rw [mul_one_div, inv_eq_one_div]
        apply (div_le_div_iff₀ (by positivity) hs).mpr
        nlinarith [Real.sq_sqrt hn0.le]


/-- Enlarging existing clusters has diminishing algebraic returns at fixed positive correlation. -/
theorem effective_size_diminishing_returns (b m rho : ℝ)
    (hb : 0 ≤ b) (hm : 1 ≤ m) (hr : 0 < rho) (hr1 : rho ≤ 1) :
    b*(m+2)/(1+(m+1)*rho)-b*(m+1)/(1+m*rho) ≤
      b*(m+1)/(1+m*rho)-b*m/(1+(m-1)*rho) := by
  have h0 : 0 < 1+(m-1)*rho := by nlinarith
  have h1 : 0 < 1+m*rho := by nlinarith
  have h2 : 0 < 1+(m+1)*rho := by nlinarith
  have h0' : 1+m*rho-rho ≠ 0 := by nlinarith [h0]
  have e0 : b*(m+1)/(1+m*rho)-b*m/(1+(m-1)*rho) =
      b*(1-rho)/((1+(m-1)*rho)*(1+m*rho)) := by
    field_simp [h0.ne',h1.ne',h2.ne',h0']
    ring_nf
    field_simp
    <;> ring
  have e1 : b*(m+2)/(1+(m+1)*rho)-b*(m+1)/(1+m*rho) =
      b*(1-rho)/((1+m*rho)*(1+(m+1)*rho)) := by field_simp [h0.ne',h1.ne',h2.ne',h0']; ring
  rw [e0,e1]
  apply div_le_div_of_nonneg_left (mul_nonneg hb (sub_nonneg.mpr hr1)) (mul_pos h0 h1)
  nlinarith [mul_pos h1 hr]

/-- A nonconstant size profile cannot reduce the size-biased mean below the ordinary mean. -/
theorem size_biased_mean_ge_mean {b : ℕ} (hb : 0 < b) (m : Fin b → ℝ) (hs : 0 < ∑ j, m j) :
    (∑ j, m j)/(b:ℝ) ≤ (∑ j, (m j)^2)/(∑ j, m j) := by
  rw [size_biased_mean_cv hb m hs]
  have hmean : 0 < (∑ j, m j)/(b:ℝ) := div_pos hs (by exact_mod_cast hb)
  have hcv : 0 ≤ ((∑ j, (m j-(∑ l, m l)/(b:ℝ))^2)/(b:ℝ))/(((∑ j, m j)/(b:ℝ))^2) := by positivity
  nlinarith

/-- The direction of the design-effect comparison depends on the sign of the correlation. -/
theorem size_biased_design_effect_comparison {b : ℕ} (hb : 0 < b) (m : Fin b → ℝ)
    (hs : 0 < ∑ j, m j) (rho : ℝ) :
    (0 ≤ rho → 1+((∑ j, m j)/(b:ℝ)-1)*rho ≤ 1+((∑ j, (m j)^2)/(∑ j, m j)-1)*rho) ∧
    (rho ≤ 0 → 1+((∑ j, (m j)^2)/(∑ j, m j)-1)*rho ≤ 1+((∑ j, m j)/(b:ℝ)-1)*rho) := by
  have hh := size_biased_mean_ge_mean hb m hs
  constructor <;> intro h <;> nlinarith

end Exceedance
#print axioms Exceedance.size_biased_mean_cv
#print axioms Exceedance.effective_size_fixed_cluster_bound
#print axioms Exceedance.ceil_rank_sqrt_centering

#print axioms Exceedance.effective_size_diminishing_returns
#print axioms Exceedance.size_biased_design_effect_comparison
