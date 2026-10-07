import BetaMoments
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

noncomputable def binomialSurvivalPolynomial (n k : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (k+1), bernsteinPolynomial ℝ n i

lemma binomialSurvivalPolynomial_derivative (n k : ℕ) :
    (binomialSurvivalPolynomial n k).derivative =
      -(n : Polynomial ℝ)*bernsteinPolynomial ℝ (n-1) k := by
  induction k with
  | zero => simp [binomialSurvivalPolynomial, bernsteinPolynomial.derivative_zero]
  | succ k ih =>
    have he : binomialSurvivalPolynomial n (k+1) =
        binomialSurvivalPolynomial n k + bernsteinPolynomial ℝ n (k+1) := by
      exact Finset.sum_range_succ _ _
    rw [he, Polynomial.derivative_add, ih, bernsteinPolynomial.derivative_succ]
    ring

lemma binomialSurvivalPolynomial_zero (n k : ℕ) :
    (binomialSurvivalPolynomial n k).eval 0 = 1 := by
  simp [binomialSurvivalPolynomial, Polynomial.eval_finsetSum, bernsteinPolynomial.eval_at_0]

lemma binomialSurvivalPolynomial_eval (n k : ℕ) (p : ℝ) :
    (binomialSurvivalPolynomial n k).eval p =
      ∑ i ∈ Finset.range (k+1), (n.choose i : ℝ)*p^i*(1-p)^(n-i) := by
  simp [binomialSurvivalPolynomial, bernsteinPolynomial, Polynomial.eval_finsetSum]

/-- The integer-shape Beta density equals the appropriate Bernstein basis polynomial. -/
lemma beta_order_density (n k : ℕ) (hk : k < n) (x : ℝ) (hx : x ∈ Ioo 0 1) :
    betaPDFReal (k+1) (n-k) x = (n : ℝ)*(bernsteinPolynomial ℝ (n-1) k).eval x := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk
  have he : (n-k : ℕ) = (n-1-k)+1 := by omega
  have he1 : (k:ℝ)+1+((n:ℝ)-k) = (n:ℝ)+1 := by ring
  have he2 : (n:ℝ)-(k:ℝ) = ((n-1-k : ℕ):ℝ)+1 := by
    rw [← Nat.cast_sub hk.le, he, Nat.cast_add, Nat.cast_one]
  have hfac : ((n-1).choose k : ℝ)*(k.factorial : ℝ)*((n-1-k).factorial : ℝ) = ((n-1).factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (show k ≤ n-1 by omega)
  have hnfac : (n.factorial : ℝ) = (n:ℝ)*((n-1).factorial : ℝ) := by
    have hh := Nat.factorial_succ (n-1)
    rw [Nat.sub_add_cancel hn] at hh
    exact_mod_cast hh
  have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnf : ((n-1-k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-1-k)
  rw [betaPDFReal, if_pos (show 0 < x ∧ x < 1 from hx), beta, he1, Real.Gamma_nat_eq_factorial,
    Real.Gamma_nat_eq_factorial, he2, Real.Gamma_nat_eq_factorial]
  simp only [add_sub_cancel_right, Real.rpow_natCast, bernsteinPolynomial,
    Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one]
  rw [hnfac]
  field_simp
  rw [← hfac]
  ring


lemma beta_measure_real_apply (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (betaMeasure a b).real s = ∫ x in s, betaPDFReal a b x := by
  rw [measureReal_def, betaMeasure, withDensity_apply _ hs]
  symm
  exact integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (betaPDFReal_nonneg a b ha hb))
    (measurable_betaPDFReal a b).aestronglyMeasurable

/-- The integer-shape Beta CDF is the exact complementary binomial sum. -/
theorem beta_order_cdf_interior (n k : ℕ) (hk : k < n) (p : ℝ) (hp : p ∈ Ioo 0 1) :
    (betaMeasure (k+1) (n-k)).real (Iic p) = 1-(binomialSurvivalPolynomial n k).eval p := by
  have ha : 0 < (k:ℝ)+1 := by positivity
  have hb : 0 < (n:ℝ)-k := sub_pos.mpr (by exact_mod_cast hk)
  rw [beta_measure_real_apply _ _ ha hb _ measurableSet_Iic]
  have hrestrict : (∫ x in Iic p, betaPDFReal (k+1) (n-k) x) =
      ∫ x in Ioc 0 p, betaPDFReal (k+1) (n-k) x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic Ioc_subset_Iic_self
    intro x hx
    have hx0 : x ≤ 0 := by
      by_contra hh
      exact hx.2 ⟨lt_of_not_ge hh,hx.1⟩
    simp [betaPDFReal, not_lt.mpr hx0]
  rw [hrestrict]
  have he : (∫ x in Ioc 0 p, betaPDFReal (k+1) (n-k) x) =
      ∫ x in Ioc 0 p, (n:ℝ)*(bernsteinPolynomial ℝ (n-1) k).eval x := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    exact beta_order_density n k hk x ⟨hx.1,hx.2.trans_lt hp.2⟩
  rw [he, ← intervalIntegral.integral_of_le hp.1.le]
  have hd (x : ℝ) : HasDerivAt (fun x ↦ -(binomialSurvivalPolynomial n k).eval x)
      ((n:ℝ)*(bernsteinPolynomial ℝ (n-1) k).eval x) x := by
    convert ((binomialSurvivalPolynomial n k).hasDerivAt x).neg using 1 <;> try rfl
    all_goals simp [binomialSurvivalPolynomial_derivative]

  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hd x)
    ((continuous_const.mul (Polynomial.continuous _)).intervalIntegrable _ _),
    binomialSurvivalPolynomial_zero]
  ring

end Exceedance
#print axioms Exceedance.beta_order_density

#print axioms Exceedance.beta_order_cdf_interior
