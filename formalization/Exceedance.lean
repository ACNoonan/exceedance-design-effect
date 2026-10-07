import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/- Exact identities supporting the paper. No asymptotic probability theorem is claimed here. -/
open MeasureTheory ProbabilityTheory
namespace Exceedance

theorem design_effect_algebra (m v ρ : ℝ) :
    m * v + m * (m - 1) * (ρ * v) = m * v * (1 + (m - 1) * ρ) := by ring

theorem indicator_covariance (p δ : ℝ) (hp : p * (1 - p) ≠ 0) :
    p * (1 - p) * ((δ - p ^ 2) / (p * (1 - p))) = δ - p ^ 2 := by
  exact mul_div_cancel₀ (δ - p ^ 2) hp

theorem tail_rate_identity (p δ : ℝ) (hp : p ≠ 0) (h1 : 1 - p ≠ 0) :
    (δ / p ^ 2 - 1) / (1 - p) = ((δ - p ^ 2) / (p * (1 - p))) / p := by
  field_simp

theorem drift_sign (p ρ d : ℝ) :
    0 < (1 / 2 : ℝ) * ((1 - 2 * p) * ρ + p * (1 - p) * d) ↔
    (2 * p - 1) * ρ < p * (1 - p) * d := by constructor <;> intro h <;> linarith

theorem positive_derivative_negative_drift :
    (0 : ℝ) < 50 / 81 ∧
    (1 / 2 : ℝ) * ((1 - 2 * (9 / 10)) * (4 / 9) +
      (9 / 10) * (1 - 9 / 10) * (50 / 81)) = -3 / 20 := by norm_num

/-- Arithmetic for b=10h duplicated-pair clusters, once the order-statistic expectation
    E[C]=(18h+1)/(20h+1) has been established separately. -/
theorem duplicated_pair_scaled_drift (h : ℝ) (hh : 0 < h) :
    (10 * h) * ((18 * h + 1) / (20 * h + 1) - (36 * h + 1) / (40 * h + 1)) =
    20 * h ^ 2 / ((20 * h + 1) * (40 * h + 1)) := by
  have h20 : 20 * h + 1 ≠ 0 := ne_of_gt (by linarith)
  have h40 : 40 * h + 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

theorem duplicated_pair_drift_positive (h : ℝ) (hh : 0 < h) :
    0 < (10 * h) * ((18 * h + 1) / (20 * h + 1) - (36 * h + 1) / (40 * h + 1)) := by
  rw [duplicated_pair_scaled_drift h hh]
  positivity

/-- This links the algebra to Mathlib's actual variance and covariance operators.
    Covariance row sums are assumed, not estimated or proved from sampling assumptions. -/
theorem variance_from_covariance_rows
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (v ρ : ℝ)
    (hrows : ∀ i, ∑ j, cov[X i, X j; μ] = v * (1 + ((Fintype.card ι : ℝ) - 1) * ρ)) :
    Var[fun ω ↦ ∑ i, X i ω; μ] =
      (Fintype.card ι : ℝ) * v * (1 + ((Fintype.card ι : ℝ) - 1) * ρ) := by
  rw [variance_fun_sum hX]
  simp_rw [hrows]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end Exceedance

#print axioms Exceedance.variance_from_covariance_rows
#print axioms Exceedance.duplicated_pair_drift_positive
