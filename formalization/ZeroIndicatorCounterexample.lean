import ReflectionMixture

open MeasureTheory ProbabilityTheory Set
namespace Exceedance

/-- The maximum of the actual two-member sample has the pair's diagonal CDF, including ties. -/
lemma pair_max_quantile_event (z : ℝ × ℝ) (p : ℝ) :
    sampleQuantile ![z.1,z.2] (1 : Fin 2) ≤ p ↔ z.1 ≤ p ∧ z.2 ≤ p := by
  classical
  rw [sampleQuantile_le_iff]
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,Fin.val_one]
  split_ifs <;> simp_all

/-- Zero indicator correlation at one level does not force the exact independent-sample Beta law. -/
theorem zero_indicator_correlation_not_beta :
    Nat.ceil (((2:ℝ)+1)*(2/3)) = 2 ∧
    ((reflectionMixture (1/3)).real {z | z.1 ≤ 2/3 ∧ z.2 ≤ 2/3}-(2/3)^2)/
      ((2/3)*(1-2/3)) = 0 ∧
    (reflectionMixture (1/3)).map (fun z ↦ sampleQuantile ![z.1,z.2] (1 : Fin 2)) ≠ betaMeasure 2 1 := by
  refine ⟨by norm_num,?_⟩
  have hc := (reflectionMixture_correlations (1/3) (by exact_mod_cast (show (1:ℝ)/3≤1 by norm_num)) (2/3)
    (by constructor <;> norm_num)).2
  constructor
  · convert hc using 1 <;> norm_num
  · intro he
    have hm : Measurable (fun z : ℝ × ℝ ↦ sampleQuantile ![z.1,z.2] (1 : Fin 2)) :=
      measurable_sampleQuantile _ (by intro i; fin_cases i <;> fun_prop) _
    have hprob := congrArg (fun ν : Measure ℝ ↦ ν.real (Iic (1/2))) he
    rw [map_measureReal_apply hm measurableSet_Iic] at hprob
    have hevent : (fun z : ℝ × ℝ ↦ sampleQuantile ![z.1,z.2] (1 : Fin 2)) ⁻¹' Iic (1/2) =
        {z | z.1 ≤ 1/2 ∧ z.2 ≤ 1/2} := by
      ext z; exact pair_max_quantile_event z (1/2)
    rw [hevent,reflectionMixture_diagonal (1/3) (by exact_mod_cast (show (1:ℝ)/3≤1 by norm_num)) (1/2) (by constructor <;> norm_num)] at hprob
    have hb := beta_order_cdf_interior 2 1 (by norm_num) (1/2) (by constructor <;> norm_num)
    norm_num [binomialSurvivalPolynomial,Finset.sum_range_succ,bernsteinPolynomial] at hb
    norm_num [hb] at hprob

end Exceedance
#print axioms Exceedance.zero_indicator_correlation_not_beta
