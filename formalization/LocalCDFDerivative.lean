import ScoreCountLocal
import Mathlib.Analysis.Calculus.Deriv.Slope

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance

lemma sqrt_succ_inv_tendsto :
    Tendsto (fun n : ℕ ↦ (Real.sqrt ((n+1:ℕ):ℝ))⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))

/-- Differentiability supplies the deterministic mean of a local empirical count. -/
theorem local_cdf_derivative (F : ℝ → ℝ) (q f c : ℝ) (hf : HasDerivAt F f q) :
    Tendsto (fun n : ℕ ↦ Real.sqrt ((n+1:ℕ):ℝ)*
      (F (q+c/Real.sqrt ((n+1:ℕ):ℝ))-F q)) atTop (nhds (f*c)) := by
  classical
  let G := Function.update (fun x ↦ (F x-F q)/(x-q)) q f
  have ht : Tendsto (fun n : ℕ ↦ q+c/Real.sqrt ((n+1:ℕ):ℝ)) atTop (nhds q) := by
    simpa only [div_eq_mul_inv,mul_zero,add_zero] using
      (sqrt_succ_inv_tendsto.const_mul c).const_add q
  have hh := (hf.continuousAt_div.tendsto.comp ht).mul_const c
  simp only [Function.update_self,Function.comp_apply] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  have hs : 0 < Real.sqrt ((n+1:ℕ):ℝ) := Real.sqrt_pos.mpr (by positivity)
  by_cases hc : c=0
  · simp [hc]
  · have hne : q+c/Real.sqrt ((n+1:ℕ):ℝ) ≠ q := by
      intro he
      have : c/Real.sqrt ((n+1:ℕ):ℝ)=0 := by linarith
      exact hc ((div_eq_zero_iff).mp this |>.resolve_right hs.ne')
    dsimp only
    rw [Function.update_of_ne hne]
    simp only [add_sub_cancel_left]
    field_simp

end Exceedance
#print axioms Exceedance.local_cdf_derivative
