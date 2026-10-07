import Exceedance

open Filter Set
namespace Exceedance

/-- Indicator correlation tends to the lower tail coefficient, when that coefficient exists. -/
theorem indicator_correlation_lower_tail (δ : ℝ → ℝ) (ell : ℝ)
    (h : Tendsto (fun p ↦ δ p / p) (nhdsWithin 0 (Ioo 0 1)) (nhds ell)) :
    Tendsto (fun p ↦ (δ p - p^2)/(p*(1-p)))
      (nhdsWithin 0 (Ioo 0 1)) (nhds ell) := by
  have hp : Tendsto (fun p : ℝ ↦ p) (nhdsWithin 0 (Ioo 0 1)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hh := (h.sub hp).div (tendsto_const_nhds.sub hp) (by norm_num : (1:ℝ)-0 ≠ 0)
  simp only [sub_zero, div_one] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  have h0 : p ≠ 0 := ne_of_gt hp.1
  have h1 : 1-p ≠ 0 := ne_of_gt (sub_pos.mpr hp.2)
  simp only [Pi.div_apply]
  field_simp

/-- Indicator correlation tends to the upper tail coefficient, when that coefficient exists. -/
theorem indicator_correlation_upper_tail (δ : ℝ → ℝ) (ell : ℝ)
    (h : Tendsto (fun p ↦ (1-2*p+δ p)/(1-p))
      (nhdsWithin 1 (Ioo 0 1)) (nhds ell)) :
    Tendsto (fun p ↦ (δ p - p^2)/(p*(1-p)))
      (nhdsWithin 1 (Ioo 0 1)) (nhds ell) := by
  have hp : Tendsto (fun p : ℝ ↦ p) (nhdsWithin 1 (Ioo 0 1)) (nhds 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hh := (h.sub ((tendsto_const_nhds (x := (1:ℝ))).sub hp)).div hp (by norm_num : (1:ℝ) ≠ 0)
  simp only [sub_self, sub_zero, div_one] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  have h0 : p ≠ 0 := ne_of_gt hp.1
  have h1 : 1-p ≠ 0 := ne_of_gt (sub_pos.mpr hp.2)
  simp only [Pi.div_apply]
  field_simp
  all_goals ring

end Exceedance
#print axioms Exceedance.indicator_correlation_lower_tail
#print axioms Exceedance.indicator_correlation_upper_tail
