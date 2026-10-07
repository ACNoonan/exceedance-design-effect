import RandomCutoff

open MeasureTheory ProbabilityTheory Filter Set
namespace Exceedance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Asymptotic tightness in a form suited to probability bounds. -/
def ProbabilityTight (Z : ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ e > 0, ∃ R > 0, ∀ᶠ n in atTop, μ.real {ω | R ≤ |Z n ω|} < e

/-- Monotone processes converging to the identity converge uniformly on each fixed compact interval. -/
theorem monotone_process_uniform_in_probability
    (A : ℕ → ℝ → Ω → ℝ) (hmono : ∀ n ω, Monotone (fun t ↦ A n t ω))
    (hA : ∀ t, TendstoInMeasure μ (fun n ω ↦ A n t ω) atTop (fun _ ↦ t))
    (l u e : ℝ) (he : 0 < e) :
    Tendsto (fun n ↦ μ.real {ω | ∃ t ∈ Icc l u, e ≤ |A n t ω-t|}) atTop (nhds 0) := by
  classical
  obtain ⟨S,hS⟩ := isCompact_Icc.elim_finite_subcover
    (fun s : ℝ ↦ Ioo (s-e/4) (s+e/4)) (fun _ ↦ isOpen_Ioo)
    (show Icc l u ⊆ ⋃ s : ℝ, Ioo (s-e/4) (s+e/4) from fun t _ ↦
      mem_iUnion.mpr ⟨t,by constructor <;> linarith⟩)
  let E := fun n s ↦ {ω | e/4 ≤ |A n (s-e/4) ω-(s-e/4)|} ∪
    {ω | e/4 ≤ |A n (s+e/4) ω-(s+e/4)|}
  have hlim : Tendsto (fun n ↦ ∑ s ∈ S,
      (μ.real {ω | e/4 ≤ |A n (s-e/4) ω-(s-e/4)|}+
       μ.real {ω | e/4 ≤ |A n (s+e/4) ω-(s+e/4)|})) atTop (nhds 0) := by
    have hh := tendsto_finsetSum S (fun s _ ↦
      ((tendstoInMeasure_iff_measureReal_norm.mp (hA (s-e/4))) (e/4) (by positivity)).add
      ((tendstoInMeasure_iff_measureReal_norm.mp (hA (s+e/4))) (e/4) (by positivity)))
    simpa only [Real.norm_eq_abs,zero_add,Finset.sum_const_zero] using hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
  · intro n; exact measureReal_nonneg
  · intro n
    have hsub : {ω | ∃ t ∈ Icc l u, e ≤ |A n t ω-t|} ⊆ ⋃ s ∈ S, E n s := by
      rintro ω ⟨t,ht,hbad⟩
      obtain ⟨s,hs'⟩ := mem_iUnion.mp (hS ht)
      obtain ⟨hs,hst⟩ := mem_iUnion.mp hs'
      refine mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨hs,?_⟩⟩
      by_contra hn
      simp only [E,mem_union,mem_setOf_eq,not_or,not_le] at hn
      have hl := hmono n ω hst.1.le
      have hu := hmono n ω hst.2.le
      have h1 := abs_lt.mp hn.1
      have h2 := abs_lt.mp hn.2
      have hh : |A n t ω-t| < e := abs_lt.mpr ⟨by linarith [hst.2],by linarith [hst.1]⟩
      exact (not_le_of_gt hh) hbad
    apply (measureReal_mono (μ := μ) hsub (measure_ne_top _ _)).trans
    apply (measureReal_biUnion_finset_le S (E n)).trans
    apply Finset.sum_le_sum
    intro s _
    exact measureReal_union_le _ _

/-- Exact count inversion and a tight quantile imply stochastic linearization.
This is the probability argument behind the Bahadur representation. -/
theorem stochastic_inverse_linearization
    (A : ℕ → ℝ → Ω → ℝ) (Z B : ℕ → Ω → ℝ)
    (hmono : ∀ n ω, Monotone (fun t ↦ A n t ω))
    (hA : ∀ t, TendstoInMeasure μ (fun n ω ↦ A n t ω) atTop (fun _ ↦ t))
    (hinv : ∀ n ω t, Z n ω ≤ t ↔ B n ω ≤ A n t ω)
    (htight : ProbabilityTight Z μ) :
    TendstoInMeasure μ (fun n ω ↦ Z n ω-B n ω) atTop (fun _ ↦ 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro e he
  simp only [sub_zero,Real.norm_eq_abs]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n ↦ ha.trans_le measureReal_nonneg)
  · intro d hd
    obtain ⟨R,hR,hTail⟩ := htight (d/2) (by positivity)
    have hUnif := monotone_process_uniform_in_probability A hmono hA (-R-e) (R+e) (e/4) (by positivity)
    filter_upwards [hTail,hUnif.eventually_lt_const (by linarith : (0:ℝ) < d/2)] with n hn hu
    have hsub : {ω | e ≤ |Z n ω-B n ω|} ⊆ {ω | R ≤ |Z n ω|} ∪
        {ω | ∃ t ∈ Icc (-R-e) (R+e), e/4 ≤ |A n t ω-t|} := by
      intro ω hω
      by_contra hnot
      simp only [mem_union,mem_setOf_eq,not_or,not_le,not_exists,not_and] at hnot
      have hz := abs_lt.mp hnot.1
      have hlow : Z n ω-e/2 ∈ Icc (-R-e) (R+e) := ⟨by linarith [hz.1],by linarith [hz.2]⟩
      have hupp : Z n ω+e/2 ∈ Icc (-R-e) (R+e) := ⟨by linarith [hz.1],by linarith [hz.2]⟩
      have hl := abs_lt.mp (hnot.2 _ hlow)
      have hu := abs_lt.mp (hnot.2 _ hupp)
      have hb1 : A n (Z n ω-e/2) ω < B n ω := by
        apply lt_of_not_ge
        intro hh
        have hh' := (hinv n ω _).mpr hh
        linarith
      have hb2 : B n ω ≤ A n (Z n ω+e/2) ω := (hinv n ω _).mp (by linarith)
      have hh : |Z n ω-B n ω| < e := abs_lt.mpr ⟨by linarith,by linarith⟩
      exact (not_le_of_gt hh) hω
    have hh := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
    linarith


/-- Exact inversion transfers tightness from the count fluctuation to the quantile. -/
theorem inverse_probability_tight
    (A : ℕ → ℝ → Ω → ℝ) (Z B : ℕ → Ω → ℝ)
    (hA : ∀ t, TendstoInMeasure μ (fun n ω ↦ A n t ω) atTop (fun _ ↦ t))
    (hinv : ∀ n ω t, Z n ω ≤ t ↔ B n ω ≤ A n t ω)
    (hB : ProbabilityTight B μ) : ProbabilityTight Z μ := by
  intro e he
  obtain ⟨R,hR,hTail⟩ := hB (e/3) (by positivity)
  refine ⟨2*R+1,by positivity,?_⟩
  have hl := (tendstoInMeasure_iff_measureReal_norm.mp (hA (-2*R))) R hR
  have hu := (tendstoInMeasure_iff_measureReal_norm.mp (hA (2*R))) R hR
  filter_upwards [hTail,hl.eventually_lt_const (by positivity : (0:ℝ)<e/3),
    hu.eventually_lt_const (by positivity : (0:ℝ)<e/3)] with n hn hln hun
  have hsub : {ω | 2*R+1 ≤ |Z n ω|} ⊆
      ({ω | R ≤ |B n ω|} ∪ {ω | R ≤ ‖A n (-2*R) ω-(-2*R)‖}) ∪
        {ω | R ≤ ‖A n (2*R) ω-2*R‖} := by
    intro ω hω
    by_contra hnot
    simp only [mem_union,mem_setOf_eq,not_or,not_le,Real.norm_eq_abs] at hnot
    have hb := abs_lt.mp hnot.1.1
    have hl' := abs_lt.mp hnot.1.2
    have hu' := abs_lt.mp hnot.2
    have hz1 : ¬ Z n ω ≤ -2*R := by
      rw [hinv]; linarith [hb.1,hl'.2]
    have hz2 : Z n ω ≤ 2*R := (hinv n ω _).mpr (by linarith [hb.2,hu'.1])
    have hh : |Z n ω| < 2*R+1 := abs_lt.mpr ⟨by linarith,by linarith⟩
    exact (not_le_of_gt hh) hω
  have hh := (measureReal_mono (μ := μ) hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))
  linarith

/-- A uniform variance bound gives tightness of centered random variables. -/
theorem bounded_variance_probability_tight (X : ℕ → Ω → ℝ)
    (hX : ∀ n, MemLp (X n) 2 μ) (K : ℝ) (hK : 0 ≤ K)
    (hv : ∀ n, Var[X n; μ] ≤ K) :
    ProbabilityTight (fun n ω ↦ X n ω-∫ x, X n x ∂μ) μ := by
  intro e he
  have ht : Tendsto (fun R : ℝ ↦ K/R^2) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  obtain ⟨R,hR,hRe⟩ := (eventually_gt_atTop (0:ℝ)).and
    (ht.eventually_lt_const he) |>.exists
  refine ⟨R,hR,Eventually.of_forall (fun n ↦ ?_)⟩
  have hh := meas_ge_le_variance_div_sq (hX n) hR
  have hh' := ENNReal.toReal_mono (by finiteness) hh
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg R))] at hh'
  exact (hh'.trans (div_le_div_of_nonneg_right (hv n) (sq_nonneg R))).trans_lt hRe


lemma deterministic_tendstoInMeasure (a : ℕ → ℝ) (c : ℝ) (ha : Tendsto a atTop (nhds c)) :
    TendstoInMeasure μ (fun n _ ↦ a n) atTop (fun _ ↦ c) :=
  tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
    (Eventually.of_forall (fun _ ↦ ha))

lemma probabilityTight_neg_add (X : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (hX : ProbabilityTight X μ) (ha : Tendsto a atTop (nhds 0)) :
    ProbabilityTight (fun n ω ↦ a n-X n ω) μ := by
  intro e he
  obtain ⟨R,hR,hn⟩ := hX e he
  refine ⟨R+1,by positivity,?_⟩
  filter_upwards [hn,ha.abs.eventually_lt_const (by norm_num : |(0:ℝ)|<1)] with n hn ha
  apply lt_of_le_of_lt (measureReal_mono (μ := μ) ?_) hn
  intro ω hω
  change R ≤ |X n ω|
  change R+1 ≤ |a n-X n ω| at hω
  have hh := abs_sub (a n) (X n ω)
  linarith

end Exceedance
#print axioms Exceedance.stochastic_inverse_linearization
