import LectureNotes.Foundations

set_option autoImplicit false

/-! Analytic estimates used in the sharp empirical-CDF deviation bound. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- Bernoulli relative entropy, with the endpoint convention supplied by
`x * log x = 0` at zero. The reference probability is used in `(0,1)`. -/
def bernoulliDivergence (p q : ℝ) : ℝ :=
  p * Real.log p + (1 - p) * Real.log (1 - p) -
    p * Real.log q - (1 - p) * Real.log (1 - q)

theorem bernoulliDivergence_self (p : ℝ) : bernoulliDivergence p p = 0 := by
  unfold bernoulliDivergence
  ring

theorem continuous_bernoulliDivergence_left (q : ℝ) :
    Continuous (fun p => bernoulliDivergence p q) := by
  unfold bernoulliDivergence
  exact ((Real.continuous_mul_log.add
    (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))).sub
    (continuous_id.mul continuous_const)).sub ((continuous_const.sub continuous_id).mul continuous_const)

private theorem bernoulliDivergence_quadratic_deriv (p : ℝ) {q : ℝ} (hq : q ∈ Ioo 0 1) :
    HasDerivAt (fun r => bernoulliDivergence p r - 2 * (p - r) ^ 2)
      ((q - p) * (1 / (q * (1 - q)) - 4)) q := by
  have hq0 : q ≠ 0 := hq.1.ne'
  have hq1 : 1 - q ≠ 0 := (sub_pos.mpr hq.2).ne'
  have hl := ((hasDerivAt_id q).log hq0).const_mul p
  have hr := (((hasDerivAt_const q (1 : ℝ)).sub (hasDerivAt_id q)).log hq1).const_mul (1 - p)
  have hs := (((hasDerivAt_const q p).sub (hasDerivAt_id q)).pow 2).const_mul 2
  have h := (((hasDerivAt_const q
    (p * Real.log p + (1 - p) * Real.log (1 - p))).sub hl).sub hr).sub hs
  convert! h using 1
  dsimp only [id_eq, Pi.sub_apply]
  field_simp
  ring

private theorem bernoulli_curvature_bound {q : ℝ} (hq : q ∈ Ioo 0 1) :
    0 ≤ 1 / (q * (1 - q)) - 4 := by
  have hd : 0 < q * (1 - q) := mul_pos hq.1 (sub_pos.mpr hq.2)
  have hh : 4 ≤ 1 / (q * (1 - q)) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg (2 * q - 1)]
  linarith

/-- Pinsker's sharp quadratic constant for two Bernoulli laws, first with
both parameters in the open unit interval. -/
theorem bernoulliDivergence_pinsker_interior {p q : ℝ}
    (hp : p ∈ Ioo 0 1) (hq : q ∈ Ioo 0 1) :
    2 * (p - q) ^ 2 ≤ bernoulliDivergence p q := by
  let f (r : ℝ) := bernoulliDivergence p r - 2 * (p - r) ^ 2
  have hfp : f p = 0 := by simp [f, bernoulliDivergence_self]
  by_cases hpq : p ≤ q
  · have hi {r : ℝ} (hr : r ∈ Icc p q) : r ∈ Ioo 0 1 :=
      ⟨hp.1.trans_le hr.1, hr.2.trans_lt hq.2⟩
    have hm : MonotoneOn f (Icc p q) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc p q)
        (fun r hr => (bernoulliDivergence_quadratic_deriv p (hi hr)).continuousAt.continuousWithinAt)
        (fun r hr => (bernoulliDivergence_quadratic_deriv p (hi (interior_subset hr))).hasDerivWithinAt)
        (fun r hr => mul_nonneg (sub_nonneg.mpr (interior_subset hr).1)
          (bernoulli_curvature_bound (hi (interior_subset hr))))
    have h := hm (left_mem_Icc.mpr hpq) (right_mem_Icc.mpr hpq) hpq
    rw [hfp] at h
    dsimp [f] at h
    linarith
  · have hqp : q ≤ p := le_of_not_ge hpq
    have hi {r : ℝ} (hr : r ∈ Icc q p) : r ∈ Ioo 0 1 :=
      ⟨hq.1.trans_le hr.1, hr.2.trans_lt hp.2⟩
    have hm : AntitoneOn f (Icc q p) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc q p)
        (fun r hr => (bernoulliDivergence_quadratic_deriv p (hi hr)).continuousAt.continuousWithinAt)
        (fun r hr => (bernoulliDivergence_quadratic_deriv p (hi (interior_subset hr))).hasDerivWithinAt)
        (fun r hr => mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (interior_subset hr).2)
          (bernoulli_curvature_bound (hi (interior_subset hr))))
    have h := hm (left_mem_Icc.mpr hqp) (right_mem_Icc.mpr hqp) hqp
    rw [hfp] at h
    dsimp [f] at h
    linarith

/-- The sharp Bernoulli quadratic bound includes degenerate first laws. -/
theorem bernoulliDivergence_pinsker {p q : ℝ}
    (hp : p ∈ Icc 0 1) (hq : q ∈ Ioo 0 1) :
    2 * (p - q) ^ 2 ≤ bernoulliDivergence p q := by
  have hclosed : IsClosed {r : ℝ | 2 * (r - q) ^ 2 ≤ bernoulliDivergence r q} :=
    isClosed_le (by fun_prop) (continuous_bernoulliDivergence_left q)
  have hi : Ioo (0 : ℝ) 1 ⊆ {r : ℝ | 2 * (r - q) ^ 2 ≤ bernoulliDivergence r q} :=
    fun _ hr => bernoulliDivergence_pinsker_interior hr hq
  have h := closure_minimal hi hclosed
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at h
  exact h hp

end LectureNotes
