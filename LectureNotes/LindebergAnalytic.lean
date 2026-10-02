import LectureNotes.Foundations

set_option autoImplicit false

/-! Analytic estimates for the Lindeberg replacement argument. The bounds
use second moments and truncated second moments, with no third-moment
assumption on the random variables. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

def characteristicRemainder (x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I + (x : ℂ) ^ 2 / 2

theorem exp_imaginary_first_remainder_bound (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I‖ ≤ |x| ^ 2 := by
  let f (t : ℝ) := Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I
  have hd (t : ℝ) : HasDerivAt f
      ((Complex.exp ((t : ℂ) * Complex.I) - 1) * Complex.I) t := by
    have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).cexp.sub_const 1
    convert! h.sub ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I) using 1 <;>
      simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] <;> ring
  have hb t (ht : t ∈ uIcc 0 x) :
      ‖(Complex.exp ((t : ℂ) * Complex.I) - 1) * Complex.I‖ ≤ |x| := by
    rw [norm_mul, Complex.norm_I, mul_one]
    have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t)
    rw [mul_comm Complex.I, Real.norm_eq_abs] at h
    exact h.trans (by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc ht)
  have h := (convex_uIcc 0 x).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) hb left_mem_uIcc right_mem_uIcc
  simpa [f, pow_two, Real.norm_eq_abs] using h

theorem characteristicRemainder_cubic_bound (x : ℝ) :
    ‖characteristicRemainder x‖ ≤ |x| ^ 3 := by
  have hd (t : ℝ) : HasDerivAt characteristicRemainder
      ((Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I) * Complex.I) t := by
    have h := (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).cexp.sub_const 1).sub
      ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I)
    have h₂ := ((Complex.ofRealCLM.hasDerivAt (x := t)).pow 2).div_const 2
    convert! h.add h₂ using 1 <;>
      simp only [characteristicRemainder, Complex.ofRealCLM_apply,
        Complex.ofReal_one, one_mul, pow_one] <;>
      ring_nf <;> simp [Complex.I_sq]
  have hb t (ht : t ∈ uIcc 0 x) :
      ‖(Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I) * Complex.I‖ ≤ |x| ^ 2 := by
    rw [norm_mul, Complex.norm_I, mul_one]
    apply (exp_imaginary_first_remainder_bound t).trans
    apply pow_le_pow_left₀ (abs_nonneg _) (by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc ht)
  have h := (convex_uIcc 0 x).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) hb left_mem_uIcc right_mem_uIcc
  simpa [characteristicRemainder, pow_succ, Real.norm_eq_abs] using h

theorem characteristicRemainder_quadratic_bound (x : ℝ) :
    ‖characteristicRemainder x‖ ≤ 2 * x ^ 2 := by
  have h := norm_add_le
    (Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I) ((x : ℂ) ^ 2 / 2)
  have h₁ := exp_imaginary_first_remainder_bound x
  have h₂ : ‖(x : ℂ) ^ 2 / 2‖ = x ^ 2 / 2 := by
    simp [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [h₂] at h
  rw [sq_abs] at h₁
  change ‖characteristicRemainder x‖ ≤ _ at h
  nlinarith [sq_nonneg x]

theorem characteristicRemainder_truncation_bound (t x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ‖characteristicRemainder (t * x)‖ ≤
      |t| ^ 3 * δ * x ^ 2 + 2 * t ^ 2 * (if δ < |x| then x ^ 2 else 0) := by
  by_cases hx : δ < |x|
  · rw [if_pos hx]
    have h := characteristicRemainder_quadratic_bound (t * x)
    rw [mul_pow] at h
    nlinarith [mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg t) 3) hδ.le) (sq_nonneg x)]
  · rw [if_neg hx, mul_zero, add_zero]
    calc
      _ ≤ |t * x| ^ 3 := characteristicRemainder_cubic_bound _
      _ = |t| ^ 3 * |x| * x ^ 2 := by rw [abs_mul, mul_pow]; simp [pow_succ, sq_abs]; ring
      _ ≤ _ := by gcongr; exact le_of_not_gt hx

theorem norm_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hf' : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' : ∀ i ∈ s, ‖g i‖ ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hgp : ‖∏ i ∈ s, g i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) hg'
    have he : f a * (∏ i ∈ s, f i) - g a * (∏ i ∈ s, g i) =
        f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
          (f a - g a) * (∏ i ∈ s, g i) := by ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    calc
      _ ≤ 1 * (∑ i ∈ s, ‖f i - g i‖) + ‖f a - g a‖ * 1 := by
        gcongr
        · exact hf a (Finset.mem_insert_self _ _)
        · exact ih hf' hg'
      _ = _ := by ring

theorem exp_neg_first_remainder_bound {a : ℝ} (ha : 0 ≤ a) :
    |Real.exp (-a) - 1 + a| ≤ a ^ 2 := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-t) - 1 + t)
      (1 - Real.exp (-t)) t := by
    convert! ((((hasDerivAt_id t).neg.exp).sub_const 1).add (hasDerivAt_id t)) using 1 <;>
      simp only [Pi.neg_apply, id_eq] <;> ring
  have hb t (ht : t ∈ Icc 0 a) : ‖1 - Real.exp (-t)‖ ≤ a := by
    have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.1)
    have hl := Real.add_one_le_exp (-t)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr he)]
    linarith [ht.2]
  have h := (convex_Icc 0 a).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) hb (left_mem_Icc.mpr ha) (right_mem_Icc.mpr ha)
  simpa [Real.norm_eq_abs, abs_of_nonneg ha, pow_two] using h

end LectureNotes
