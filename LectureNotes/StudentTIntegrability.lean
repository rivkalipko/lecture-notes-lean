import LectureNotes.GaussianRadialMoments
import LectureNotes.StudentTMoments

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

/-- Exact inverse chi-square integrability, including the low-dimensional failure. -/
theorem chiSquared_inverse_integrable_iff {n : ℕ} (hn : 0 < n) :
    Integrable (fun y : ℝ => 1 / y) (chiSquared n) ↔ 2 < n := by
  have hl : HasLaw (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (chiSquared n)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by simpa using (stdGaussian_norm_sq (E := EuclideanSpace ℝ (Fin n)))
  rw [← hl.map_eq, integrable_map_measure (Measurable.aestronglyMeasurable (by fun_prop)) hl.aemeasurable]
  have he : (fun x : EuclideanSpace ℝ (Fin n) => 1 / ‖x‖ ^ 2) = fun x => ‖x‖ ^ (-(2 : ℝ)) := by
    funext x
    rw [Real.rpow_neg (norm_nonneg x), Real.rpow_two, one_div]
  change Integrable (fun x : EuclideanSpace ℝ (Fin n) => 1 / ‖x‖ ^ 2) _ ↔ _
  rw [he, stdGaussian_inverse_norm_integrable_iff hn]
  norm_cast

/-- The reciprocal Student denominator is integrable exactly above one degree of freedom. -/
theorem chiSquared_inverse_student_denominator_integrable_iff {n : ℕ} (hn : 0 < n) :
    Integrable (fun y : ℝ => 1 / Real.sqrt (y / n)) (chiSquared n) ↔ 1 < n := by
  have hl : HasLaw (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (chiSquared n)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by simpa using (stdGaussian_norm_sq (E := EuclideanSpace ℝ (Fin n)))
  rw [← hl.map_eq, integrable_map_measure (Measurable.aestronglyMeasurable (by fun_prop)) hl.aemeasurable]
  have he : (fun x : EuclideanSpace ℝ (Fin n) => 1 / Real.sqrt (‖x‖ ^ 2 / n)) =
      fun x => Real.sqrt n * ‖x‖ ^ (-(1 : ℝ)) := by
    funext x
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.rpow_neg_one]
    simp only [div_eq_mul_inv, inv_mul_cancel₀, inv_inv, one_mul, mul_inv_rev]
  change Integrable (fun x : EuclideanSpace ℝ (Fin n) => 1 / Real.sqrt (‖x‖ ^ 2 / n)) _ ↔ _
  rw [he, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn))),
    stdGaussian_inverse_norm_integrable_iff hn]
  norm_cast

/-- The mean of a Student distribution exists exactly when the degrees of
freedom exceed one. In particular, a Cauchy random variable has no expectation. -/
theorem studentT_integrable_iff {n : ℕ} (hn : 0 < n) :
    Integrable id (studentT n) ↔ 1 < n := by
  rw [← chiSquared_inverse_student_denominator_integrable_iff hn, studentT,
    integrable_map_measure (by fun_prop) (Measurable.aemeasurable (by fun_prop))]
  change Integrable (fun z : ℝ × ℝ => z.1 / Real.sqrt (z.2 / n))
    ((gaussianReal 0 1).prod (chiSquared n)) ↔ _
  constructor
  · intro h
    haveI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
    obtain ⟨z, hz, hi⟩ := (((gaussianReal 0 1).ae_ne 0).and h.prod_right_ae).exists
    apply (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hz) _).mp
    simpa only [div_eq_mul_inv, one_mul] using hi
  · intro h
    have hi : Integrable id (gaussianReal 0 1) := (memLp_id_gaussianReal 2).integrable (by norm_num)
    simpa only [id_eq, div_eq_mul_inv, one_mul] using hi.mul_prod h

/-- The Student second moment exists exactly above two degrees of freedom. -/
theorem studentT_memLp_two_iff {n : ℕ} (hn : 0 < n) :
    MemLp id 2 (studentT n) ↔ 2 < n := by
  constructor
  · intro h
    have hi := (memLp_two_iff_integrable_sq (by fun_prop)).mp h
    rw [studentT, integrable_map_measure (by fun_prop) (Measurable.aemeasurable (by fun_prop))] at hi
    have he := (studentT_ratio_square_ae hn)
    have hip : Integrable (fun z : ℝ × ℝ => z.1 ^ 2 * ((n : ℝ) * (1 / z.2)))
        ((gaussianReal 0 1).prod (chiSquared n)) := hi.congr he
    haveI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
    obtain ⟨z, hz, hi⟩ := (((gaussianReal 0 1).ae_ne 0).and hip.prod_right_ae).exists
    have hc : z ^ 2 * (n : ℝ) ≠ 0 := mul_ne_zero (pow_ne_zero _ hz) (by exact_mod_cast hn.ne')
    have hi' : Integrable (fun y : ℝ => 1 / y) (chiSquared n) := by
      apply (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _).mp
      simpa only [mul_assoc] using hi
    exact (chiSquared_inverse_integrable_iff hn).mp hi'
  · intro h
    exact studentT_memLp_two (by omega)

/-- L1's zero-mean assertion needs the explicit condition `n > 1`. -/
theorem studentT_mean {n : ℕ} (_hn : 1 < n) : (∫ x : ℝ, x ∂studentT n) = 0 := by
  rw [studentT, integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  simp only [id_eq, div_eq_mul_inv]
  rw [integral_prod_mul (fun z : ℝ => z) (fun y : ℝ => (Real.sqrt (y * (n : ℝ)⁻¹))⁻¹)]
  simp

theorem studentT_one_not_integrable : ¬ Integrable id (studentT 1) := by
  rw [studentT_integrable_iff (by norm_num)]
  norm_num

/-- Infinite second moments are expressed in the extended nonnegative reals,
not by assigning an infinite value to the totalized real-valued variance. -/
theorem studentT_low_df_second_moment_infinite {n : ℕ} (hn : 0 < n) (hn2 : n ≤ 2) :
    (∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂studentT n) = ∞ := by
  have hnot : ¬ Integrable (fun x : ℝ => x ^ 2) (studentT n) := by
    intro h
    have hh := (memLp_two_iff_integrable_sq (by fun_prop)).mpr h
    have := (studentT_memLp_two_iff hn).mp hh
    omega
  by_contra h
  apply hnot
  refine ⟨by fun_prop, ?_⟩
  change (∫⁻ x : ℝ, ‖x ^ 2‖ₑ ∂studentT n) < ∞
  simp only [Real.enorm_eq_ofReal_abs, abs_pow, sq_abs]
  exact lt_top_iff_ne_top.mpr h

end LectureNotes
