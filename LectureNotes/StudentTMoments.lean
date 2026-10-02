import LectureNotes.EmpiricalBayesStein
import LectureNotes.ChiSquaredMoments

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

/-- The inverse chi-square moment is integrable above two degrees of freedom. -/
theorem chiSquared_inverse_integrable {n : ℕ} (hn : 3 ≤ n) :
    Integrable (fun y : ℝ => 1 / y) (chiSquared n) := by
  cases n with
  | zero => omega
  | succ k =>
    rw [chiSquared]
    apply (integrable_map_measure (by fun_prop) (Measurable.aemeasurable (by fun_prop))).mpr
    simpa only [Function.comp_def, normalSquareNorm] using
      (normal_inverse_square_integrable (fun _ : Fin (k + 1) => 0) 1 (by norm_num) hn)

theorem chiSquared_inverse_moment {n : ℕ} (hn : 3 ≤ n) :
    (∫ y : ℝ, 1 / y ∂chiSquared n) = 1 / ((n : ℝ) - 2) := by
  rw [chiSquared, integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  simpa only [normalSquareNorm, NNReal.coe_one, mul_one] using
    centered_normal_inverse_square hn 1 (by norm_num)

theorem studentT_ratio_square_ae {n : ℕ} (hn : 0 < n) :
    (fun z : ℝ × ℝ => (z.1 / Real.sqrt (z.2 / n)) ^ 2) =ᵐ[(gaussianReal 0 1).prod (chiSquared n)]
      fun z => z.1 ^ 2 * ((n : ℝ) * (1 / z.2)) := by
  have hy : ∀ᵐ z : ℝ × ℝ ∂(gaussianReal 0 1).prod (chiSquared n), 0 < z.2 :=
    (measurePreserving_snd (μ := gaussianReal 0 1) (ν := chiSquared n)).quasiMeasurePreserving.ae
      (chiSquared_ae_pos hn)
  filter_upwards [hy] with z hz
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_pow, Real.sq_sqrt (div_pos hz hn').le]
  field_simp

/-- Student's t has a finite second moment when its degrees of freedom exceed two. -/
theorem studentT_memLp_two {n : ℕ} (hn : 3 ≤ n) : MemLp id 2 (studentT n) := by
  rw [studentT]
  apply (memLp_map_measure_iff (by fun_prop) (Measurable.aemeasurable (by fun_prop))).mpr
  change MemLp (fun z : ℝ × ℝ => z.1 / Real.sqrt (z.2 / n)) 2 _
  apply (memLp_two_iff_integrable_sq (Measurable.aestronglyMeasurable (by fun_prop))).mpr
  have hZ : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 1) :=
    (normal_square_memLp 0 1).integrable (by norm_num)
  have hY := (chiSquared_inverse_integrable hn).const_mul (n : ℝ)
  exact (hZ.mul_prod hY).congr (studentT_ratio_square_ae (by omega)).symm

/-- The mean in the finite-variance range is an ordinary integrable expectation. -/
theorem studentT_integrable_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    Integrable id (studentT n) := (studentT_memLp_two hn).integrable (by norm_num)

theorem studentT_mean_of_three_le {n : ℕ} (_hn : 3 ≤ n) :
    (∫ x : ℝ, x ∂studentT n) = 0 := by
  rw [studentT, integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  simp only [div_eq_mul_inv]
  rw [integral_prod_mul (fun z : ℝ => z) (fun y : ℝ => (Real.sqrt (y * (n : ℝ)⁻¹))⁻¹)]
  simp

theorem studentT_second_moment {n : ℕ} (hn : 3 ≤ n) :
    (∫ x : ℝ, x ^ 2 ∂studentT n) = (n : ℝ) / ((n : ℝ) - 2) := by
  rw [studentT, integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  rw [integral_congr_ae (studentT_ratio_square_ae (by omega)),
    integral_prod_mul (fun z : ℝ => z ^ 2) (fun y : ℝ => (n : ℝ) * (1 / y)),
    standard_normal_second_moment, one_mul, integral_const_mul, chiSquared_inverse_moment hn]
  ring

/-- L1: the finite Student-t variance, proved from the independent normal and
chi-square construction and an integrable inverse chi-square moment. -/
theorem studentT_variance {n : ℕ} (hn : 3 ≤ n) :
    Var[id; studentT n] = (n : ℝ) / ((n : ℝ) - 2) := by
  rw [variance_eq_sub (studentT_memLp_two hn)]
  simp only [Pi.pow_apply, id_eq, studentT_second_moment hn, studentT_mean_of_three_le hn,
    zero_pow (by decide : 2 ≠ 0), sub_zero]

end LectureNotes
