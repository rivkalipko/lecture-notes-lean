import LectureNotes.VectorWald

set_option autoImplicit false

/-! L11: both endpoints of the projection of a bivariate Wald ellipse.
The covariance has positive diagonal entries and positive determinant.
The cutoff is the joint chi-square cutoff, not a marginal normal cutoff. -/
noncomputable section
namespace LectureNotes
open Set Matrix

def bivariateWald (a b c u v : ℝ) : ℝ :=
  (b * u ^ 2 - 2 * c * u * v + a * v ^ 2) / (a * b - c ^ 2)

/-- The displayed scalar expression is the actual inverse-covariance form. -/
theorem bivariateWald_eq_matrix (a b c u v : ℝ) :
    matrixQuadratic (!![a, c; c, b])⁻¹ (WithLp.toLp 2 ![u, v]) =
      bivariateWald a b c u v := by
  rw [matrixQuadratic_eq_sum, Matrix.inv_def, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of]
  simp only [Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    bivariateWald]
  change u * ((a * b - c * c)⁻¹ * b) * u + u * ((a * b - c * c)⁻¹ * -c) * v +
    (v * ((a * b - c * c)⁻¹ * -c) * u + v * ((a * b - c * c)⁻¹ * a) * v) = _
  simp only [pow_two, div_eq_mul_inv]
  ring

theorem bivariateWald_complete_square {a b c : ℝ} (hb : 0 < b)
    (hdet : 0 < a * b - c ^ 2) (u v : ℝ) :
    bivariateWald a b c u v = v ^ 2 / b +
      b / (a * b - c ^ 2) * (u - c * v / b) ^ 2 := by
  unfold bivariateWald
  have hd : b * a - c ^ 2 ≠ 0 := by nlinarith
  field_simp [hb.ne', hdet.ne', hd]
  <;> ring

theorem bivariateWald_minimum {a b c : ℝ} (hb : 0 < b)
    (hdet : 0 < a * b - c ^ 2) (u v : ℝ) :
    v ^ 2 / b ≤ bivariateWald a b c u v := by
  rw [bivariateWald_complete_square hb hdet]
  exact le_add_of_nonneg_right (mul_nonneg (div_pos hb hdet).le (sq_nonneg _))

theorem bivariateWald_minimum_attained {a b c : ℝ} (hb : 0 < b)
    (hdet : 0 < a * b - c ^ 2) (v : ℝ) :
    bivariateWald a b c (c * v / b) v = v ^ 2 / b := by
  simp [bivariateWald_complete_square hb hdet]

theorem bivariateWald_projection {a b c N q v : ℝ} (hb : 0 < b)
    (hdet : 0 < a * b - c ^ 2) (hN : 0 < N) :
    (∃ u, N * bivariateWald a b c u v ≤ q) ↔ v ^ 2 ≤ q * b / N := by
  have he : v ^ 2 / b ≤ q / N ↔ v ^ 2 ≤ q * b / N := by
    have heq : q / N * b = q * b / N := by ring
    rw [div_le_iff₀ hb, heq]
  constructor
  · rintro ⟨u, hu⟩
    apply he.mp
    exact (bivariateWald_minimum hb hdet u v).trans
      ((le_div_iff₀ hN).mpr (by nlinarith))
  · intro h
    refine ⟨c * v / b, ?_⟩
    rw [bivariateWald_minimum_attained hb hdet]
    have hh := (le_div_iff₀ hN).mp (he.mpr h)
    nlinarith

theorem squared_error_interval {r : ℝ} (hr : 0 ≤ r) (m t : ℝ) :
    (m - t) ^ 2 ≤ r ↔ t ∈ Icc (m - Real.sqrt r) (m + Real.sqrt r) := by
  have hs := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg r
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (m - t + Real.sqrt r),
      sq_nonneg (m - t - Real.sqrt r)]
  · rintro ⟨hl, hu⟩
    nlinarith [mul_nonneg (by linarith : 0 ≤ Real.sqrt r - (m - t))
      (by linarith : 0 ≤ (m - t) + Real.sqrt r)]

/-- Projecting onto the second coordinate eliminates the first coordinate by
minimization. Correlation changes the minimizing first coordinate, but the
projection radius is `sqrt(q * b / N)`. -/
theorem wald_ellipse_projection_second {a b c N q : ℝ} (hb : 0 < b)
    (hdet : 0 < a * b - c ^ 2) (hN : 0 < N) (hq : 0 ≤ q) (αhat βhat : ℝ) :
    {β | ∃ α, N * matrixQuadratic (!![a, c; c, b])⁻¹
      (WithLp.toLp 2 ![αhat - α, βhat - β]) ≤ q} =
      Icc (βhat - Real.sqrt (q * b / N)) (βhat + Real.sqrt (q * b / N)) := by
  ext β
  simp only [Set.mem_ofPred_eq, bivariateWald_eq_matrix]
  rw [← squared_error_interval (by positivity : 0 ≤ q * b / N)]
  rw [← bivariateWald_projection hb hdet hN]
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨αhat - α, hα⟩
  · rintro ⟨u, hu⟩
    refine ⟨αhat - u, ?_⟩
    simpa only [sub_sub_cancel] using hu

theorem bivariateWald_swap (a b c u v : ℝ) :
    bivariateWald a b c u v = bivariateWald b a c v u := by
  unfold bivariateWald
  congr 1 <;> ring

theorem wald_ellipse_projection_first {a b c N q : ℝ} (ha : 0 < a)
    (hdet : 0 < a * b - c ^ 2) (hN : 0 < N) (hq : 0 ≤ q) (αhat βhat : ℝ) :
    {α | ∃ β, N * matrixQuadratic (!![a, c; c, b])⁻¹
      (WithLp.toLp 2 ![αhat - α, βhat - β]) ≤ q} =
      Icc (αhat - Real.sqrt (q * a / N)) (αhat + Real.sqrt (q * a / N)) := by
  have hdet' : 0 < b * a - c ^ 2 := by nlinarith
  have h := wald_ellipse_projection_second ha hdet' hN hq βhat αhat
  simp only [bivariateWald_eq_matrix] at h ⊢
  convert! h using 1
  ext α
  simp only [Set.mem_ofPred_eq, bivariateWald_swap a b c]

end LectureNotes
