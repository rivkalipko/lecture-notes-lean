import LectureNotes.GaussianBayesRisk

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

def normalDensityReal {p : ℕ} (θ : Fin p → ℝ) (v : ℝ≥0) (y : Fin p → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal (θ i) v (y i)

theorem normalDensityReal_nonneg {p : ℕ} (θ : Fin p → ℝ) (v : ℝ≥0) (y : Fin p → ℝ) :
    0 ≤ normalDensityReal θ v y :=
  Finset.prod_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _)

theorem normalDensityReal_exp {p : ℕ} (θ : Fin p → ℝ) (v : ℝ≥0) (y : Fin p → ℝ) :
    normalDensityReal θ v y =
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ^ p *
        Real.exp (-(∑ i, (y i - θ i) ^ 2) / (2 * v)) := by
  unfold normalDensityReal
  simp only [gaussianPDFReal, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Real.exp_sum, ← Finset.sum_div,
    ← Finset.sum_neg_distrib]

theorem normalDensityReal_measurable {p : ℕ} (θ : Fin p → ℝ) (v : ℝ≥0) :
    Measurable (normalDensityReal θ v) := by unfold normalDensityReal; fun_prop

/-- Gaussian mass is larger on the side of a reflected pair facing the mean. -/
theorem normal_density_reflection_sign {p : ℕ} (θ y : Fin p → ℝ) (v : ℝ≥0)
    (hv : 0 < v) :
    0 ≤ (∑ i, θ i * y i) * (normalDensityReal θ v y - normalDensityReal θ v (-y)) := by
  have he : (∑ i, ((-y) i - θ i) ^ 2) - (∑ i, (y i - θ i) ^ 2) =
      4 * ∑ i, θ i * y i := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.neg_apply]
    ring
  have hv' : (0 : ℝ) < 2 * v := by positivity
  by_cases h : 0 ≤ ∑ i, θ i * y i
  · apply mul_nonneg h
    apply sub_nonneg.mpr
    rw [normalDensityReal_exp, normalDensityReal_exp]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact (div_le_div_iff_of_pos_right hv').mpr (by linarith)
  · apply mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge h)
    apply sub_nonpos.mpr
    rw [normalDensityReal_exp, normalDensityReal_exp]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact (div_le_div_iff_of_pos_right hv').mpr (by linarith)

theorem normal_risk_density {p : ℕ} (v : ℝ≥0) (hv : v ≠ 0)
    (δ : (Fin p → ℝ) → Fin p → ℝ) (hδ : Measurable δ) (θ : Fin p → ℝ) :
    normalMeansSquaredRisk v δ θ = ∫⁻ y,
      ENNReal.ofReal (normalDensityReal θ v y * ∑ i, (δ y i - θ i) ^ 2) := by
  unfold normalMeansSquaredRisk risk
  dsimp only
  rw [normal_pi_withDensity θ v hv,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  apply lintegral_congr
  intro y
  simp only [Pi.mul_apply, gaussianPDF, normalDensityReal,
    ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)]

/-- Quadratic loss of a scalar multiple of the data, expanded into its radial
and directional terms. -/
theorem normal_scalar_loss_expand {p : ℕ} (θ y : Fin p → ℝ) (c : ℝ) :
    (∑ i, (c * y i - θ i) ^ 2) =
      c ^ 2 * (∑ i, y i ^ 2) - 2 * c * (∑ i, θ i * y i) + ∑ i, θ i ^ 2 := by
  simp_rw [show ∀ i, (c * y i - θ i) ^ 2 =
    c ^ 2 * y i ^ 2 - 2 * c * (θ i * y i) + θ i ^ 2 by intro i; ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Truncating a negative scalar multiplier decreases the combined loss of
each reflected pair after weighting by the normal density. -/
theorem normal_reflected_positive_part_loss {p : ℕ} (θ y : Fin p → ℝ)
    (v : ℝ≥0) (hv : 0 < v) (c : ℝ) :
    normalDensityReal θ v y * (∑ i, (max 0 c * y i - θ i) ^ 2) +
      normalDensityReal θ v (-y) * (∑ i, (max 0 c * (-y) i - θ i) ^ 2) ≤
    normalDensityReal θ v y * (∑ i, (c * y i - θ i) ^ 2) +
      normalDensityReal θ v (-y) * (∑ i, (c * (-y) i - θ i) ^ 2) := by
  by_cases hc : 0 ≤ c
  · simp [max_eq_right hc]
  rw [max_eq_left (le_of_not_ge hc)]
  rw [normal_scalar_loss_expand θ y 0, normal_scalar_loss_expand θ (-y) 0,
    normal_scalar_loss_expand θ y c, normal_scalar_loss_expand θ (-y) c]
  simp only [Pi.neg_apply, neg_sq, mul_neg, Finset.sum_neg_distrib,
    zero_pow (by norm_num : 2 ≠ 0), zero_mul]
  have hS : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (y i))
  have h₁ := mul_nonneg (normalDensityReal_nonneg θ v y) (mul_nonneg (sq_nonneg c) hS)
  have h₂ := mul_nonneg (normalDensityReal_nonneg θ v (-y)) (mul_nonneg (sq_nonneg c) hS)
  have h₃ := mul_nonneg (show 0 ≤ -2 * c by linarith)
    (normal_density_reflection_sign θ y v hv)
  nlinarith

end LectureNotes
