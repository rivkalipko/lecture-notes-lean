import LectureNotes.BayesianUpdating

set_option autoImplicit false

/-! L12 normal-normal conjugacy: identify the normalized product of likelihood
and prior Gaussian kernels as an actual Gaussian probability measure. Factors
independent of the parameter cancel by `bayesUpdate_scale`. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem normalized_gaussian_density (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    bayesUpdate volume (gaussianPDFReal μ v) = gaussianReal μ v := by
  have he : evidence volume (gaussianPDFReal μ v) = 1 := integral_gaussianPDFReal_eq_one μ hv
  rw [bayesUpdate, he, gaussianReal_of_var_ne_zero μ hv]
  simp only [div_one]
  rfl

theorem normalized_gaussian_kernel (μ : ℝ) (v : ℝ≥0) (hv : 0 < v) :
    bayesUpdate volume (fun θ => Real.exp (-(θ - μ) ^ 2 / (2 * v))) = gaussianReal μ v := by
  rw [← normalized_gaussian_density μ v hv.ne']
  rw [gaussianPDFReal_def]
  symm
  apply bayesUpdate_scale
  apply inv_ne_zero
  apply (Real.sqrt_pos.mpr _).ne'
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (by exact_mod_cast hv)

/-- Known normal sampling precision a and positive prior precision b. The
input is exactly the unnormalized product of their Gaussian kernels. -/
theorem normal_normal_conjugacy (a b m μ : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    bayesUpdate volume (fun θ => Real.exp (-(a * (θ - m) ^ 2 + b * (θ - μ) ^ 2) / 2)) =
      gaussianReal (normalPosteriorMean a b m μ)
        ⟨normalPosteriorVariance a b, by unfold normalPosteriorVariance; positivity⟩ := by
  have hab : 0 < a + b := by positivity
  let v : ℝ≥0 := ⟨1 / (a + b), by positivity⟩
  have hv : 0 < v := by change 0 < (1 / (a + b) : ℝ); positivity
  have he (θ : ℝ) :
      Real.exp (-(a * (θ - m) ^ 2 + b * (θ - μ) ^ 2) / 2) =
      Real.exp (-(a * b / (a + b) * (m - μ) ^ 2) / 2) *
        Real.exp (-(θ - normalPosteriorMean a b m μ) ^ 2 / (2 * v)) := by
    rw [normal_posterior_complete_square a b m μ θ hab.ne', ← Real.exp_add]
    congr 1
    change -((a + b) * (θ - normalPosteriorMean a b m μ) ^ 2 +
      (a * b / (a + b)) * (m - μ) ^ 2) / 2 =
      -(a * b / (a + b) * (m - μ) ^ 2) / 2 +
        -(θ - normalPosteriorMean a b m μ) ^ 2 / (2 * (1 / (a + b)))
    field_simp [hab.ne']
    <;> ring
  simp_rw [he]
  rw [bayesUpdate_scale _ _ (Real.exp_pos _).ne']
  exact normalized_gaussian_kernel _ v hv

end LectureNotes
