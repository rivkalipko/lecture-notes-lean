import LectureNotes.VectorPosteriorAsymptotics

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped Topology InnerProductSpace

section VectorNormalMean
variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

/-- The parameter-dependent quadratic normal-mean log likelihood with covariance
A*Aᵀ. For n observations, rate = √n and center is the sample mean. -/
def vectorNormalMeanLogKernel (center : ℕ → V) (rate : ℕ → ℝ)
    (A : V ≃L[ℝ] V) (n : ℕ) (θ : V) : ℝ :=
  -(rate n) ^ 2 * ‖A.symm (θ - center n)‖ ^ 2 / 2

/-- In local coordinates the normal-mean log likelihood ratio is exactly quadratic. -/
theorem vector_normal_mean_local_log_ratio (center : ℕ → V) (rate : ℕ → ℝ)
    (A : V ≃L[ℝ] V) (n : ℕ) (hr : rate n ≠ 0) (z : V) :
    vectorNormalMeanLogKernel center rate A n (center n + (rate n)⁻¹ • z) -
      vectorNormalMeanLogKernel center rate A n (center n) = -‖A.symm z‖ ^ 2 / 2 := by
  unfold vectorNormalMeanLogKernel
  simp only [add_sub_cancel_left, sub_self, map_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_div, sub_zero, map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp

/-- A bounded continuous nonnegative integrable prior, positive at the true
parameter, suffices for the vector normal-mean posterior limit. Properness,
domination, and local quadraticity are proved here, not assumed. -/
theorem vector_normal_mean_posterior_gaussian_limit
    (prior : V → ℝ) (center : ℕ → V) (rate : ℕ → ℝ) (θ₀ : V) (A : V ≃L[ℝ] V)
    (hprior : Continuous prior) (hprior0 : ∀ θ, 0 ≤ prior θ)
    (hpriorInt : Integrable prior volume) (hpriorPos : 0 < prior θ₀)
    (C : ℝ) (hC : ∀ θ, prior θ ≤ C)
    (hcenter : Tendsto center atTop (𝓝 θ₀))
    (hrate : Tendsto (fun n => (rate n)⁻¹) atTop (𝓝 0))
    (hr : ∀ n, rate n ≠ 0) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (𝓝 0) ∧
      ∀ n S, MeasurableSet S →
        |((bayesUpdate volume (fun θ => prior θ *
          Real.exp (vectorNormalMeanLogKernel center rate A n θ))).map
            (fun θ => rate n • (θ - center n))).real S -
              (multivariateGaussian 0 (vectorPosteriorCovariance A)).real S| ≤ error n := by
  have hnonpos n θ : vectorNormalMeanLogKernel center rate A n θ ≤ 0 := by
    unfold vectorNormalMeanLogKernel
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _)) (by norm_num)
  have hcont n : Continuous (fun θ => prior θ *
      Real.exp (vectorNormalMeanLogKernel center rate A n θ)) := by
    unfold vectorNormalMeanLogKernel
    fun_prop
  have hi n : Integrable (fun θ => prior θ *
      Real.exp (vectorNormalMeanLogKernel center rate A n θ)) volume := by
    apply hpriorInt.mono' (hcont n).aestronglyMeasurable
    apply ae_of_all
    intro θ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hprior0 θ) (Real.exp_pos _).le)]
    exact mul_le_of_le_one_right (hprior0 θ) (Real.exp_le_one_iff.mpr (hnonpos n θ))
  have he n : 0 < evidence volume (fun θ => prior θ *
      Real.exp (vectorNormalMeanLogKernel center rate A n θ)) := by
    apply integral_pos_of_integrable_nonneg_nonzero (hcont n) (hi n)
      (fun θ => mul_nonneg (hprior0 θ) (Real.exp_pos _).le)
    exact (mul_pos hpriorPos (Real.exp_pos _)).ne'
  refine vector_centered_posterior_gaussian_limit
    (vectorNormalMeanLogKernel center rate A) prior center rate θ₀ A
    hprior.measurable hprior0 hprior.continuousAt hpriorPos
    (fun n => by unfold vectorNormalMeanLogKernel; fun_prop) hcenter hrate hr
    ?_ (fun z => C * Real.exp (-‖A.symm z‖ ^ 2 / 2)) ?_ ?_ hi he
  · intro z
    simpa only [vector_normal_mean_local_log_ratio center rate A _ (hr _) z] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => -‖A.symm z‖ ^ 2 / 2) atTop _)
  · exact (vector_gaussian_kernel_integrable A).const_mul C
  · intro n
    apply ae_of_all
    intro z
    rw [vectorLocalPosteriorKernel,
      vector_normal_mean_local_log_ratio center rate A n (hr n) z,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hprior0 _) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.exp_pos _).le

/-- A proper nondegenerate Gaussian prior satisfies all the normal-mean prior
conditions, without requiring a flat-prior approximation in finite samples. -/
theorem vector_normal_mean_gaussian_prior_limit
    (μ : V) (B : V ≃L[ℝ] V) (center : ℕ → V) (rate : ℕ → ℝ) (θ₀ : V) (A : V ≃L[ℝ] V)
    (hcenter : Tendsto center atTop (𝓝 θ₀))
    (hrate : Tendsto (fun n => (rate n)⁻¹) atTop (𝓝 0))
    (hr : ∀ n, rate n ≠ 0) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (𝓝 0) ∧
      ∀ n S, MeasurableSet S →
        |((bayesUpdate volume (fun θ => Real.exp (-‖B.symm (θ - μ)‖ ^ 2 / 2) *
          Real.exp (vectorNormalMeanLogKernel center rate A n θ))).map
            (fun θ => rate n • (θ - center n))).real S -
              (multivariateGaussian 0 (vectorPosteriorCovariance A)).real S| ≤ error n := by
  apply vector_normal_mean_posterior_gaussian_limit
    (fun θ => Real.exp (-‖B.symm (θ - μ)‖ ^ 2 / 2)) center rate θ₀ A
    (by fun_prop) (fun _ => (Real.exp_pos _).le)
    ((vector_gaussian_kernel_integrable B).comp_sub_right μ) (Real.exp_pos _) 1
    (fun θ => Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num))) hcenter hrate hr
end VectorNormalMean

end LectureNotes
