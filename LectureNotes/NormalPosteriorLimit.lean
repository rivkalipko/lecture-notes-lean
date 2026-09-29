import LectureNotes.PosteriorAsymptotics

set_option autoImplicit false

/-! Verification of posterior asymptotics for a quadratic normal-mean
likelihood with a bounded continuous prior, which need not be Gaussian. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

/-- The parameter-dependent part of a normal-mean log likelihood. For n
observations with known variance v, take rate = √n and center = sample mean. -/
def normalMeanLogKernel (center rate : ℕ → ℝ) (v : ℝ≥0) (n : ℕ) (θ : ℝ) : ℝ :=
  -(rate n) ^ 2 * (θ - center n) ^ 2 / (2 * v)

theorem normal_mean_local_log_ratio (center rate : ℕ → ℝ) (v : ℝ≥0)
    (n : ℕ) (hr : rate n ≠ 0) (z : ℝ) :
    normalMeanLogKernel center rate v n (center n + z / rate n) -
      normalMeanLogKernel center rate v n (center n) = -z ^ 2 / (2 * v) := by
  unfold normalMeanLogKernel
  simp only [add_sub_cancel_left, sub_self, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_div, sub_zero]
  congr 1
  field_simp
  <;> ring

theorem normal_mean_local_posterior_kernel (prior : ℝ → ℝ) (center rate : ℕ → ℝ)
    (v : ℝ≥0) (n : ℕ) (hr : rate n ≠ 0) (z : ℝ) :
    localPosteriorKernel (normalMeanLogKernel center rate v) prior center rate n z =
      prior (center n + z / rate n) * Real.exp (-z ^ 2 / (2 * v)) := by
  unfold localPosteriorKernel
  rw [normal_mean_local_log_ratio center rate v n hr z]

/-- A full verification of the analytic posterior theorem for a normal-mean
likelihood. Boundedness and continuity of the prior establish domination and
local prior convergence; integrability and positivity at θ₀ establish proper
posteriors. No normal approximation is included among the hypotheses. -/
theorem normal_mean_posterior_gaussian_limit
    (prior : ℝ → ℝ) (center rate : ℕ → ℝ) (θ₀ : ℝ) (v : ℝ≥0) (hv : 0 < v)
    (hprior : Continuous prior) (hprior0 : ∀ θ, 0 ≤ prior θ)
    (hpriorInt : Integrable prior volume) (hpriorPos : 0 < prior θ₀)
    (K : ℝ) (hK : ∀ θ, prior θ ≤ K)
    (hcenter : Tendsto center atTop (𝓝 θ₀))
    (hrate : Tendsto (fun n => (rate n)⁻¹) atTop (𝓝 0))
    (hr : ∀ n, rate n ≠ 0) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (𝓝 0) ∧
      ∀ n A, MeasurableSet A →
        |((bayesUpdate volume (fun θ => prior θ *
          Real.exp (normalMeanLogKernel center rate v n θ))).map
            (fun θ => rate n * (θ - center n))).real A -
              (gaussianReal 0 v).real A| ≤ error n := by
  have hnonpos n θ : normalMeanLogKernel center rate v n θ ≤ 0 := by
    unfold normalMeanLogKernel
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _))
      (by positivity)
  have hcont n : Continuous (fun θ => prior θ *
      Real.exp (normalMeanLogKernel center rate v n θ)) := by
    unfold normalMeanLogKernel
    fun_prop
  have hi n : Integrable (fun θ => prior θ *
      Real.exp (normalMeanLogKernel center rate v n θ)) volume := by
    apply hpriorInt.mono' (hcont n).aestronglyMeasurable
    apply ae_of_all
    intro θ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hprior0 θ) (Real.exp_pos _).le)]
    exact mul_le_of_le_one_right (hprior0 θ) (Real.exp_le_one_iff.mpr (hnonpos n θ))
  have he n : 0 < evidence volume (fun θ => prior θ *
      Real.exp (normalMeanLogKernel center rate v n θ)) := by
    apply integral_pos_of_integrable_nonneg_nonzero (hcont n) (hi n)
      (fun θ => mul_nonneg (hprior0 θ) (Real.exp_pos _).le)
    exact (mul_pos hpriorPos (Real.exp_pos _)).ne'
  refine centered_posterior_gaussian_limit
    (normalMeanLogKernel center rate v) prior center rate θ₀ v hv
    hprior.measurable hprior0 hprior.continuousAt hpriorPos
    (fun n => by unfold normalMeanLogKernel; fun_prop) hcenter hrate hr
    ?_ (fun z => K * Real.exp (-z ^ 2 / (2 * v))) ?_ ?_ hi he
  · intro z
    simpa only [normal_mean_local_log_ratio center rate v _ (hr _) z] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => -z ^ 2 / (2 * (v : ℝ))) atTop _)
  · exact (by simpa using (gaussian_kernel_integrable 0 v hv).const_mul K)
  · intro n
    apply ae_of_all
    intro z
    rw [normal_mean_local_posterior_kernel prior center rate v n (hr n) z,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hprior0 _) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right (hK _) (Real.exp_pos _).le

end LectureNotes
