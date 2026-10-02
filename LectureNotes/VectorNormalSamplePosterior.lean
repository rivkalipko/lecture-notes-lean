import LectureNotes.VectorNormalPosteriorLimit
import Mathlib.Probability.StrongLaw

set_option autoImplicit false

/-! A normal location experiment in vector parameters: actual normalized densities,
finite-sample likelihood identities, and posterior approximation derived almost
surely from IID Gaussian sampling and explicit prior conditions. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped Topology InnerProductSpace

section VectorNormalDensity
variable {d n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

/-- The actual density of a normal location family with nonsingular scale A. -/
def vectorNormalDensity (A : V ≃L[ℝ] V) (μ x : V) : ℝ :=
  normalizedKernel volume (fun z : V => Real.exp (-‖A.symm z‖ ^ 2 / 2)) (x - μ)

theorem vector_gaussian_kernel_evidence_pos (A : V ≃L[ℝ] V) :
    0 < evidence volume (fun z : V => Real.exp (-‖A.symm z‖ ^ 2 / 2)) := by
  apply integral_pos_of_integrable_nonneg_nonzero (x := (0 : V))
    (by fun_prop) (vector_gaussian_kernel_integrable A) (fun _ => (Real.exp_pos _).le)
  exact (Real.exp_pos _).ne'

/-- Translation gives the usual Gaussian mean without changing its covariance. -/
theorem vector_gaussian_map_add (μ : V) (S : Matrix (Fin d) (Fin d) ℝ) :
    (multivariateGaussian 0 S).map (fun z => μ + z) = multivariateGaussian μ S := by
  unfold multivariateGaussian
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp only [Function.comp_apply, zero_add]

/-- The normal density used in the sample likelihood integrates to the actual
multivariateGaussian law, with the stated location and covariance. -/
theorem vectorNormalDensity_withDensity (A : V ≃L[ℝ] V) (μ : V) :
    volume.withDensity (fun x => ENNReal.ofReal (vectorNormalDensity A μ x)) =
      multivariateGaussian μ (vectorPosteriorCovariance A) := by
  have he : evidence volume (fun x : V => Real.exp (-‖A.symm (x - μ)‖ ^ 2 / 2)) =
      evidence volume (fun z : V => Real.exp (-‖A.symm z‖ ^ 2 / 2)) := by
    exact integral_sub_right_eq_self (fun z : V => Real.exp (-‖A.symm z‖ ^ 2 / 2)) μ
  have h := bayesUpdate_map_affine_linear volume (vector_gaussian_kernel_integrable A)
    (fun z => (Real.exp_pos _).le) (vector_gaussian_kernel_evidence_pos A) (-μ)
    (ContinuousLinearEquiv.refl ℝ V)
  have hm : (fun θ : V => (ContinuousLinearEquiv.refl ℝ V).symm (θ - -μ)) =
      (fun θ => μ + θ) := by funext θ; simp [add_comm]
  rw [hm, normalized_vector_gaussian_kernel, vector_gaussian_map_add] at h
  rw [h]
  unfold bayesUpdate vectorNormalDensity normalizedKernel
  have hf : (fun z : V => Real.exp (-‖A.symm (-μ + (ContinuousLinearEquiv.refl ℝ V) z)‖ ^ 2 / 2)) =
      (fun z => Real.exp (-‖A.symm (z - μ)‖ ^ 2 / 2)) := by
    funext z
    simp [sub_eq_add_neg, add_comm]
  rw [hf, he]

/-- Normalizing each observation's density contributes a parameter-independent
factor, so the product-density posterior equals the product-kernel posterior. -/
theorem vector_normal_density_posterior (x : Fin n → V) (A : V ≃L[ℝ] V) (prior : V → ℝ) :
    bayesUpdate volume (fun θ => prior θ * ∏ i, vectorNormalDensity A θ (x i)) =
      bayesUpdate volume (fun θ => prior θ * ∏ i, Real.exp (-‖A.symm (x i - θ)‖ ^ 2 / 2)) := by
  let c := (evidence volume (fun z : V => Real.exp (-‖A.symm z‖ ^ 2 / 2)))⁻¹
  have hc : c ≠ 0 := inv_ne_zero (vector_gaussian_kernel_evidence_pos A).ne'
  have he : (fun θ => prior θ * ∏ i, vectorNormalDensity A θ (x i)) =
      fun θ => c ^ n * (prior θ * ∏ i, Real.exp (-‖A.symm (x i - θ)‖ ^ 2 / 2)) := by
    funext θ
    simp only [vectorNormalDensity, normalizedKernel, div_eq_mul_inv, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, c]
    ring
  rw [he, bayesUpdate_scale _ _ (pow_ne_zero n hc)]
end VectorNormalDensity

section VectorNormalSample
variable {d n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

/-- The vector sample average, with the usual zero convention for an empty sample. -/
def vectorSampleAverage (x : Fin n → V) : V := (n : ℝ)⁻¹ • ∑ i, x i

/-- Centering a nonempty sample makes its transformed residuals sum to zero. -/
theorem vector_normal_centered_sum (x : Fin n → V) (hn : 0 < n) (A : V ≃L[ℝ] V) :
    (∑ i, A.symm (x i - vectorSampleAverage x)) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← map_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
    vectorSampleAverage, smul_smul, mul_inv_cancel₀ hn', one_smul, sub_self, map_zero]

/-- The multivariate normal likelihood's quadratic sum separates exactly into
sample residuals and the squared distance from the sample average. -/
theorem vector_normal_sum_squares (x : Fin n → V) (hn : 0 < n)
    (A : V ≃L[ℝ] V) (θ : V) :
    (∑ i, ‖A.symm (x i - θ)‖ ^ 2) =
      (∑ i, ‖A.symm (x i - vectorSampleAverage x)‖ ^ 2) +
        (n : ℝ) * ‖A.symm (θ - vectorSampleAverage x)‖ ^ 2 := by
  have he (i : Fin n) : A.symm (x i - θ) =
      A.symm (x i - vectorSampleAverage x) - A.symm (θ - vectorSampleAverage x) := by
    rw [← map_sub]
    congr 1
    abel
  simp_rw [he, norm_sub_sq_real]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← sum_inner, vector_normal_centered_sum x hn A, inner_zero_left,
    mul_zero, sub_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The full parameter-dependent normal sample likelihood is a positive
constant times the centered normal-mean likelihood kernel. -/
theorem vector_normal_sample_kernel_factorization (x : Fin n → V) (hn : 0 < n)
    (A : V ≃L[ℝ] V) (θ : V) :
    (∏ i, Real.exp (-‖A.symm (x i - θ)‖ ^ 2 / 2)) =
      Real.exp (-(∑ i, ‖A.symm (x i - vectorSampleAverage x)‖ ^ 2) / 2) *
        Real.exp (-(n : ℝ) * ‖A.symm (θ - vectorSampleAverage x)‖ ^ 2 / 2) := by
  rw [← Real.exp_sum]
  simp only [← Finset.sum_div, Finset.sum_neg_distrib]
  rw [vector_normal_sum_squares x hn A θ, ← Real.exp_add]
  congr 1
  ring

/-- Replacing the actual product of normal kernels by the quadratic kernel
at the sample average leaves the posterior exactly unchanged. -/
theorem vector_normal_sample_posterior (x : Fin n → V) (hn : 0 < n)
    (A : V ≃L[ℝ] V) (prior : V → ℝ) :
    bayesUpdate volume (fun θ => prior θ * ∏ i, Real.exp (-‖A.symm (x i - θ)‖ ^ 2 / 2)) =
      bayesUpdate volume (fun θ => prior θ *
        Real.exp (-(n : ℝ) * ‖A.symm (θ - vectorSampleAverage x)‖ ^ 2 / 2)) := by
  have he : (fun θ => prior θ * ∏ i, Real.exp (-‖A.symm (x i - θ)‖ ^ 2 / 2)) =
      fun θ => Real.exp (-(∑ i, ‖A.symm (x i - vectorSampleAverage x)‖ ^ 2) / 2) *
        (prior θ * Real.exp (-(n : ℝ) * ‖A.symm (θ - vectorSampleAverage x)‖ ^ 2 / 2)) := by
    funext θ
    rw [vector_normal_sample_kernel_factorization x hn A θ]
    ring
  rw [he, bayesUpdate_scale _ _ (Real.exp_pos _).ne']

/-- The posterior limit for sample normal likelihoods and a bounded continuous
prior. The center is the actual sample average of n+1 observations. -/
theorem vector_normal_sample_posterior_limit
    (x : ∀ n : ℕ, Fin (n + 1) → V) (prior : V → ℝ) (θ₀ : V) (A : V ≃L[ℝ] V)
    (hprior : Continuous prior) (hprior0 : ∀ θ, 0 ≤ prior θ)
    (hpriorInt : Integrable prior volume) (hpriorPos : 0 < prior θ₀)
    (C : ℝ) (hC : ∀ θ, prior θ ≤ C)
    (hcenter : Tendsto (fun n => vectorSampleAverage (x n)) atTop (𝓝 θ₀)) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (𝓝 0) ∧
      ∀ n S, MeasurableSet S →
        |((bayesUpdate volume (fun θ => prior θ *
          ∏ i, Real.exp (-‖A.symm (x n i - θ)‖ ^ 2 / 2))).map
            (fun θ => Real.sqrt ((n : ℝ) + 1) • (θ - vectorSampleAverage (x n)))).real S -
              (multivariateGaussian 0 (vectorPosteriorCovariance A)).real S| ≤ error n := by
  have hr (n : ℕ) : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
  have hrate : Tendsto (fun n : ℕ => (Real.sqrt ((n : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
  obtain ⟨error, hn, hl, he⟩ := vector_normal_mean_posterior_gaussian_limit prior
    (fun n => vectorSampleAverage (x n)) (fun n => Real.sqrt ((n : ℝ) + 1)) θ₀ A
    hprior hprior0 hpriorInt hpriorPos C hC hcenter hrate hr
  refine ⟨error, hn, hl, fun n S hS => ?_⟩
  have hp := vector_normal_sample_posterior (x n) (Nat.succ_pos n) A prior
  have hk : (fun θ => prior θ *
      Real.exp (-((n + 1 : ℕ) : ℝ) * ‖A.symm (θ - vectorSampleAverage (x n))‖ ^ 2 / 2)) =
      fun θ => prior θ * Real.exp (vectorNormalMeanLogKernel
        (fun n => vectorSampleAverage (x n)) (fun n => Real.sqrt ((n : ℝ) + 1)) A n θ) := by
    funext θ
    simp [vectorNormalMeanLogKernel, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1)]
  rw [hp, hk]
  exact he n S hS
end VectorNormalSample

section VectorNormalIID
variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

/-- The posterior limit for products of the actual normalized Gaussian densities. -/
theorem vector_normal_density_posterior_limit
    (x : ∀ n : ℕ, Fin (n + 1) → V) (prior : V → ℝ) (θ₀ : V) (A : V ≃L[ℝ] V)
    (hprior : Continuous prior) (hprior0 : ∀ θ, 0 ≤ prior θ)
    (hpriorInt : Integrable prior volume) (hpriorPos : 0 < prior θ₀)
    (C : ℝ) (hC : ∀ θ, prior θ ≤ C)
    (hcenter : Tendsto (fun n => vectorSampleAverage (x n)) atTop (𝓝 θ₀)) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (𝓝 0) ∧
      ∀ n S, MeasurableSet S →
        |((bayesUpdate volume (fun θ => prior θ * ∏ i, vectorNormalDensity A θ (x n i))).map
            (fun θ => Real.sqrt ((n : ℝ) + 1) • (θ - vectorSampleAverage (x n)))).real S -
              (multivariateGaussian 0 (vectorPosteriorCovariance A)).real S| ≤ error n := by
  obtain ⟨error, hn, hl, he⟩ := vector_normal_sample_posterior_limit x prior θ₀ A
    hprior hprior0 hpriorInt hpriorPos C hC hcenter
  refine ⟨error, hn, hl, fun n S hS => ?_⟩
  rw [vector_normal_density_posterior]
  exact he n S hS

/-- For IID observations from the actual vector Gaussian location model, the
center consistency follows from the strong law. Almost every sample path has
uniform Gaussian posterior approximation for every bounded continuous proper
prior that is positive at the true mean. -/
theorem iid_vector_normal_posterior_limit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → V) (θ₀ : V) (A : V ≃L[ℝ] V)
    (hX : ∀ i, HasLaw (X i) (multivariateGaussian θ₀ (vectorPosteriorCovariance A)) P)
    (hind : iIndepFun X P)
    (prior : V → ℝ) (hprior : Continuous prior) (hprior0 : ∀ θ, 0 ≤ prior θ)
    (hpriorInt : Integrable prior volume) (hpriorPos : 0 < prior θ₀)
    (C : ℝ) (hC : ∀ θ, prior θ ≤ C) :
    ∀ᵐ ω ∂P, ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (𝓝 0) ∧
      ∀ n S, MeasurableSet S →
        |((bayesUpdate volume (fun θ => prior θ *
          ∏ i : Fin (n + 1), vectorNormalDensity A θ (X i ω))).map
            (fun θ => Real.sqrt ((n : ℝ) + 1) •
              (θ - vectorSampleAverage (fun i : Fin (n + 1) => X i ω)))).real S -
                (multivariateGaussian 0 (vectorPosteriorCovariance A)).real S| ≤ error n := by
  have hi : IdentDistrib (X 0) id P (multivariateGaussian θ₀ (vectorPosteriorCovariance A)) :=
    (hX 0).identDistrib HasLaw.id
  have hint : Integrable (X 0) P := hi.integrable_iff.mpr IsGaussian.integrable_id
  have hmean : (∫ ω, X 0 ω ∂P) = θ₀ := (hX 0).integral_eq.trans integral_id_multivariateGaussian
  have hlln := strong_law_ae X hint (fun i j hij => hind.indepFun hij)
    (fun i => (hX i).identDistrib (hX 0))
  filter_upwards [hlln] with ω hω
  have hcenter : Tendsto
      (fun n => vectorSampleAverage (fun i : Fin (n + 1) => X i ω)) atTop (𝓝 θ₀) := by
    have hshift := hω.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ •
      ∑ i ∈ Finset.range (n + 1), X i ω) atTop (𝓝 (∫ ω, X 0 ω ∂P)) at hshift
    have hfun : (fun n => vectorSampleAverage (fun i : Fin (n + 1) => X i ω)) =
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range (n + 1), X i ω) := by
      funext n
      unfold vectorSampleAverage
      rw [Fin.sum_univ_eq_sum_range (fun i => X i ω) (n + 1)]
    rw [hfun]
    simpa only [hmean] using! hshift
  exact vector_normal_density_posterior_limit
    (fun n i => X i ω) prior θ₀ A hprior hprior0 hpriorInt hpriorPos C hC hcenter
end VectorNormalIID

section VectorNormalMaximum
variable {d n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

/-- The actual vector normal sample likelihood has a global maximum at the
sample average, for every nonempty sample and nonsingular known scale. -/
theorem vector_normal_density_likelihood_max (x : Fin n → V) (hn : 0 < n)
    (A : V ≃L[ℝ] V) (θ : V) :
    (∏ i, vectorNormalDensity A θ (x i)) ≤
      ∏ i, vectorNormalDensity A (vectorSampleAverage x) (x i) := by
  let c := (evidence volume (fun z : V => Real.exp (-‖A.symm z‖ ^ 2 / 2)))⁻¹
  have hc : 0 ≤ c ^ n := pow_nonneg (inv_nonneg.mpr (vector_gaussian_kernel_evidence_pos A).le) n
  have he (t : V) : (∏ i, vectorNormalDensity A t (x i)) =
      c ^ n * ∏ i, Real.exp (-‖A.symm (x i - t)‖ ^ 2 / 2) := by
    simp only [vectorNormalDensity, normalizedKernel, div_eq_mul_inv, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, c]
    ring
  rw [he θ, he (vectorSampleAverage x)]
  apply mul_le_mul_of_nonneg_left _ hc
  rw [vector_normal_sample_kernel_factorization x hn A θ,
    vector_normal_sample_kernel_factorization x hn A (vectorSampleAverage x)]
  simp only [sub_self, map_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_div, Real.exp_zero, mul_one]
  apply mul_le_of_le_one_right (Real.exp_pos _).le
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (sq_nonneg _))
    (by norm_num)
end VectorNormalMaximum

end LectureNotes
