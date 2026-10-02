import LectureNotes.PosteriorAsymptotics
import LectureNotes.VectorGaussianKernel
import LectureNotes.VectorScoreCLT
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped Topology InnerProductSpace

section Affine
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (ν : Measure E) [Measure.IsAddHaarMeasure ν]

/-- The inverse coordinate map used to center and linearly rescale a posterior. -/
def posteriorAffineEquiv (t : E) (A : E ≃L[ℝ] E) : E ≃ᵐ E where
  toFun z := t + A z
  invFun θ := A.symm (θ - t)
  left_inv z := by simp
  right_inv θ := by simp
  measurable_toFun := by change Measurable (fun z : E => t + A z); fun_prop
  measurable_invFun := by change Measurable (fun θ : E => A.symm (θ - t)); fun_prop

/-- Exact finite-dimensional change of variables for the evidence. -/
theorem evidence_affine_linear (q : E → ℝ) (t : E) (A : E ≃L[ℝ] E) :
    evidence ν q = |A.toContinuousLinearMap.det| *
      evidence ν (fun z => q (t + A z)) := by
  let e := posteriorAffineEquiv t A
  have hd (x : E) : HasFDerivAt e A.toContinuousLinearMap x := by
    exact A.hasFDerivAt.const_add t
  have h := integral_image_eq_integral_abs_det_fderiv_smul ν MeasurableSet.univ
    (fun x _ => (hd x).hasFDerivWithinAt) e.injective.injOn q
  rw [Set.image_univ, e.surjective.range_eq] at h
  change (∫ x in (Set.univ : Set E), q x ∂ν) =
    ∫ x in (Set.univ : Set E), |A.toContinuousLinearMap.det| * q (t + A x) ∂ν at h
  simpa only [Measure.restrict_univ, integral_const_mul, evidence] using h

/-- Integrability is preserved by every nonsingular affine coordinate change. -/
theorem integrable_affine_linear {q : E → ℝ} (hq : Integrable q ν)
    (t : E) (A : E ≃L[ℝ] E) : Integrable (fun z => q (t + A z)) ν := by
  let e := posteriorAffineEquiv t A
  have hd (x : E) : HasFDerivAt e A.toContinuousLinearMap x := by
    exact A.hasFDerivAt.const_add t
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul ν MeasurableSet.univ
    (fun x _ => (hd x).hasFDerivWithinAt) e.injective.injOn q
  rw [Set.image_univ, e.surjective.range_eq] at h
  change IntegrableOn q Set.univ ν ↔
    IntegrableOn (fun z => |A.toContinuousLinearMap.det| * q (t + A z)) Set.univ ν at h
  have hh : Integrable (fun z => |A.toContinuousLinearMap.det| * q (t + A z)) ν := by
    simpa only [integrableOn_univ] using h.mp (by simpa using hq)
  have hdet : |A.toContinuousLinearMap.det| ≠ 0 := by
    exact abs_ne_zero.mpr A.toLinearEquiv.isUnit_det'.ne_zero
  have hh' := hh.const_mul |A.toContinuousLinearMap.det|⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hdet, one_mul] using hh'

/-- The posterior under affine coordinates, including the proved Jacobian and
its cancellation against the transformed normalizer. -/
theorem bayesUpdate_map_affine_linear {q : E → ℝ} (hq : Integrable q ν)
    (hq0 : ∀ θ, 0 ≤ q θ) (he : 0 < evidence ν q)
    (t : E) (A : E ≃L[ℝ] E) :
    (bayesUpdate ν q).map (fun θ => A.symm (θ - t)) =
      bayesUpdate ν (fun z => q (t + A z)) := by
  let e := posteriorAffineEquiv t A
  have hd (x : E) : HasFDerivAt e A.toContinuousLinearMap x := by
    exact A.hasFDerivAt.const_add t
  have hdet : 0 < |A.toContinuousLinearMap.det| :=
    abs_pos.mpr A.toLinearEquiv.isUnit_det'.ne_zero
  have hi := integrable_affine_linear ν hq t A
  have hn : 0 < evidence ν (fun z => q (t + A z)) := by
    have hh := he
    rw [evidence_affine_linear ν q t A] at hh
    exact (mul_pos_iff_of_pos_left hdet).mp hh
  change (bayesUpdate ν q).map e.symm = _
  ext S hS
  rw [bayesUpdate, e.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul ν hS
    (ae_of_all _ (fun θ _ => div_nonneg (hq0 θ) he.le)) (hq.div_const _).integrableOn
    (fun x _ => (hd x).hasFDerivWithinAt)]
  rw [bayesUpdate, withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _).integrableOn
      (ae_of_all _ (fun z => div_nonneg (hq0 _) hn.le))]
  congr 1
  apply setIntegral_congr_fun hS
  intro z _
  change |A.toContinuousLinearMap.det| * (q (t + A z) / evidence ν q) =
    q (t + A z) / evidence ν (fun z => q (t + A z))
  rw [evidence_affine_linear ν q t A]
  field_simp
end Affine

section VectorCoordinates
variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

/-- Inverse scalar rescaling as a nonsingular linear coordinate change. -/
def posteriorScaleEquiv (r : ℝ) (hr : r ≠ 0) : V ≃L[ℝ] V where
  toFun z := r⁻¹ • z
  invFun θ := r • θ
  map_add' x y := smul_add _ _ _
  map_smul' c x := by simp [smul_smul, mul_comm]
  left_inv z := by simp [smul_smul, hr]
  right_inv θ := by simp [smul_smul, hr]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The likelihood-prior kernel in centered vector coordinates. -/
def vectorLocalPosteriorKernel (logL : ℕ → V → ℝ) (prior : V → ℝ)
    (center : ℕ → V) (rate : ℕ → ℝ) (n : ℕ) (z : V) : ℝ :=
  prior (center n + (rate n)⁻¹ • z) *
    Real.exp (logL n (center n + (rate n)⁻¹ • z) - logL n (center n))

/-- The scalar rescaling Jacobian has power equal to the parameter dimension. -/
theorem vector_evidence_affine (q : V → ℝ) (t : V) (r : ℝ) :
    evidence volume (fun z => q (t + r⁻¹ • z)) = |r ^ d| * evidence volume q := by
  unfold evidence
  change (∫ z : V, (fun x => q (t + x)) (r⁻¹ • z)) = _
  rw [Measure.integral_comp_inv_smul volume (fun x => q (t + x)) r,
    integral_add_left_eq_self]
  simp

/-- The exact posterior of the centered and rescaled parameter. -/
theorem vector_bayesUpdate_map_affine {q : V → ℝ} (hq : Integrable q volume)
    (hq0 : ∀ θ, 0 ≤ q θ) (he : 0 < evidence volume q)
    (t : V) (r : ℝ) (hr : r ≠ 0) :
    (bayesUpdate volume q).map (fun θ => r • (θ - t)) =
      bayesUpdate volume (fun z => q (t + r⁻¹ • z)) := by
  exact bayesUpdate_map_affine_linear volume hq hq0 he t (posteriorScaleEquiv r hr)

/-- The removed likelihood value and Jacobian are explicit factors of the local evidence. -/
theorem vectorLocalPosteriorKernel_evidence
    (logL : ℕ → V → ℝ) (prior : V → ℝ) (center : ℕ → V) (rate : ℕ → ℝ) (n : ℕ) :
    evidence volume (vectorLocalPosteriorKernel logL prior center rate n) =
      Real.exp (-logL n (center n)) * |rate n ^ d| *
        evidence volume (fun θ => prior θ * Real.exp (logL n θ)) := by
  have hk : vectorLocalPosteriorKernel logL prior center rate n =
      fun z => Real.exp (-logL n (center n)) *
        (prior (center n + (rate n)⁻¹ • z) * Real.exp (logL n (center n + (rate n)⁻¹ • z))) := by
    funext z
    simp only [vectorLocalPosteriorKernel, sub_eq_add_neg, Real.exp_add]
    ring
  rw [hk]
  change (∫ z, Real.exp (-logL n (center n)) *
    (prior (center n + (rate n)⁻¹ • z) * Real.exp (logL n (center n + (rate n)⁻¹ • z)))) = _
  rw [integral_const_mul]
  change Real.exp (-logL n (center n)) * evidence volume
    (fun z => (fun θ => prior θ * Real.exp (logL n θ)) (center n + (rate n)⁻¹ • z)) = _
  rw [vector_evidence_affine (fun θ => prior θ * Real.exp (logL n θ)) (center n) (rate n)]
  ring

/-- The local vector kernel represents the actual posterior pushforward before any limit. -/
theorem vectorLocalPosteriorKernel_eq_map
    (logL : ℕ → V → ℝ) (prior : V → ℝ) (center : ℕ → V) (rate : ℕ → ℝ)
    (hprior0 : ∀ θ, 0 ≤ prior θ) (n : ℕ) (hr : rate n ≠ 0)
    (hi : Integrable (fun θ => prior θ * Real.exp (logL n θ)) volume)
    (he : 0 < evidence volume (fun θ => prior θ * Real.exp (logL n θ))) :
    bayesUpdate volume (vectorLocalPosteriorKernel logL prior center rate n) =
      (bayesUpdate volume (fun θ => prior θ * Real.exp (logL n θ))).map
        (fun θ => rate n • (θ - center n)) := by
  rw [vector_bayesUpdate_map_affine hi
    (fun θ => mul_nonneg (hprior0 θ) (Real.exp_pos _).le) he _ _ hr]
  have hk : vectorLocalPosteriorKernel logL prior center rate n =
      fun z => Real.exp (-logL n (center n)) *
        (prior (center n + (rate n)⁻¹ • z) * Real.exp (logL n (center n + (rate n)⁻¹ • z))) := by
    funext z
    simp only [vectorLocalPosteriorKernel, sub_eq_add_neg, Real.exp_add]
    ring
  rw [hk, bayesUpdate_scale _ _ (Real.exp_pos _).ne']
end VectorCoordinates

section VectorGaussian
variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

/-- The covariance associated with a nonsingular Gaussian scale factor. -/
def vectorPosteriorCovariance (A : V ≃L[ℝ] V) : Matrix (Fin d) (Fin d) ℝ :=
  let B := (toEuclideanCLM (𝕜 := ℝ)).symm A.toContinuousLinearMap
  B * Bᵀ

/-- A nonsingular linear image of the standard Gaussian has its actual matrix covariance. -/
theorem vector_gaussian_scale_map (A : V ≃L[ℝ] V) :
    (stdGaussian V).map A = multivariateGaussian 0 (vectorPosteriorCovariance A) := by
  let B := (toEuclideanCLM (𝕜 := ℝ)).symm A.toContinuousLinearMap
  have h := multivariateGaussian_map_matrix (0 : V) (Matrix.PosSemidef.one (n := Fin d)) B
  have hB : toEuclideanCLM (𝕜 := ℝ) B = A.toContinuousLinearMap :=
    (toEuclideanCLM (𝕜 := ℝ)).apply_symm_apply A.toContinuousLinearMap
  rw [hB] at h
  simpa only [multivariateGaussian_zero_one, B,
    map_zero, mul_one, vectorPosteriorCovariance] using! h

/-- Integrability of every nonsingular multivariate Gaussian kernel. -/
theorem vector_gaussian_kernel_integrable (A : V ≃L[ℝ] V) :
    Integrable (fun z : V => Real.exp (-‖A.symm z‖ ^ 2 / 2)) volume := by
  simpa only [zero_add] using!
    integrable_affine_linear volume (stdGaussian_kernel_integrable (d := d)) 0 A.symm

/-- Normalization of the full covariance Gaussian kernel follows from change of variables. -/
theorem normalized_vector_gaussian_kernel (A : V ≃L[ℝ] V) :
    bayesUpdate volume (fun z : V => Real.exp (-‖A.symm z‖ ^ 2 / 2)) =
      multivariateGaussian 0 (vectorPosteriorCovariance A) := by
  have h := bayesUpdate_map_affine_linear volume (stdGaussian_kernel_integrable (d := d))
    (fun z => (Real.exp_pos _).le) (stdGaussian_kernel_integral_pos (d := d)) 0 A.symm
  simpa only [normalized_stdGaussian_kernel, sub_zero, zero_add,
    ContinuousLinearEquiv.symm_symm, vector_gaussian_scale_map] using! h.symm

/-- Dominated convergence of unnormalized vector kernels gives uniform posterior
probability approximation by the specified multivariate Gaussian. -/
theorem posterior_vector_gaussian_approximation {q : ℕ → V → ℝ} {bound : V → ℝ}
    {c : ℝ} (hc : 0 < c) (A : V ≃L[ℝ] V)
    (hq : ∀ n, AEStronglyMeasurable (q n) volume)
    (hq0 : ∀ n, ∀ᵐ z ∂volume, 0 ≤ q n z)
    (hb : Integrable bound volume) (hbound : ∀ n, ∀ᵐ z ∂volume, ‖q n z‖ ≤ bound z)
    (he : ∀ n, 0 < evidence volume (q n))
    (hlim : ∀ᵐ z ∂volume, Tendsto (fun n => q n z) atTop
      (𝓝 (c * Real.exp (-‖A.symm z‖ ^ 2 / 2)))) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (𝓝 0) ∧
      ∀ n S, MeasurableSet S →
        |(bayesUpdate volume (q n)).real S -
          (multivariateGaussian 0 (vectorPosteriorCovariance A)).real S| ≤ error n := by
  let f : V → ℝ := fun z => c * Real.exp (-‖A.symm z‖ ^ 2 / 2)
  have hf : Integrable f volume := (vector_gaussian_kernel_integrable A).const_mul c
  have hf0 : ∀ᵐ z ∂volume, 0 ≤ f z := ae_of_all _ (fun z => mul_nonneg hc.le (Real.exp_pos _).le)
  have hef : 0 < evidence volume f := by
    apply integral_pos_of_integrable_nonneg_nonzero (x := (0 : V)) (by fun_prop) hf
      (fun z => mul_nonneg hc.le (Real.exp_pos _).le)
    exact (mul_pos hc (Real.exp_pos _)).ne'
  have hqi (n) : Integrable (q n) volume := hb.mono' (hq n) (hbound n)
  have hnorm : bayesUpdate volume f = multivariateGaussian 0 (vectorPosteriorCovariance A) := by
    rw [show f = fun z => c * Real.exp (-‖A.symm z‖ ^ 2 / 2) from rfl,
      bayesUpdate_scale _ _ hc.ne', normalized_vector_gaussian_kernel]
  refine ⟨fun n => ∫ z, |normalizedKernel volume (q n) z - normalizedKernel volume f z|,
    fun _ => integral_nonneg (fun _ => abs_nonneg _),
    normalized_kernel_L1_of_dominated hq hf hb hbound hlim hef.ne', ?_⟩
  intro n S hS
  rw [← hnorm]
  exact posterior_event_error_le_L1 (hqi n) hf (hq0 n) hf0 (he n) hef S hS

/-- Vector local posterior approximation from prior continuity, local quadratic
likelihood convergence, and an integrable envelope. These are conditions on
unnormalized kernels and do not contain a posterior convergence conclusion. -/
theorem vector_local_posterior_gaussian_approximation
    (logL : ℕ → V → ℝ) (prior : V → ℝ) (center : ℕ → V) (rate : ℕ → ℝ)
    (θ₀ : V) (A : V ≃L[ℝ] V)
    (hprior : Measurable prior) (hprior0 : ∀ θ, 0 ≤ prior θ)
    (hpriorCont : ContinuousAt prior θ₀) (hpriorPos : 0 < prior θ₀)
    (hlogL : ∀ n, Measurable (logL n))
    (hcenter : Tendsto center atTop (𝓝 θ₀))
    (hrate : Tendsto (fun n => (rate n)⁻¹) atTop (𝓝 0))
    (hquadratic : ∀ z, Tendsto
      (fun n => logL n (center n + (rate n)⁻¹ • z) - logL n (center n)) atTop
      (𝓝 (-‖A.symm z‖ ^ 2 / 2)))
    (bound : V → ℝ) (hb : Integrable bound volume)
    (hbound : ∀ n, ∀ᵐ z ∂volume,
      ‖vectorLocalPosteriorKernel logL prior center rate n z‖ ≤ bound z)
    (he : ∀ n, 0 < evidence volume (vectorLocalPosteriorKernel logL prior center rate n)) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (𝓝 0) ∧
      ∀ n S, MeasurableSet S →
        |(bayesUpdate volume (vectorLocalPosteriorKernel logL prior center rate n)).real S -
          (multivariateGaussian 0 (vectorPosteriorCovariance A)).real S| ≤ error n := by
  apply posterior_vector_gaussian_approximation hpriorPos A
  · intro n
    apply Measurable.aestronglyMeasurable
    unfold vectorLocalPosteriorKernel
    fun_prop
  · intro n
    exact ae_of_all _ (fun z => mul_nonneg (hprior0 _) (Real.exp_pos _).le)
  · exact hb
  · exact hbound
  · exact he
  · apply ae_of_all
    intro z
    have ht : Tendsto (fun n => center n + (rate n)⁻¹ • z) atTop (𝓝 θ₀) := by
      simpa using hcenter.add (hrate.smul_const z)
    exact (hpriorCont.tendsto.comp ht).mul (Real.continuous_exp.tendsto _ |>.comp (hquadratic z))

/-- A vector extension of L12's posterior limit, with explicit sufficient
regularity. The conclusion is about the actual posterior of the parameter,
pushed forward by its centering and rate, uniformly over all measurable events. -/
theorem vector_centered_posterior_gaussian_limit
    (logL : ℕ → V → ℝ) (prior : V → ℝ) (center : ℕ → V) (rate : ℕ → ℝ)
    (θ₀ : V) (A : V ≃L[ℝ] V)
    (hprior : Measurable prior) (hprior0 : ∀ θ, 0 ≤ prior θ)
    (hpriorCont : ContinuousAt prior θ₀) (hpriorPos : 0 < prior θ₀)
    (hlogL : ∀ n, Measurable (logL n))
    (hcenter : Tendsto center atTop (𝓝 θ₀))
    (hrate : Tendsto (fun n => (rate n)⁻¹) atTop (𝓝 0)) (hr : ∀ n, rate n ≠ 0)
    (hquadratic : ∀ z, Tendsto
      (fun n => logL n (center n + (rate n)⁻¹ • z) - logL n (center n)) atTop
      (𝓝 (-‖A.symm z‖ ^ 2 / 2)))
    (bound : V → ℝ) (hb : Integrable bound volume)
    (hbound : ∀ n, ∀ᵐ z ∂volume,
      ‖vectorLocalPosteriorKernel logL prior center rate n z‖ ≤ bound z)
    (hi : ∀ n, Integrable (fun θ => prior θ * Real.exp (logL n θ)) volume)
    (he : ∀ n, 0 < evidence volume (fun θ => prior θ * Real.exp (logL n θ))) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (𝓝 0) ∧
      ∀ n S, MeasurableSet S →
        |((bayesUpdate volume (fun θ => prior θ * Real.exp (logL n θ))).map
          (fun θ => rate n • (θ - center n))).real S -
            (multivariateGaussian 0 (vectorPosteriorCovariance A)).real S| ≤ error n := by
  have helocal n : 0 < evidence volume (vectorLocalPosteriorKernel logL prior center rate n) := by
    rw [vectorLocalPosteriorKernel_evidence]
    exact mul_pos (mul_pos (Real.exp_pos _) (abs_pos.mpr (pow_ne_zero d (hr n)))) (he n)
  obtain ⟨err, herr, hlim, hS⟩ := vector_local_posterior_gaussian_approximation
    logL prior center rate θ₀ A hprior hprior0 hpriorCont hpriorPos hlogL
    hcenter hrate hquadratic bound hb hbound helocal
  refine ⟨err, herr, hlim, fun n S hSm => ?_⟩
  rw [← vectorLocalPosteriorKernel_eq_map logL prior center rate hprior0 n (hr n) (hi n) (he n)]
  exact hS n S hSm
end VectorGaussian

end LectureNotes
