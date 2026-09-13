import LectureNotes.GaussianQuadraticForms

/-! L1 §4.2: the covariance-inverse quadratic form of a nondegenerate Gaussian. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace MatrixOrder

/-- Whitening cancels the positive square root of the covariance. -/
theorem covariance_sqrt_inverse_cancel {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosDef) : CFC.sqrt S * S⁻¹ * CFC.sqrt S = 1 := by
  let R := CFC.sqrt S
  have hR : R * R = S := CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have hRd : IsUnit R.det := by
    rw [isUnit_iff_ne_zero]
    intro he
    have h := congrArg Matrix.det hR
    rw [Matrix.det_mul, he, zero_mul] at h
    exact hdet.ne_zero h.symm
  change R * S⁻¹ * R = 1
  calc
    R * S⁻¹ * R = R * (R⁻¹ * R⁻¹) * R := by rw [← hR, Matrix.mul_inv_rev]
    _ = (R * R⁻¹) * (R⁻¹ * R) := by simp only [mul_assoc]
    _ = 1 := by rw [Matrix.mul_nonsing_inv _ hRd, Matrix.nonsing_inv_mul _ hRd, one_mul]

/-- The actual multivariate Gaussian covariance model has a chi-square
Mahalanobis distance, with degrees of freedom equal to the ambient dimension. -/
theorem normal_mahalanobis {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {X : Ω → EuclideanSpace ℝ (Fin n)} {μ : EuclideanSpace ℝ (Fin n)}
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    (hX : HasLaw X (multivariateGaussian μ S) P) :
    HasLaw (fun ω => ⟪X ω - μ, toEuclideanCLM (𝕜 := ℝ) S⁻¹ (X ω - μ)⟫_ℝ)
      (chiSquared n) P := by
  let R := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  let V := toEuclideanCLM (𝕜 := ℝ) S⁻¹
  have hsym : R.adjoint = R := by
    exact ((CFC.sqrt_nonneg S).isSelfAdjoint.map (toEuclideanCLM (𝕜 := ℝ))).adjoint_eq
  have hcancel : R * V * R = 1 := by
    change toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) * toEuclideanCLM (𝕜 := ℝ) S⁻¹ *
      toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) = 1
    rw [← map_mul, ← map_mul, covariance_sqrt_inverse_cancel hS, map_one]
  have he (z : EuclideanSpace ℝ (Fin n)) : ⟪R z, V (R z)⟫_ℝ = ‖z‖ ^ 2 := by
    rw [← R.adjoint_inner_right, hsym]
    have hc : R (V (R z)) = z := by
      have h := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => L z) hcancel
      simpa [mul_apply_eq_comp] using h
    rw [hc, real_inner_self_eq_norm_sq]
  have hLaw : HasLaw (fun x : EuclideanSpace ℝ (Fin n) =>
      ⟪x - μ, V (x - μ)⟫_ℝ) (chiSquared n) (multivariateGaussian μ S) := by
    refine ⟨by fun_prop, ?_⟩
    rw [multivariateGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
    have hf : (fun x : EuclideanSpace ℝ (Fin n) => ⟪x - μ, V (x - μ)⟫_ℝ) ∘
        (fun z => μ + R z) = fun z => ‖z‖ ^ 2 := by
      funext z
      simpa only [Function.comp_apply, add_sub_cancel_left] using he z
    change (stdGaussian (EuclideanSpace ℝ (Fin n))).map
      ((fun x => ⟪x - μ, V (x - μ)⟫_ℝ) ∘ (fun z => μ + R z)) = _
    rw [hf]
    simpa using (stdGaussian_norm_sq (E := EuclideanSpace ℝ (Fin n))).map_eq
  exact hLaw.comp hX

end LectureNotes
