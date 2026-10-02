import LectureNotes.MultivariateCLT
import LectureNotes.GaussianMahalanobis
import LectureNotes.IIDScoreAsymptotics

set_option autoImplicit false

/-! L3/L7: a vector CLT with its actual covariance matrix, including singular
covariances. The Gaussian target is constructed from coordinate covariances;
its projection laws are proved, rather than supplied as extra hypotheses. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology InnerProductSpace

variable {Ω Ξ Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {d : ℕ}

/-- The covariance of a real vector, in the standard coordinate basis. -/
def vectorCovariance (P : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => cov[fun ω => X ω i, fun ω => X ω j; P]

theorem covarianceBilin_eq_vectorCovariance {X : Ω → EuclideanSpace ℝ (Fin d)}
    (hX : MemLp X 2 P) (x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin (P.map X) x y = x ⬝ᵥ vectorCovariance P X *ᵥ y := by
  have h := covarianceBilin_apply_pi (fun i => hX.eval_piLp i) x y
  have he : (fun ω => WithLp.toLp 2 (fun i => X ω i)) = X := by rfl
  rw [he] at h
  rw [h]
  simp only [vectorCovariance, dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem vectorCovariance_posSemidef {X : Ω → EuclideanSpace ℝ (Fin d)}
    (hX : MemLp X 2 P) : (vectorCovariance P X).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, vectorCovariance]
    exact covariance_comm _ _
  · intro x
    simpa only [star_trivial, covarianceBilin_eq_vectorCovariance hX] using
      (covarianceBilin_self_nonneg (μ := P.map X) (WithLp.toLp 2 x))

/-- Every projection of the constructed Gaussian has exactly the projection
variance of the original vector. -/
theorem gaussian_vectorCovariance_projection {X : Ω → EuclideanSpace ℝ (Fin d)}
    (hX : MemLp X 2 P) (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    HasLaw L (gaussianReal 0 (Var[fun ω => L (X ω); P]).toNNReal)
      (multivariateGaussian 0 (vectorCovariance P X)) := by
  let v := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm L
  have he : (fun x => ⟪v, x⟫_ℝ) = L := by
    funext x
    exact InnerProductSpace.toDual_symm_apply
  have hLp : MemLp id 2 (P.map X) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hX.aemeasurable).mpr hX
  have hv : Var[L; multivariateGaussian 0 (vectorCovariance P X)] =
      Var[fun ω => L (X ω); P] := by
    rw [← he, ← covarianceBilin_self IsGaussian.memLp_two_id,
      covarianceBilin_multivariateGaussian (vectorCovariance_posSemidef hX),
      ← covarianceBilin_eq_vectorCovariance hX, covarianceBilin_self hLp, he,
      variance_map L.measurable.aemeasurable hX.aemeasurable]
    rfl
  refine ⟨L.measurable.aemeasurable, ?_⟩
  rw [IsGaussian.map_eq_gaussianReal, hv,
    L.integral_comp_id_comm IsGaussian.integrable_id,
    integral_id_multivariateGaussian, map_zero]

/-- The multivariate CLT with a canonical target measure and actual covariance.
No positive definiteness or independently supplied Gaussian target is needed. -/
theorem multivariate_clt_covariance {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : MemLp (X 0) 2 P) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ •
        ((∑ i ∈ Finset.range n, X i ω) - (n : ℝ) • P[X 0]))
      atTop id (fun _ => P) (multivariateGaussian 0 (vectorCovariance P (X 0))) := by
  exact multivariate_central_limit_theorem hX hind hident aemeasurable_id
    (gaussian_vectorCovariance_projection hX)

/-- The IID vector score CLT in the square-root-times-average form used in
the estimating equation proof. -/
theorem iid_zero_mean_vector_score_clt (X : ℕ → Ω → Ξ)
    (g : Ξ → EuclideanSpace ℝ (Fin d)) (hg : Measurable g)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (h₂ : MemLp (fun ω => g (X 0 ω)) 2 P)
    (hmean : (∫ ω, g (X 0 ω) ∂P) = 0)
    {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    (hZ : HasLaw Z (multivariateGaussian 0 (vectorCovariance P (fun ω => g (X 0 ω)))) Q) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n •
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, g (X i ω)))
      atTop Z (fun _ => P) Q := by
  have h := multivariate_central_limit_theorem h₂
    (hind.comp (fun _ => g) (fun _ => hg)) (fun i => (hident i).comp hg)
    hZ.aemeasurable (fun L => (gaussian_vectorCovariance_projection h₂ L).comp hZ)
  have he (n : ℕ) : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
    simpa only [div_eq_mul_inv, one_mul, mul_one] using sqrt_times_average n 1
  simpa only [Function.comp_def, hmean, smul_zero, sub_zero, smul_smul, he] using h

/-- A linear transformation of a multivariate Gaussian has the covariance
matrix `A S Aᵀ`, including when the covariance or transformation is singular. -/
theorem multivariateGaussian_map_matrix (μ : EuclideanSpace ℝ (Fin d))
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef)
    (A : Matrix (Fin d) (Fin d) ℝ) :
    (multivariateGaussian μ S).map (toEuclideanCLM (𝕜 := ℝ) A) =
      multivariateGaussian (toEuclideanCLM (𝕜 := ℝ) A μ) (A * S * Aᵀ) := by
  let L := toEuclideanCLM (𝕜 := ℝ) A
  have hS' : (A * S * Aᵀ).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hS.mul_mul_conjTranspose_same A
  have hAdj : toEuclideanCLM (𝕜 := ℝ) Aᵀ = L.adjoint := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      ContinuousLinearMap.star_eq_adjoint] using! (map_star (toEuclideanCLM (𝕜 := ℝ)) A)
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [L.integral_id_map IsGaussian.integrable_id,
      integral_id_multivariateGaussian, integral_id_multivariateGaussian]
  · ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id L,
      covarianceBilin_multivariateGaussian hS, covarianceBilin_multivariateGaussian hS',
      ← inner_toEuclideanCLM, ← inner_toEuclideanCLM,
      ContinuousLinearMap.adjoint_inner_left]
    congr 1
    rw [map_mul, map_mul, hAdj]
    rfl

theorem gaussian_linear_transform {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    {μ : EuclideanSpace ℝ (Fin d)} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) (hZ : HasLaw Z (multivariateGaussian μ S) Q)
    (A : Matrix (Fin d) (Fin d) ℝ) :
    HasLaw (fun ω => toEuclideanCLM (𝕜 := ℝ) A (Z ω))
      (multivariateGaussian (toEuclideanCLM (𝕜 := ℝ) A μ) (A * S * Aᵀ)) Q := by
  apply HasLaw.comp (X := Z) _ hZ
  exact ⟨(toEuclideanCLM (𝕜 := ℝ) A).measurable.aemeasurable,
    multivariateGaussian_map_matrix μ hS A⟩

/-- Operator form of the covariance transformation, used for inverse
information operators in the vector estimating equation. -/
theorem gaussian_clm_transform {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    {μ : EuclideanSpace ℝ (Fin d)} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) (hZ : HasLaw Z (multivariateGaussian μ S) Q)
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    let A := (toEuclideanCLM (𝕜 := ℝ)).symm L
    HasLaw (fun ω => L (Z ω)) (multivariateGaussian (L μ) (A * S * Aᵀ)) Q := by
  simpa only [StarAlgEquiv.apply_symm_apply] using!
    gaussian_linear_transform hS hZ ((toEuclideanCLM (𝕜 := ℝ)).symm L)

end LectureNotes
