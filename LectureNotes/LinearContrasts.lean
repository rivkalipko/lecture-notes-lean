import LectureNotes.GaussianBlockConditioning
import LectureNotes.VectorWald

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology InnerProductSpace MatrixProbability Matrix.Norms.Elementwise

/-- The full covariance of any rectangular linear contrast, retaining all
cross-coordinate terms. -/
theorem vectorCovariance_matrixBlockMap {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d p : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin d)} (hX : MemLp X 2 P)
    (A : Matrix (Fin p) (Fin d) ℝ) :
    vectorCovariance P (fun ω => matrixBlockMap A (X ω)) =
      A * vectorCovariance P X * Aᵀ := by
  ext i j
  simp only [vectorCovariance, matrixBlockMap_apply]
  rw [covariance_fun_sum_fun_sum (fun k => (hX.eval_piLp k).const_mul (A i k))
    (fun k => (hX.eval_piLp k).const_mul (A j k))]
  simp only [covariance_const_mul_left, covariance_const_mul_right,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  simp only [vectorCovariance]
  ring

/-- Rectangular Gaussian transformations, including singular covariance and
rank-deficient contrasts. -/
theorem multivariateGaussian_map_rectangular {d p : ℕ}
    (μ : EuclideanSpace ℝ (Fin d)) {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) (A : Matrix (Fin p) (Fin d) ℝ) :
    (multivariateGaussian μ S).map (matrixBlockMap A) =
      multivariateGaussian (matrixBlockMap A μ) (A * S * Aᵀ) := by
  have hg : HasGaussianLaw (matrixBlockMap A) (multivariateGaussian μ S) := by
    simpa only [Function.comp_id] using (IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian μ S)).map (matrixBlockMap A)
  have he : vectorCovariance (multivariateGaussian μ S) id = S := by
    ext i j
    exact covariance_eval_multivariateGaussian hS i j
  rw [gaussian_vector_law _ hg]
  rw [(matrixBlockMap A).integral_comp_id_comm IsGaussian.integrable_id,
    integral_id_multivariateGaussian]
  congr 1
  simpa only [id_eq, he] using vectorCovariance_matrixBlockMap
    (P := multivariateGaussian μ S) IsGaussian.memLp_two_id A

theorem gaussian_rectangular_contrast {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d p : ℕ} {Z : Ω → EuclideanSpace ℝ (Fin d)}
    {μ : EuclideanSpace ℝ (Fin d)} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) (hZ : HasLaw Z (multivariateGaussian μ S) P)
    (A : Matrix (Fin p) (Fin d) ℝ) :
    HasLaw (fun ω => matrixBlockMap A (Z ω))
      (multivariateGaussian (matrixBlockMap A μ) (A*S*Aᵀ)) P :=
  (show HasLaw (matrixBlockMap A)
    (multivariateGaussian (matrixBlockMap A μ) (A*S*Aᵀ)) (multivariateGaussian μ S) from
    ⟨(matrixBlockMap A).measurable.aemeasurable, multivariateGaussian_map_rectangular μ hS A⟩).comp hZ

/-- The contrast estimator's CLT follows from the joint input CLT. No
independence between entries of the input estimator is required. -/
theorem linear_contrast_clt {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d p : ℕ} {T : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {θ : EuclideanSpace ℝ (Fin d)}
    {Z : Ω' → EuclideanSpace ℝ (Fin d)} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef)
    (hT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ))
      atTop Z (fun _ => P) Q)
    (hZ : HasLaw Z (multivariateGaussian 0 S) Q)
    (A : Matrix (Fin p) (Fin d) ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n • (matrixBlockMap A (T n ω) - matrixBlockMap A θ))
      atTop (fun ω => matrixBlockMap A (Z ω)) (fun _ => P) Q ∧
    HasLaw (fun ω => matrixBlockMap A (Z ω)) (multivariateGaussian 0 (A*S*Aᵀ)) Q := by
  constructor
  · simpa only [Function.comp_def, map_smul, map_sub] using hT.continuous_comp (matrixBlockMap A).continuous
  · simpa only [map_zero] using gaussian_rectangular_contrast hS hZ A

/-- The joint Wald test for linear contrasts uses the full transformed
covariance AΣAᵀ and the number of independent contrast coordinates. -/
theorem linear_contrast_wald_coverage {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d p : ℕ} (hp : 0 < p)
    {T : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {θ : EuclideanSpace ℝ (Fin d)}
    {Z : Ω' → EuclideanSpace ℝ (Fin d)} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef)
    (hT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ))
      atTop Z (fun _ => P) Q)
    (hZ : HasLaw Z (multivariateGaussian 0 S) Q)
    (A : Matrix (Fin p) (Fin d) ℝ) (hV : (A*S*Aᵀ).PosDef)
    {Vhat : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ}
    (hVhat : TendstoInMeasure P Vhat atTop (fun _ => A*S*Aᵀ))
    (hVm : ∀ n, AEMeasurable (Vhat n) P)
    {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω | n * matrixQuadratic (Vhat n ω)⁻¹
      (matrixBlockMap A (T n ω) - matrixBlockMap A θ) ≤
        distributionQuantile (chiSquared p) q}) atTop (𝓝 q) := by
  obtain ⟨hC, hL⟩ := linear_contrast_clt hS hT hZ A
  exact vector_wald_ellipsoid_coverage hp hV hC hL hVhat hVm hq

end LectureNotes
