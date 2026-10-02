import LectureNotes.GaussianConditioning
import LectureNotes.VectorScoreCLT

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped ENNReal InnerProductSpace

/-- Rectangular matrix multiplication as a continuous linear map on Euclidean spaces. -/
def matrixBlockMap {d e : ℕ} (A : Matrix (Fin d) (Fin e) ℝ) :
    EuclideanSpace ℝ (Fin e) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

theorem matrixBlockMap_apply {d e : ℕ} (A : Matrix (Fin d) (Fin e) ℝ)
    (y : EuclideanSpace ℝ (Fin e)) (i : Fin d) :
    matrixBlockMap A y i = ∑ j, A i j * y j := rfl

/-- The rectangular cross-covariance block. -/
def crossCovariance {Ω : Type*} [MeasurableSpace Ω] {d e : ℕ}
    (P : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d))
    (Y : Ω → EuclideanSpace ℝ (Fin e)) : Matrix (Fin d) (Fin e) ℝ :=
  fun i j => cov[fun ω => X ω i, fun ω => Y ω j; P]

theorem gaussian_vector_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin d)} (hX : HasGaussianLaw X P) :
    P.map X = multivariateGaussian (∫ ω, X ω ∂P) (vectorCovariance P X) := by
  have := hX.isGaussian_map
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [integral_id_multivariateGaussian]
    simpa only [id_eq] using! (integral_map hX.aemeasurable aestronglyMeasurable_id)
  · ext x y
    rw [covarianceBilin_eq_vectorCovariance hX.memLp_two,
      covarianceBilin_multivariateGaussian (vectorCovariance_posSemidef hX.memLp_two)]

theorem multivariateGaussian_map_add {d : ℕ} (μ a : EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ) :
    (multivariateGaussian μ S).map (fun r => r + a) = multivariateGaussian (μ + a) S := by
  unfold multivariateGaussian
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_def]
  abel

/-- Gaussian block regression. The matrix equation is the normal equation
`A Σ₂₂ = Σ₁₂`; no conditional distribution is assumed. -/
theorem gaussian_block_conditional_law_of_regression_matrix
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d e : ℕ} {X : Ω → EuclideanSpace ℝ (Fin d)}
    {Y : Ω → EuclideanSpace ℝ (Fin e)} (hX : Measurable X) (hY : Measurable Y)
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (A : Matrix (Fin d) (Fin e) ℝ)
    (hA : A * vectorCovariance P Y = crossCovariance P X Y) :
    condDistrib X Y P =ᵐ[P.map Y] fun y =>
      multivariateGaussian ((∫ ω, X ω ∂P) + matrixBlockMap A (y - ∫ ω, Y ω ∂P))
        (vectorCovariance P X - A * (crossCovariance P X Y)ᵀ) := by
  let L := matrixBlockMap A
  let R : Ω → EuclideanSpace ℝ (Fin d) := fun ω => X ω - L (Y ω)
  have hR : Measurable R := hX.sub (L.measurable.comp hY)
  have hg : HasGaussianLaw (fun ω => (R ω, Y ω)) P :=
    hXY.map_fun (((ContinuousLinearMap.fst ℝ _ _) -
      L.comp (ContinuousLinearMap.snd ℝ _ _)).prod (ContinuousLinearMap.snd ℝ _ _))
  have hRp := hg.fst.memLp_two
  have hYp := hXY.snd.memLp_two
  have hXp := hXY.fst.memLp_two
  have hLY := (hXY.snd.map_fun L).memLp_two
  have hc (i : Fin d) (j : Fin e) :
      cov[fun ω => R ω i, fun ω => Y ω j; P] = 0 := by
    change cov[fun ω => X ω i - L (Y ω) i, fun ω => Y ω j; P] = 0
    rw [covariance_fun_sub_left (hXp.eval_piLp i) (hLY.eval_piLp i) (hYp.eval_piLp j)]
    change cov[fun ω => X ω i, fun ω => Y ω j; P] -
      cov[fun ω => ∑ k, A i k * Y ω k, fun ω => Y ω j; P] = 0
    rw [covariance_fun_sum_left (fun k => (hYp.eval_piLp k).const_mul _) (hYp.eval_piLp j)]
    simp_rw [covariance_const_mul_left]
    have hh := congrFun (congrFun hA i) j
    change (∑ k, A i k * cov[fun ω => Y ω k, fun ω => Y ω j; P]) =
      cov[fun ω => X ω i, fun ω => Y ω j; P] at hh
    rw [hh, sub_self]
  have hind : IndepFun R Y P := by
    let ed := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)
    let ee := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin e => ℝ)
    have hp := hg.map_equiv (ed.prodCongr ee)
    have hi := hp.indepFun_of_covariance_eval hc
    exact hi.comp ed.symm.continuous.measurable ee.symm.continuous.measurable
  have hcov : vectorCovariance P R =
      vectorCovariance P X - A * (crossCovariance P X Y)ᵀ := by
    ext i j
    change cov[fun ω => R ω i, fun ω => X ω j - L (Y ω) j; P] =
      cov[fun ω => X ω i, fun ω => X ω j; P] -
        ∑ k, A i k * cov[fun ω => X ω j, fun ω => Y ω k; P]
    rw [covariance_fun_sub_right (hRp.eval_piLp i) (hXp.eval_piLp j) (hLY.eval_piLp j)]
    change cov[fun ω => R ω i, fun ω => X ω j; P] -
      cov[fun ω => R ω i, fun ω => ∑ k, A j k * Y ω k; P] = _
    rw [covariance_fun_sum_right (fun k => (hYp.eval_piLp k).const_mul _) (hRp.eval_piLp i)]
    simp_rw [covariance_const_mul_right, hc, mul_zero, Finset.sum_const_zero, sub_zero]
    change cov[fun ω => X ω i - L (Y ω) i, fun ω => X ω j; P] = _
    rw [covariance_fun_sub_left (hXp.eval_piLp i) (hLY.eval_piLp i) (hXp.eval_piLp j)]
    change _ - cov[fun ω => ∑ k, A i k * Y ω k, fun ω => X ω j; P] = _
    rw [covariance_fun_sum_left (fun k => (hYp.eval_piLp k).const_mul _) (hXp.eval_piLp j)]
    simp_rw [covariance_const_mul_left]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [covariance_comm]
  have hmean : (∫ ω, R ω ∂P) = (∫ ω, X ω ∂P) - L (∫ ω, Y ω ∂P) := by
    rw [show R = (fun ω => X ω - L (Y ω)) from rfl,
      integral_sub hXY.fst.integrable (hXY.snd.map_fun L).integrable,
      L.integral_comp_comm hXY.snd.integrable]
  have hh := condDistrib_independent_noise P hY hR hind.symm
    (fun z => z.2 + L z.1) (by fun_prop)
  change condDistrib (fun ω => R ω + L (Y ω)) Y P =ᵐ[P.map Y] _ at hh
  have heq : (fun ω => R ω + L (Y ω)) = X := by funext ω; dsimp [R]; abel
  rw [heq] at hh
  filter_upwards [hh] with y hy
  rw [hy]
  change (P.map R).map (fun r => r + L y) = _
  rw [gaussian_vector_law P hg.fst, hmean, hcov, multivariateGaussian_map_add]
  congr 1
  rw [map_sub]
  abel

/-- L1: the full Gaussian block conditional distribution, with its
Schur-complement covariance. Positive definiteness of the conditioning block
justifies its inverse; the residual covariance may be singular. -/
theorem gaussian_block_conditional_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d e : ℕ} {X : Ω → EuclideanSpace ℝ (Fin d)}
    {Y : Ω → EuclideanSpace ℝ (Fin e)} (hX : Measurable X) (hY : Measurable Y)
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hS : (vectorCovariance P Y).PosDef) :
    condDistrib X Y P =ᵐ[P.map Y] fun y =>
      multivariateGaussian ((∫ ω, X ω ∂P) +
        matrixBlockMap (crossCovariance P X Y * (vectorCovariance P Y)⁻¹)
          (y - ∫ ω, Y ω ∂P))
        (vectorCovariance P X -
          crossCovariance P X Y * (vectorCovariance P Y)⁻¹ * (crossCovariance P X Y)ᵀ) := by
  apply gaussian_block_conditional_law_of_regression_matrix P hX hY hXY
  letI := hS.isUnit.invertible
  exact Matrix.nonsing_inv_mul_cancel_right _ _ (Matrix.isUnit_det_of_invertible _)

end LectureNotes
