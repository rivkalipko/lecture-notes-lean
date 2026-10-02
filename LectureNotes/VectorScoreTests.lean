import LectureNotes.ConstrainedVectorMLE

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped Topology InnerProductSpace MatrixProbability Matrix.Norms.Elementwise

/-- The score at a consistent estimated parameter has its joint linearized
limit. The effective derivative and its convergence are derived from actual
Fréchet derivatives and a Lipschitz envelope, not postulated expansions. -/
theorem score_at_consistent_estimator_limit {Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (score : ℕ → Ω → E → E) (L : ℕ → Ω → E → E →L[ℝ] E)
    (U : ℕ → Ω → E) (B : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set E) (hD : Convex ℝ D) (θ : E) (H : E ≃L[ℝ] E) (M : ℝ)
    (hθ : θ ∈ D) (hUin : ∀ n ω, U n ω ∈ D)
    (hUm : ∀ n, Measurable (U n))
    (hsm : ∀ n, Measurable (fun p : Ω × E => score n p.1 p.2))
    (hB0 : ∀ n ω, 0 ≤ B n ω)
    (hd : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hL : ∀ n ω x, x ∈ D → ‖L n ω x - L n ω θ‖ ≤ B n ω * ‖x - θ‖)
    (hU : TendstoInMeasure P U atTop (fun _ => θ))
    (hB : TendstoInMeasure P B atTop (fun _ => M))
    (hc : TendstoInMeasure P (fun n ω => L n ω θ) atTop (fun _ => -H.toContinuousLinearMap))
    {Z W : Ω' → E}
    (hJoint : TendstoInDistribution
      (fun n ω => (rate n • score n ω θ, rate n • (U n ω - θ)))
      atTop (fun ω => (Z ω, W ω)) (fun _ => P) Q) :
    TendstoInDistribution (fun n ω => rate n • score n ω (U n ω))
      atTop (fun ω => Z ω - H (W ω)) (fun _ => P) Q := by
  obtain ⟨hA, hAm⟩ := effective_vector_curvature_regular score L U B D hD θ H M
    hθ hUin hUm hsm hB0 hd hL hU hB hc
  have h := hJoint.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : (E × E) × (E →L[ℝ] E) => p.1.1 - p.2 p.1.2)
    (by fun_prop) hA hAm
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl)) h
  intro n
  apply ae_of_all
  intro ω
  change rate n • score n ω θ -
    effectiveVectorCurvature (score n ω) θ (U n ω) H.toContinuousLinearMap
      (rate n • (U n ω - θ)) = _
  rw [map_smul, effectiveVectorCurvature_identity, ← smul_sub]
  congr 1
  abel

/-- The normal-space projected score has chi-square norm, with degrees of
freedom equal to the codimension of the null tangent space. -/
theorem normal_space_score_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} {Z : Ω → EuclideanSpace ℝ (Fin d)}
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin d))) P) :
    HasLaw (fun ω => ‖Z ω - K.starProjection (Z ω)‖^2)
      (chiSquared (d - Module.finrank ℝ K)) P := by
  have h := (stdGaussian_norm_sq (E := Kᗮ)).comp
    ((stdGaussian_orthogonalProjection Kᗮ).comp hZ)
  have hd : Module.finrank ℝ Kᗮ = d - Module.finrank ℝ K := by
    have hh : Module.finrank ℝ K + Module.finrank ℝ Kᗮ = d := by
      simpa using K.finrank_add_finrank_orthogonal
    omega
  have he (ω : Ω) : ‖Kᗮ.orthogonalProjectionOnto (Z ω)‖^2 =
      ‖Z ω - K.starProjection (Z ω)‖^2 := by
    change ‖Kᗮ.starProjection (Z ω)‖^2 = _
    rw [K.starProjection_orthogonal_val]
  change HasLaw (fun ω => ‖Kᗮ.orthogonalProjectionOnto (Z ω)‖^2)
    (chiSquared (Module.finrank ℝ Kᗮ)) P at h
  simpa only [hd, he] using! h

set_option backward.isDefEq.respectTransparency false in
/-- Estimated inverse information can be used with a singular projected
score limit. The ambient information is positive definite; the chi-square
degrees of freedom are the projection rank, not the ambient dimension. -/
theorem projected_score_statistic_limit {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℕ} (K : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    {S : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    (hS : TendstoInDistribution S atTop
      (fun ω => Z ω - K.starProjection (Z ω)) (fun _ => P) Q)
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin d))) Q)
    {Ihat : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ}
    (hI : TendstoInMeasure P Ihat atTop (fun _ => 1))
    (hIm : ∀ n, AEMeasurable (Ihat n) P) :
    ConvergesInDistribution P Q (fun n ω => matrixQuadratic (Ihat n ω)⁻¹ (S n ω))
      (fun ω => ‖Z ω - K.starProjection (Z ω)‖^2) ∧
    HasLaw (fun ω => ‖Z ω - K.starProjection (Z ω)‖^2)
      (chiSquared (d - Module.finrank ℝ K)) Q := by
  refine ⟨?_, normal_space_score_law K hZ⟩
  have hi := covariance_inverse_consistency (by simp : (1 : Matrix (Fin d) (Fin d) ℝ).det ≠ 0) hI
  have h := hS.continuous_comp_prodMk_of_tendstoInMeasure_const
    (mE' := MatrixProbability.matrixMeasurableSpace)
    (g := fun p : EuclideanSpace ℝ (Fin d) × Matrix (Fin d) (Fin d) ℝ =>
      matrixQuadratic p.2 p.1) continuous_matrixQuadratic hi
    (fun n => measurable_matrix_inverse.comp_aemeasurable (hIm n))
  simpa only [inv_one, matrixQuadratic, map_one, one_apply_eq_self,
    real_inner_self_eq_norm_sq] using! h

end LectureNotes
