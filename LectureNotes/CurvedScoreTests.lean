import LectureNotes.ConstrainedScoreTests
import LectureNotes.CurvedWilks

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped Topology InnerProductSpace MatrixProbability Matrix.Norms.Elementwise

/-- The ambient score at a consistent curved-null root converges to the
normal-space Gaussian component. The chart score is the actual adjoint
chart derivative applied to the ambient score. Identity-information coordinates
and a supplied smooth local chart are explicit, as in the curved Wilks result. -/
theorem curved_constraint_score_limit {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℕ} (K₀ : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (chart : K₀ → EuclideanSpace ℝ (Fin d))
    (J : K₀ → K₀ →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hchart : Continuous chart) (hJ : Continuous J)
    (hchart0 : chart 0 = 0) (hJ0 : J 0 = K₀.subtypeL)
    (score : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℕ → Ω → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (K : ℕ → Ω → K₀ → K₀ →L[ℝ] K₀)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (U : ℕ → Ω → K₀)
    (B C : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (D' : Set K₀)
    (hD : Convex ℝ D) (hD' : Convex ℝ D') (M N : ℝ)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ D) (h0' : (0 : K₀) ∈ D')
    (hmap : MapsTo chart D' D)
    (hjd : ∀ u ∈ D', HasFDerivAt chart (J u) u)
    (hTin : ∀ n ω, T n ω ∈ D) (hUin : ∀ n ω, U n ω ∈ D')
    (hTm : ∀ n, Measurable (T n)) (hUm : ∀ n, Measurable (U n))
    (hsm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => score n p.1 p.2))
    (hB0 : ∀ n ω, 0 ≤ B n ω) (hC0 : ∀ n ω, 0 ≤ C n ω)
    (hd : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hd' : ∀ n ω u, u ∈ D' → HasFDerivWithinAt
      (fun a => (J a).adjoint (score n ω (chart a))) (K n ω u) D' u)
    (hL : ∀ n ω x, x ∈ D → ‖L n ω x - L n ω 0‖ ≤ B n ω * ‖x - 0‖)
    (hK : ∀ n ω u, u ∈ D' → ‖K n ω u - K n ω 0‖ ≤ C n ω * ‖u - 0‖)
    (hroot : ∀ n ω, score n ω (T n ω) = 0)
    (hroot' : ∀ n ω, (J (U n ω)).adjoint (score n ω (chart (U n ω))) = 0)
    (hT : TendstoInMeasure P T atTop (fun _ => 0))
    (hU : TendstoInMeasure P U atTop (fun _ => 0))
    (hB : TendstoInMeasure P B atTop (fun _ => M))
    (hC : TendstoInMeasure P C atTop (fun _ => N))
    (hc : TendstoInMeasure P (fun n ω => L n ω 0) atTop
      (fun _ => -(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))))
    (hc' : TendstoInMeasure P (fun n ω => K n ω 0) atTop
      (fun _ => -(ContinuousLinearMap.id ℝ K₀)))
    {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    (hs : TendstoInDistribution (fun n ω => rate n • score n ω 0) atTop Z (fun _ => P) Q) :
    TendstoInDistribution (fun n ω => rate n • score n ω (chart (U n ω))) atTop
      (fun ω => Z ω - K₀.starProjection (Z ω)) (fun _ => P) Q := by
  let I := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))
  let restrictedScore n ω u := (J u).adjoint (score n ω (chart u))
  let Uₑ : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun n ω => chart (U n ω)
  have hUₑm n : Measurable (Uₑ n) := hchart.measurable.comp (hUm n)
  have hUₑ : TendstoInMeasure P Uₑ atTop (fun _ => 0) := by
    simpa only [hchart0] using! continuous_mapping_probability_const_metric hchart.continuousAt hU
  have hrm n : Measurable (fun p : Ω × K₀ => restrictedScore n p.1 p.2) := by
    have hss := (hsm n).comp (measurable_fst.prodMk (hchart.measurable.comp measurable_snd))
    have ha : Continuous (fun u => (J u).adjoint) := ContinuousLinearMap.adjoint.continuous.comp hJ
    have hev : Continuous (fun p :
        (EuclideanSpace ℝ (Fin d) →L[ℝ] K₀) × EuclideanSpace ℝ (Fin d) => p.1 p.2) := by fun_prop
    exact hev.measurable.comp ((ha.measurable.comp measurable_snd).prodMk hss)
  have hlink n ω : restrictedScore n ω 0 = K₀.orthogonalProjectionOnto (score n ω 0) := by
    simp only [restrictedScore, hchart0, hJ0, Submodule.adjoint_subtypeL]
  have hpair := consistent_joint_vector_score_root_limit score L restrictedScore K T U B C rate
    D D' hD hD' 0 0 (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin d)))
    (ContinuousLinearEquiv.refl ℝ K₀) K₀.orthogonalProjectionOnto M N h0 h0'
    hTin hUin hTm hUm hsm hrm hB0 hC0 hd hd' hL hK hroot hroot' hlink hT hU hB hC hc hc' hs
  let A : (EuclideanSpace ℝ (Fin d) × K₀) →L[ℝ]
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
    (ContinuousLinearMap.fst ℝ _ _).prod (K₀.subtypeL.comp (ContinuousLinearMap.snd ℝ _ _))
  have hdg : HasFDerivAt
      (fun p : EuclideanSpace ℝ (Fin d) × K₀ => (p.1, chart p.2)) A (0, 0) := by
    have hj0 : HasFDerivAt chart K₀.subtypeL 0 := by simpa only [hJ0] using hjd 0 h0'
    exact (hasFDerivAt_fst (𝕜 := ℝ)).prodMk (hj0.comp (0, 0) hasFDerivAt_snd)
  have hJoint : TendstoInDistribution
      (fun n ω => rate n • ((T n ω, U n ω) - (0, 0))) atTop
      (fun ω => (Z ω, K₀.orthogonalProjectionOnto (Z ω))) (fun _ => P) Q := by
    simpa only [sub_zero, ContinuousLinearEquiv.refl_apply, Prod.smul_mk, Prod.mk_zero_zero] using! hpair
  have hDelta := normed_delta_method
    (fun n => ((hTm n).prodMk (hUm n)).aemeasurable) (probability_product_const hT hU)
    hJoint (continuous_fst.prodMk (hchart.comp continuous_snd)) hdg
  have hE : TendstoInDistribution (fun n ω => (rate n • T n ω, rate n • Uₑ n ω))
      atTop (fun ω => (Z ω, K₀.starProjection (Z ω))) (fun _ => P) Q := by
    simpa [hchart0, A, Uₑ, Function.comp_def, Pi.sub_apply, Prod.smul_mk] using! hDelta
  obtain ⟨hAT, hATm⟩ := effective_vector_curvature_regular score L T B D hD 0
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin d))) M h0 hTin hTm hsm hB0 hd hL hT hB hc
  obtain ⟨hAU, hAUm⟩ := effective_vector_curvature_regular score L Uₑ B D hD 0
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin d))) M h0
    (fun n ω => hmap (hUin n ω)) hUₑm hsm hB0 hd hL hUₑ hB hc
  have h := hE.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      ((EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) ×
       (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))) =>
        p.2.1 p.1.1 - p.2.2 p.1.2) (by fun_prop)
    (probability_product_const hAT hAU) (fun n => (hATm n).prodMk (hAUm n))
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl)) h
  intro n
  apply ae_of_all
  intro ω
  change effectiveVectorCurvature (score n ω) 0 (T n ω) I (rate n • T n ω) -
    effectiveVectorCurvature (score n ω) 0 (Uₑ n ω) I (rate n • Uₑ n ω) = _
  have ht := effectiveVectorCurvature_identity (score n ω) 0 (T n ω) I
  have hu := effectiveVectorCurvature_identity (score n ω) 0 (Uₑ n ω) I
  simp only [sub_zero, hroot] at ht hu
  rw [map_smul, map_smul, ht, hu, ← smul_sub]
  congr 1
  abel


/-- Estimated-information LM calibration at the actual curved-null score
root. The normal-space limit and degrees of freedom are derived from the
same original score CLT and explicit chart/derivative conditions. -/
theorem curved_constraint_score_test_limit {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℕ} (K₀ : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (chart : K₀ → EuclideanSpace ℝ (Fin d))
    (J : K₀ → K₀ →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hchart : Continuous chart) (hJ : Continuous J)
    (hchart0 : chart 0 = 0) (hJ0 : J 0 = K₀.subtypeL)
    (score : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℕ → Ω → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (K : ℕ → Ω → K₀ → K₀ →L[ℝ] K₀)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (U : ℕ → Ω → K₀)
    (B C : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (D' : Set K₀)
    (hD : Convex ℝ D) (hD' : Convex ℝ D') (M N : ℝ)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ D) (h0' : (0 : K₀) ∈ D')
    (hmap : MapsTo chart D' D)
    (hjd : ∀ u ∈ D', HasFDerivAt chart (J u) u)
    (hTin : ∀ n ω, T n ω ∈ D) (hUin : ∀ n ω, U n ω ∈ D')
    (hTm : ∀ n, Measurable (T n)) (hUm : ∀ n, Measurable (U n))
    (hsm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => score n p.1 p.2))
    (hB0 : ∀ n ω, 0 ≤ B n ω) (hC0 : ∀ n ω, 0 ≤ C n ω)
    (hd : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hd' : ∀ n ω u, u ∈ D' → HasFDerivWithinAt
      (fun a => (J a).adjoint (score n ω (chart a))) (K n ω u) D' u)
    (hL : ∀ n ω x, x ∈ D → ‖L n ω x - L n ω 0‖ ≤ B n ω * ‖x - 0‖)
    (hK : ∀ n ω u, u ∈ D' → ‖K n ω u - K n ω 0‖ ≤ C n ω * ‖u - 0‖)
    (hroot : ∀ n ω, score n ω (T n ω) = 0)
    (hroot' : ∀ n ω, (J (U n ω)).adjoint (score n ω (chart (U n ω))) = 0)
    (hT : TendstoInMeasure P T atTop (fun _ => 0))
    (hU : TendstoInMeasure P U atTop (fun _ => 0))
    (hB : TendstoInMeasure P B atTop (fun _ => M))
    (hC : TendstoInMeasure P C atTop (fun _ => N))
    (hc : TendstoInMeasure P (fun n ω => L n ω 0) atTop
      (fun _ => -(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))))
    (hc' : TendstoInMeasure P (fun n ω => K n ω 0) atTop
      (fun _ => -(ContinuousLinearMap.id ℝ K₀)))
    {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    (hs : TendstoInDistribution (fun n ω => rate n • score n ω 0) atTop Z (fun _ => P) Q)
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin d))) Q)
    {Ihat : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ}
    (hI : TendstoInMeasure P Ihat atTop (fun _ => 1))
    (hIm : ∀ n, AEMeasurable (Ihat n) P) :
    ConvergesInDistribution P Q
      (fun n ω => rate n ^ 2 * matrixQuadratic (Ihat n ω)⁻¹ (score n ω (chart (U n ω))))
      (fun ω => ‖Z ω - K₀.starProjection (Z ω)‖^2) ∧
    HasLaw (fun ω => ‖Z ω - K₀.starProjection (Z ω)‖^2)
      (chiSquared (d - Module.finrank ℝ K₀)) Q := by
  have hscore := curved_constraint_score_limit K₀ chart J hchart hJ hchart0 hJ0 score L K T U B C rate D D' hD hD' M N
    h0 h0' hmap hjd hTin hUin hTm hUm hsm hB0 hC0 hd hd' hL hK hroot hroot'
    hT hU hB hC hc hc' hs
  simpa only [matrixQuadratic_smul] using!
    projected_score_statistic_limit K₀ hscore hZ hI hIm

/-- The curved-null score test has the nominal limiting acceptance
probability at every interior chi-square quantile and positive codimension. -/
theorem curved_constraint_score_test_coverage {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℕ} (K₀ : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (chart : K₀ → EuclideanSpace ℝ (Fin d))
    (J : K₀ → K₀ →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hchart : Continuous chart) (hJ : Continuous J)
    (hchart0 : chart 0 = 0) (hJ0 : J 0 = K₀.subtypeL)
    (score : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℕ → Ω → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (K : ℕ → Ω → K₀ → K₀ →L[ℝ] K₀)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (U : ℕ → Ω → K₀)
    (B C : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (D' : Set K₀)
    (hD : Convex ℝ D) (hD' : Convex ℝ D') (M N : ℝ)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ D) (h0' : (0 : K₀) ∈ D')
    (hmap : MapsTo chart D' D)
    (hjd : ∀ u ∈ D', HasFDerivAt chart (J u) u)
    (hTin : ∀ n ω, T n ω ∈ D) (hUin : ∀ n ω, U n ω ∈ D')
    (hTm : ∀ n, Measurable (T n)) (hUm : ∀ n, Measurable (U n))
    (hsm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => score n p.1 p.2))
    (hB0 : ∀ n ω, 0 ≤ B n ω) (hC0 : ∀ n ω, 0 ≤ C n ω)
    (hd : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hd' : ∀ n ω u, u ∈ D' → HasFDerivWithinAt
      (fun a => (J a).adjoint (score n ω (chart a))) (K n ω u) D' u)
    (hL : ∀ n ω x, x ∈ D → ‖L n ω x - L n ω 0‖ ≤ B n ω * ‖x - 0‖)
    (hK : ∀ n ω u, u ∈ D' → ‖K n ω u - K n ω 0‖ ≤ C n ω * ‖u - 0‖)
    (hroot : ∀ n ω, score n ω (T n ω) = 0)
    (hroot' : ∀ n ω, (J (U n ω)).adjoint (score n ω (chart (U n ω))) = 0)
    (hT : TendstoInMeasure P T atTop (fun _ => 0))
    (hU : TendstoInMeasure P U atTop (fun _ => 0))
    (hB : TendstoInMeasure P B atTop (fun _ => M))
    (hC : TendstoInMeasure P C atTop (fun _ => N))
    (hc : TendstoInMeasure P (fun n ω => L n ω 0) atTop
      (fun _ => -(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))))
    (hc' : TendstoInMeasure P (fun n ω => K n ω 0) atTop
      (fun _ => -(ContinuousLinearMap.id ℝ K₀)))
    {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    (hs : TendstoInDistribution (fun n ω => rate n • score n ω 0) atTop Z (fun _ => P) Q)
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin d))) Q)
    {Ihat : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ}
    (hI : TendstoInMeasure P Ihat atTop (fun _ => 1))
    (hIm : ∀ n, AEMeasurable (Ihat n) P)
    (hp : 0 < d - Module.finrank ℝ K₀) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω | rate n ^ 2 * matrixQuadratic (Ihat n ω)⁻¹
      (score n ω (chart (U n ω))) ≤ distributionQuantile (chiSquared (d - Module.finrank ℝ K₀)) q})
      atTop (𝓝 q) := by
  obtain ⟨hT', hL'⟩ := curved_constraint_score_test_limit K₀ chart J hchart hJ hchart0 hJ0 score L K T U B C rate D D' hD hD' M N
    h0 h0' hmap hjd hTin hUin hTm hUm hsm hB0 hC0 hd hd' hL hK hroot hroot'
    hT hU hB hC hc hc' hs hZ hI hIm
  exact chiSquared_weak_limit_coverage hp hT' hL' hq

end LectureNotes
