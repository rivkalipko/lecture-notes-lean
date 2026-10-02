import LectureNotes.VectorScoreTests

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped Topology InnerProductSpace MatrixProbability Matrix.Norms.Elementwise

/-- The projected score limit for a linear constrained estimator, in
identity-information coordinates. Only the original score CLT is supplied;
the restricted root limit and the score evaluated at that root are derived. -/
theorem linear_constraint_score_limit {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℕ} (K₀ : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (score : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℕ → Ω → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (restrictedScore : ℕ → Ω → K₀ → K₀) (K : ℕ → Ω → K₀ → K₀ →L[ℝ] K₀)
    (U : ℕ → Ω → K₀) (B C : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (D' : Set K₀)
    (hD : Convex ℝ D) (hD' : Convex ℝ D') (M N : ℝ)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ D) (h0' : (0 : K₀) ∈ D')
    (hUinD : ∀ n ω, (U n ω : EuclideanSpace ℝ (Fin d)) ∈ D)
    (hUin : ∀ n ω, U n ω ∈ D') (hUm : ∀ n, Measurable (U n))
    (hsm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => score n p.1 p.2))
    (hrm : ∀ n, Measurable (fun p : Ω × K₀ => restrictedScore n p.1 p.2))
    (hB0 : ∀ n ω, 0 ≤ B n ω) (hC0 : ∀ n ω, 0 ≤ C n ω)
    (hd : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hd' : ∀ n ω x, x ∈ D' → HasFDerivWithinAt (restrictedScore n ω) (K n ω x) D' x)
    (hL : ∀ n ω x, x ∈ D → ‖L n ω x - L n ω 0‖ ≤ B n ω * ‖x - 0‖)
    (hK : ∀ n ω x, x ∈ D' → ‖K n ω x - K n ω 0‖ ≤ C n ω * ‖x - 0‖)
    (hroot : ∀ n ω, restrictedScore n ω (U n ω) = 0)
    (hlink : ∀ n ω x, restrictedScore n ω x = K₀.orthogonalProjectionOnto (score n ω x))
    (hU : TendstoInMeasure P U atTop (fun _ => 0))
    (hB : TendstoInMeasure P B atTop (fun _ => M))
    (hC : TendstoInMeasure P C atTop (fun _ => N))
    (hc : TendstoInMeasure P (fun n ω => L n ω 0) atTop
      (fun _ => -(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))))
    (hc' : TendstoInMeasure P (fun n ω => K n ω 0) atTop
      (fun _ => -(ContinuousLinearMap.id ℝ K₀)))
    {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    (hs : TendstoInDistribution (fun n ω => rate n • score n ω 0) atTop Z (fun _ => P) Q) :
    TendstoInDistribution (fun n ω => rate n • score n ω (U n ω)) atTop
      (fun ω => Z ω - K₀.starProjection (Z ω)) (fun _ => P) Q := by
  let Uₑ : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun n ω => U n ω
  have hUₑm n : Measurable (Uₑ n) := continuous_subtype_val.measurable.comp (hUm n)
  have hUₑ : TendstoInMeasure P Uₑ atTop (fun _ => 0) := by
    simpa only [Submodule.coe_zero] using!
      continuous_mapping_probability_const_metric
        (g := fun u : K₀ => (u : EuclideanSpace ℝ (Fin d))) (by fun_prop) hU
  obtain ⟨hA, hAm⟩ := effective_vector_curvature_regular restrictedScore K U C D' hD' 0
    (ContinuousLinearEquiv.refl ℝ K₀) N h0' hUin hUm hrm hC0 hd' hK hU hC hc'
  have hI : TendstoInMeasure P
      (fun (_n : ℕ) (_ω : Ω) => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) atTop
      (fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ (fun _ => tendsto_const_nhds))
  have hpair := paired_vector_score_root_limit
    (V := fun n ω => rate n • score n ω 0)
    (W := fun n ω => rate n • (U n ω - 0)) K₀.orthogonalProjectionOnto
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin d)))
    (ContinuousLinearEquiv.refl ℝ K₀) hs hI hA
    (fun _ => aemeasurable_const) hAm hs.forall_aemeasurable
    (fun n => (show Measurable (fun ω => rate n • (U n ω - 0)) by fun_prop).aemeasurable)
    (fun _ => ae_of_all _ (fun _ => rfl))
    (fun n => ae_of_all _ (fun ω => by
      change effectiveVectorCurvature (restrictedScore n ω) 0 (U n ω)
        (ContinuousLinearMap.id ℝ K₀) (rate n • (U n ω - 0)) =
          K₀.orthogonalProjectionOnto (rate n • score n ω 0)
      rw [map_smul, effectiveVectorCurvature_identity, hroot, sub_zero, hlink, map_smul]
      rfl))
  have hJoint : TendstoInDistribution
      (fun n ω => (rate n • score n ω 0, rate n • (Uₑ n ω - 0)))
      atTop (fun ω => (Z ω, K₀.starProjection (Z ω))) (fun _ => P) Q := by
    have hh := hpair.continuous_comp
      (g := fun p : EuclideanSpace ℝ (Fin d) × K₀ => (p.1, (p.2 : EuclideanSpace ℝ (Fin d))))
      (by fun_prop)
    simpa only [sub_zero, ContinuousLinearEquiv.refl_apply, Submodule.coe_smul] using! hh
  simpa only [ContinuousLinearEquiv.refl_apply] using!
    score_at_consistent_estimator_limit score L Uₑ B rate D hD 0
      (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin d))) M h0 hUinD hUₑm hsm hB0
      hd hL hUₑ hB hc hJoint


/-- An atomless positive-degree chi-square limit calibrates every interior
quantile. This concerns asymptotic rather than exact finite-sample size. -/
theorem chiSquared_weak_limit_coverage {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {p : ℕ} (hp : 0 < p)
    (hT : ConvergesInDistribution P Q T Z) (hZ : HasLaw Z (chiSquared p) Q)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω | T n ω ≤ distributionQuantile (chiSquared p) q})
      atTop (𝓝 q) := by
  have := chiSquared_nullSingletonClass hp
  have hb : Q.map Z (frontier (Iic (distributionQuantile (chiSquared p) q))) = 0 := by
    rw [hZ.map_eq, frontier_Iic]
    exact measure_singleton _
  have h := asymptotic_rejection_probability hT
    (Iic (distributionQuantile (chiSquared p) q)) measurableSet_Iic hb
  have he := hZ.measureReal_eq (p := fun t => t ≤ distributionQuantile (chiSquared p) q)
    measurableSet_Iic
  simp only [Set.mem_Iic] at h
  rw [he] at h
  change Tendsto _ atTop (𝓝 ((chiSquared p).real (Iic (distributionQuantile (chiSquared p) q)))) at h
  rw [distributionQuantile_exact (chiSquared p) q hq] at h
  exact h

/-- L10's estimated-information score statistic for an actual restricted
root. For average log-likelihood scores and rate=√n, this is precisely
S_total' I_hat⁻¹ S_total / n. Codimension gives its chi-square degrees of freedom. -/
theorem linear_constraint_score_test_limit {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℕ} (K₀ : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (score : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℕ → Ω → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (restrictedScore : ℕ → Ω → K₀ → K₀) (K : ℕ → Ω → K₀ → K₀ →L[ℝ] K₀)
    (U : ℕ → Ω → K₀) (B C : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (D' : Set K₀)
    (hD : Convex ℝ D) (hD' : Convex ℝ D') (M N : ℝ)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ D) (h0' : (0 : K₀) ∈ D')
    (hUinD : ∀ n ω, (U n ω : EuclideanSpace ℝ (Fin d)) ∈ D)
    (hUin : ∀ n ω, U n ω ∈ D') (hUm : ∀ n, Measurable (U n))
    (hsm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => score n p.1 p.2))
    (hrm : ∀ n, Measurable (fun p : Ω × K₀ => restrictedScore n p.1 p.2))
    (hB0 : ∀ n ω, 0 ≤ B n ω) (hC0 : ∀ n ω, 0 ≤ C n ω)
    (hd : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hd' : ∀ n ω x, x ∈ D' → HasFDerivWithinAt (restrictedScore n ω) (K n ω x) D' x)
    (hL : ∀ n ω x, x ∈ D → ‖L n ω x - L n ω 0‖ ≤ B n ω * ‖x - 0‖)
    (hK : ∀ n ω x, x ∈ D' → ‖K n ω x - K n ω 0‖ ≤ C n ω * ‖x - 0‖)
    (hroot : ∀ n ω, restrictedScore n ω (U n ω) = 0)
    (hlink : ∀ n ω x, restrictedScore n ω x = K₀.orthogonalProjectionOnto (score n ω x))
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
      (fun n ω => rate n ^ 2 * matrixQuadratic (Ihat n ω)⁻¹ (score n ω (U n ω)))
      (fun ω => ‖Z ω - K₀.starProjection (Z ω)‖^2) ∧
    HasLaw (fun ω => ‖Z ω - K₀.starProjection (Z ω)‖^2)
      (chiSquared (d - Module.finrank ℝ K₀)) Q := by
  have hscore := linear_constraint_score_limit K₀ score L restrictedScore K U B C rate D D' hD hD' M N
    h0 h0' hUinD hUin hUm hsm hrm hB0 hC0 hd hd' hL hK hroot hlink hU hB hC hc hc' hs
  simpa only [matrixQuadratic_smul] using!
    projected_score_statistic_limit K₀ hscore hZ hI hIm

/-- Positive codimension ensures that the actual restricted score test's
chi-square cutoff has its nominal limiting acceptance probability. -/
theorem linear_constraint_score_test_coverage {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℕ} (K₀ : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (score : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℕ → Ω → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (restrictedScore : ℕ → Ω → K₀ → K₀) (K : ℕ → Ω → K₀ → K₀ →L[ℝ] K₀)
    (U : ℕ → Ω → K₀) (B C : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (D' : Set K₀)
    (hD : Convex ℝ D) (hD' : Convex ℝ D') (M N : ℝ)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ D) (h0' : (0 : K₀) ∈ D')
    (hUinD : ∀ n ω, (U n ω : EuclideanSpace ℝ (Fin d)) ∈ D)
    (hUin : ∀ n ω, U n ω ∈ D') (hUm : ∀ n, Measurable (U n))
    (hsm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => score n p.1 p.2))
    (hrm : ∀ n, Measurable (fun p : Ω × K₀ => restrictedScore n p.1 p.2))
    (hB0 : ∀ n ω, 0 ≤ B n ω) (hC0 : ∀ n ω, 0 ≤ C n ω)
    (hd : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hd' : ∀ n ω x, x ∈ D' → HasFDerivWithinAt (restrictedScore n ω) (K n ω x) D' x)
    (hL : ∀ n ω x, x ∈ D → ‖L n ω x - L n ω 0‖ ≤ B n ω * ‖x - 0‖)
    (hK : ∀ n ω x, x ∈ D' → ‖K n ω x - K n ω 0‖ ≤ C n ω * ‖x - 0‖)
    (hroot : ∀ n ω, restrictedScore n ω (U n ω) = 0)
    (hlink : ∀ n ω x, restrictedScore n ω x = K₀.orthogonalProjectionOnto (score n ω x))
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
      (score n ω (U n ω)) ≤ distributionQuantile (chiSquared (d - Module.finrank ℝ K₀)) q})
      atTop (𝓝 q) := by
  obtain ⟨hT, hL⟩ := linear_constraint_score_test_limit K₀ score L restrictedScore K U B C rate D D' hD hD' M N
    h0 h0' hUinD hUin hUm hsm hrm hB0 hC0 hd hd' hL hK hroot hlink hU hB hC hc hc' hs hZ hI hIm
  exact chiSquared_weak_limit_coverage hp hT hL hq

end LectureNotes
