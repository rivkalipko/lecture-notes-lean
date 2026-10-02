import LectureNotes.VectorWilks
import LectureNotes.VectorScoreAsymptotics
import Mathlib.Analysis.Normed.Operator.Prod

set_option autoImplicit false

/-! Joint full-model and restricted-model estimating equations. Both roots
are driven by one score limit, so their asymptotic dependence is retained. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology InnerProductSpace

variable {Ω Ω' E F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- Joint root asymptotics from two actual derivative fields and one common
score limit. A restricted score is a fixed linear image at the true parameter. -/
theorem consistent_joint_vector_score_root_limit
    (score : ℕ → Ω → E → E) (L : ℕ → Ω → E → E →L[ℝ] E)
    (restrictedScore : ℕ → Ω → F → F) (K : ℕ → Ω → F → F →L[ℝ] F)
    (T : ℕ → Ω → E) (U : ℕ → Ω → F) (B C : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set E) (D' : Set F) (hD : Convex ℝ D) (hD' : Convex ℝ D')
    (θ : E) (φ : F) (H : E ≃L[ℝ] E) (G : F ≃L[ℝ] F) (R : E →L[ℝ] F) (M N : ℝ)
    (hθ : θ ∈ D) (hφ : φ ∈ D')
    (hTin : ∀ n ω, T n ω ∈ D) (hUin : ∀ n ω, U n ω ∈ D')
    (hTm : ∀ n, Measurable (T n)) (hUm : ∀ n, Measurable (U n))
    (hsm : ∀ n, Measurable (fun p : Ω × E => score n p.1 p.2))
    (hrm : ∀ n, Measurable (fun p : Ω × F => restrictedScore n p.1 p.2))
    (hB0 : ∀ n ω, 0 ≤ B n ω) (hC0 : ∀ n ω, 0 ≤ C n ω)
    (hd : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hd' : ∀ n ω x, x ∈ D' → HasFDerivWithinAt (restrictedScore n ω) (K n ω x) D' x)
    (hL : ∀ n ω x, x ∈ D → ‖L n ω x - L n ω θ‖ ≤ B n ω * ‖x - θ‖)
    (hK : ∀ n ω x, x ∈ D' → ‖K n ω x - K n ω φ‖ ≤ C n ω * ‖x - φ‖)
    (hroot : ∀ n ω, score n ω (T n ω) = 0)
    (hroot' : ∀ n ω, restrictedScore n ω (U n ω) = 0)
    (hlink : ∀ n ω, restrictedScore n ω φ = R (score n ω θ))
    (hT : TendstoInMeasure P T atTop (fun _ => θ))
    (hU : TendstoInMeasure P U atTop (fun _ => φ))
    (hB : TendstoInMeasure P B atTop (fun _ => M))
    (hC : TendstoInMeasure P C atTop (fun _ => N))
    (hc : TendstoInMeasure P (fun n ω => L n ω θ) atTop (fun _ => -H.toContinuousLinearMap))
    (hc' : TendstoInMeasure P (fun n ω => K n ω φ) atTop (fun _ => -G.toContinuousLinearMap))
    {Z : Ω' → E}
    (hs : TendstoInDistribution (fun n ω => rate n • score n ω θ) atTop Z (fun _ => P) Q) :
    TendstoInDistribution (fun n ω => (rate n • (T n ω - θ), rate n • (U n ω - φ)))
      atTop (fun ω => (H.symm (Z ω), G.symm (R (Z ω)))) (fun _ => P) Q := by
  obtain ⟨hA, hAm⟩ := effective_vector_curvature_regular score L T B D hD θ H M
    hθ hTin hTm hsm hB0 hd hL hT hB hc
  obtain ⟨hK', hKm⟩ := effective_vector_curvature_regular restrictedScore K U C D' hD' φ G N
    hφ hUin hUm hrm hC0 hd' hK hU hC hc'
  apply paired_vector_score_root_limit R H G hs hA hK' hAm hKm
    (fun n => (measurable_const.smul ((hTm n).sub_const θ)).aemeasurable)
    (fun n => (measurable_const.smul ((hUm n).sub_const φ)).aemeasurable)
  · intro n
    apply ae_of_all
    intro ω
    change effectiveVectorCurvature (score n ω) θ (T n ω) H.toContinuousLinearMap
      (rate n • (T n ω - θ)) = rate n • score n ω θ
    rw [map_smul, effectiveVectorCurvature_identity, hroot, sub_zero]
  · intro n
    apply ae_of_all
    intro ω
    change effectiveVectorCurvature (restrictedScore n ω) φ (U n ω) G.toContinuousLinearMap
      (rate n • (U n ω - φ)) = R (rate n • score n ω θ)
    rw [map_smul, effectiveVectorCurvature_identity, hroot', sub_zero, hlink, map_smul]

variable {d : ℕ}

/-- Wilks for a linear null subspace in coordinates with identity information.
The full/restricted joint root limit supplies the projected Gaussian pair.
The degrees of freedom are the codimension of the null subspace. -/
theorem linear_constraint_wilks_of_joint_limit
    (f : ℕ → Ω → EuclideanSpace ℝ (Fin d) → ℝ)
    (score : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℕ → Ω → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (T U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (B : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (hD : Convex ℝ D)
    (M : ℝ) (K₀ : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (_hUinK : ∀ n ω, U n ω ∈ K₀)
    (hTin : ∀ n ω, T n ω ∈ D) (hUin : ∀ n ω, U n ω ∈ D)
    (hTm : ∀ n, Measurable (T n)) (hUm : ∀ n, Measurable (U n))
    (hfm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => f n p.1 p.2))
    (hBm : ∀ n, AEMeasurable (B n) P)
    (hLm : ∀ n, AEMeasurable (fun ω => L n ω (U n ω)) P)
    (hB0 : ∀ n ω, 0 ≤ B n ω)
    (hf : ∀ n ω x, x ∈ D → HasFDerivWithinAt (f n ω) (innerSL ℝ (score n ω x)) D x)
    (hs : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hL : ∀ n ω x, x ∈ D → ‖L n ω x - L n ω (U n ω)‖ ≤ B n ω * ‖x - U n ω‖)
    (hroot : ∀ n ω, score n ω (T n ω) = 0)
    (hT : TendstoInMeasure P T atTop (fun _ => 0))
    (hU : TendstoInMeasure P U atTop (fun _ => 0))
    (hB : TendstoInMeasure P B atTop (fun _ => M))
    (hc : TendstoInMeasure P (fun n ω => L n ω (U n ω)) atTop
      (fun _ => -(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))))
    {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    (hJoint : TendstoInDistribution (fun n ω => (rate n • T n ω, rate n • U n ω))
      atTop (fun ω => (Z ω, K₀.starProjection (Z ω))) (fun _ => P) Q)
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin d))) Q) :
    ConvergesInDistribution P Q
      (fun n ω => 2 * rate n ^ 2 * (f n ω (T n ω) - f n ω (U n ω)))
      (fun ω => ‖Z ω - K₀.starProjection (Z ω)‖ ^ 2) ∧
    HasLaw (fun ω => ‖Z ω - K₀.starProjection (Z ω)‖ ^ 2)
      (chiSquared (d - Module.finrank ℝ K₀)) Q := by
  have hTU : TendstoInMeasure P (fun n ω => T n ω - U n ω) atTop (fun _ => 0) := by
    simpa using continuous_mapping_probability_const_metric
      (g := fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 - p.2)
      (by fun_prop) (probability_product_const hT hU)
  have hE : TendstoInDistribution (fun n ω => rate n • (T n ω - U n ω))
      atTop (fun ω => Z ω - K₀.starProjection (Z ω)) (fun _ => P) Q := by
    simpa only [smul_sub] using! hJoint.continuous_comp
      (g := fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 - p.2)
      (by fun_prop)
  refine ⟨?_, ?_⟩
  · simpa only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] using!
      vector_likelihood_ratio_limit f score L T U B rate D hD M
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) (by intros; rfl)
        hTin hUin hTm hUm hfm hBm hLm hB0 hf hs hL hroot hTU hB hc hE
  · have h := (stdGaussian_norm_sq (E := K₀ᗮ)).comp
      ((stdGaussian_orthogonalProjection K₀ᗮ).comp hZ)
    have hd : Module.finrank ℝ K₀ᗮ = d - Module.finrank ℝ K₀ := by
      have hdim : Module.finrank ℝ K₀ + Module.finrank ℝ K₀ᗮ = d := by
        simpa using K₀.finrank_add_finrank_orthogonal
      omega
    have he (ω : Ω') : ‖K₀ᗮ.orthogonalProjectionOnto (Z ω)‖ ^ 2 =
        ‖Z ω - K₀.starProjection (Z ω)‖ ^ 2 := by
      change ‖K₀ᗮ.starProjection (Z ω)‖ ^ 2 = _
      rw [K₀.starProjection_orthogonal_val]
    change HasLaw (fun ω => ‖K₀ᗮ.orthogonalProjectionOnto (Z ω)‖ ^ 2)
      (chiSquared (Module.finrank ℝ K₀ᗮ)) Q at h
    simpa only [hd, he] using! h

/-- Linear-subspace Wilks for consistent stationary roots, with the restricted
score equal to the actual projected full gradient. In identity-information
coordinates the common score CLT and derivative conditions imply the projected
joint limit and the likelihood expansion. Neither conclusion is a premise. -/
theorem linear_constraint_wilks_from_score_roots
    (K₀ : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (f : ℕ → Ω → EuclideanSpace ℝ (Fin d) → ℝ)
    (score : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (restrictedScore : ℕ → Ω → K₀ → K₀) (K : ℕ → Ω → K₀ → K₀ →L[ℝ] K₀)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (U : ℕ → Ω → K₀) (B C : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (D' : Set K₀) (hD : Convex ℝ D) (hD' : Convex ℝ D')
    (M N : ℝ) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ D) (h0' : (0 : K₀) ∈ D')
    (hUinD : ∀ n ω, (U n ω : EuclideanSpace ℝ (Fin d)) ∈ D)
    (hTin : ∀ n ω, T n ω ∈ D) (hUin : ∀ n ω, U n ω ∈ D')
    (hTm : ∀ n, Measurable (T n)) (hUm : ∀ n, Measurable (U n))
    (hfm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => f n p.1 p.2))
    (hLm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => L n p.1 p.2))
    (hBm : ∀ n, AEMeasurable (B n) P)
    (hsm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => score n p.1 p.2))
    (hrm : ∀ n, Measurable (fun p : Ω × K₀ => restrictedScore n p.1 p.2))
    (hB0 : ∀ n ω, 0 ≤ B n ω) (hC0 : ∀ n ω, 0 ≤ C n ω)
    (hf : ∀ n ω x, x ∈ D → HasFDerivWithinAt (f n ω) (innerSL ℝ (score n ω x)) D x)
    (hd : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hd' : ∀ n ω x, x ∈ D' → HasFDerivWithinAt (restrictedScore n ω) (K n ω x) D' x)
    (hL : ∀ n ω x y, x ∈ D → y ∈ D → ‖L n ω x - L n ω y‖ ≤ B n ω * ‖x - y‖)
    (hK : ∀ n ω x, x ∈ D' → ‖K n ω x - K n ω 0‖ ≤ C n ω * ‖x - 0‖)
    (hroot : ∀ n ω, score n ω (T n ω) = 0)
    (hroot' : ∀ n ω, restrictedScore n ω (U n ω) = 0)
    (hlink : ∀ n ω x, restrictedScore n ω x = K₀.orthogonalProjectionOnto (score n ω x))
    (hT : TendstoInMeasure P T atTop (fun _ => 0))
    (hU : TendstoInMeasure P U atTop (fun _ => 0))
    (hB : TendstoInMeasure P B atTop (fun _ => M))
    (hC : TendstoInMeasure P C atTop (fun _ => N))
    (hc : TendstoInMeasure P (fun n ω => L n ω 0) atTop (fun _ => -(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))))
    (hc' : TendstoInMeasure P (fun n ω => K n ω 0) atTop (fun _ => -(ContinuousLinearMap.id ℝ K₀)))
    {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    (hs : TendstoInDistribution (fun n ω => rate n • score n ω 0) atTop Z (fun _ => P) Q)
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin d))) Q) :
    ConvergesInDistribution P Q
      (fun n ω => 2 * rate n ^ 2 * (f n ω (T n ω) - f n ω (U n ω)))
      (fun ω => ‖Z ω - K₀.starProjection (Z ω)‖ ^ 2) ∧
    HasLaw (fun ω => ‖Z ω - K₀.starProjection (Z ω)‖ ^ 2)
      (chiSquared (d - Module.finrank ℝ K₀)) Q := by
  let I := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))
  let Uₑ : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun n ω => U n ω
  have hUₑm n : Measurable (Uₑ n) := continuous_subtype_val.measurable.comp (hUm n)
  have hUₑ : TendstoInMeasure P Uₑ atTop (fun _ => 0) := by
    simpa only [Submodule.coe_zero] using!
      continuous_mapping_probability_const_metric
        (g := fun u : K₀ => (u : EuclideanSpace ℝ (Fin d))) (by fun_prop) hU
  have hpair := consistent_joint_vector_score_root_limit score L restrictedScore K T U B C rate
    D D' hD hD' 0 0 (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin d)))
    (ContinuousLinearEquiv.refl ℝ K₀) K₀.orthogonalProjectionOnto M N h0 h0'
    hTin hUin hTm hUm hsm hrm hB0 hC0 hd hd'
    (fun n ω x hx => hL n ω x 0 hx h0) hK hroot hroot' (fun n ω => hlink n ω 0) hT hU hB hC hc hc' hs
  have hJoint : TendstoInDistribution (fun n ω => (rate n • T n ω, rate n • Uₑ n ω))
      atTop (fun ω => (Z ω, K₀.starProjection (Z ω))) (fun _ => P) Q := by
    have h := hpair.continuous_comp
      (g := fun p : EuclideanSpace ℝ (Fin d) × K₀ => (p.1, (p.2 : EuclideanSpace ℝ (Fin d))))
      (by fun_prop)
    simpa only [sub_zero, ContinuousLinearEquiv.refl_apply, Submodule.coe_smul] using! h
  let err n ω := B n ω * ‖Uₑ n ω‖ + ‖L n ω 0 + I‖
  have hb : TendstoInMeasure P (fun n ω => B n ω * ‖Uₑ n ω‖) atTop (fun _ => 0) := by
    simpa using continuous_mapping_probability_const_metric
      (g := fun p : ℝ × EuclideanSpace ℝ (Fin d) => p.1 * ‖p.2‖)
      (by fun_prop) (probability_product_const hB hUₑ)
  have hl : TendstoInMeasure P (fun n ω => ‖L n ω 0 + I‖) atTop (fun _ => 0) := by
    simpa only [I, neg_add_cancel, norm_zero] using!
      continuous_mapping_probability_const_metric
        (g := fun A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) => ‖A + I‖)
        (by fun_prop) hc
  have herr : TendstoInMeasure P err atTop (fun _ => 0) := by
    simpa only [err, add_zero] using! continuous_mapping_probability_const_metric
      (g := fun p : ℝ × ℝ => p.1 + p.2) (by fun_prop) (probability_product_const hb hl)
  have hbound n ω : ‖L n ω (Uₑ n ω) - -I‖ ≤ err n ω := by
    calc
      ‖L n ω (Uₑ n ω) - -I‖ = ‖(L n ω (Uₑ n ω) - L n ω 0) + (L n ω 0 + I)‖ := by
        congr 1; abel
      _ ≤ ‖L n ω (Uₑ n ω) - L n ω 0‖ + ‖L n ω 0 + I‖ := norm_add_le _ _
      _ ≤ err n ω := by
        dsimp [err]
        gcongr
        simpa only [sub_zero] using hL n ω (Uₑ n ω) 0 (hUinD n ω) h0
  have hAtU : TendstoInMeasure P (fun n ω => L n ω (Uₑ n ω)) atTop (fun _ => -I) := by
    rw [tendstoInMeasure_iff_measureReal_norm]
    intro ε hε
    have hb' n : P.real {ω | ε ≤ ‖L n ω (Uₑ n ω) - -I‖} ≤
        P.real {ω | ε ≤ ‖err n ω - 0‖} := by
      apply measureReal_mono _ (measure_ne_top P _)
      intro ω hω
      exact hω.trans ((hbound n ω).trans (by simpa using le_abs_self (err n ω)))
    exact squeeze_zero (fun _ => measureReal_nonneg) hb'
      (tendstoInMeasure_iff_measureReal_norm.mp herr ε hε)
  exact linear_constraint_wilks_of_joint_limit f score L T Uₑ B rate D hD M K₀
    (fun n ω => (U n ω).property) hTin hUinD hTm hUₑm hfm hBm
    (fun n => ((hLm n).comp (measurable_id.prodMk (hUₑm n))).aemeasurable)
    hB0 hf hd (fun n ω x hx => hL n ω x (Uₑ n ω) hx (hUinD n ω)) hroot
    hT hUₑ hB hAtU hJoint hZ

end LectureNotes
