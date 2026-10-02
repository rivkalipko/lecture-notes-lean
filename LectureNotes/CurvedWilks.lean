import LectureNotes.ConstrainedVectorMLE
import LectureNotes.VectorDeltaMethod
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false

/-! L10 §1.1: curved restrictions, with their local analytic conditions
written explicitly. When f n is the average log-likelihood and rate n is
sqrt n, the statistic below is twice the maximized log-likelihood difference.
Coordinates are centered at the true parameter and have identity information.
The final theorem uses the actual nonlinear zero set and its supplied chart;
existence of that chart is not inferred from set-theoretic nonredundancy. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology InnerProductSpace

/-- The score of an actual likelihood restricted through a smooth chart is
the adjoint chart derivative applied to the ambient score. -/
theorem chart_likelihood_derivative
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → ℝ} {score : E → E} {chart : F → E} {J : F →L[ℝ] E}
    {D : Set E} {D' : Set F} {u : F}
    (hf : HasFDerivWithinAt f (innerSL ℝ (score (chart u))) D (chart u))
    (hj : HasFDerivWithinAt chart J D' u) (hmap : MapsTo chart D' D) :
    HasFDerivWithinAt (fun x => f (chart x))
      (innerSL ℝ (J.adjoint (score (chart u)))) D' u := by
  convert! hf.comp u hj hmap using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  exact J.adjoint_inner_left v (score (chart u))

/-- An interior local maximum in chart coordinates satisfies the genuine
restricted score equation. -/
theorem chart_maximum_score_zero
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → ℝ} {score : E → E} {chart : F → E} {J : F →L[ℝ] E} {u : F}
    (hf : HasFDerivAt f (innerSL ℝ (score (chart u))) (chart u))
    (hj : HasFDerivAt chart J u) (hmax : IsLocalMax (fun x => f (chart x)) u) :
    J.adjoint (score (chart u)) = 0 := by
  have hd : HasFDerivAt (fun x => f (chart x))
      (innerSL ℝ (J.adjoint (score (chart u)))) u := by
    convert! hf.comp u hj using 1
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    exact J.adjoint_inner_left v (score (chart u))
  have hz := hmax.hasFDerivAt_eq_zero hd
  have h := congrArg (fun A : F →L[ℝ] ℝ => A (J.adjoint (score (chart u)))) hz
  simpa only [innerSL_apply_apply, zero_apply,
    real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] using h

/-- A maximum under actual nonlinear equations yields the chart score root
whenever the chart maps a neighborhood into their zero set. -/
theorem nonlinear_restricted_maximum_score_zero
    {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [Zero G]
    {f : E → ℝ} {score : E → E} {chart : F → E} {J : F →L[ℝ] E} {u : F}
    (restriction : E → G) (D' : Set F) (hD' : D' ∈ 𝓝 u)
    (hnull : ∀ a ∈ D', restriction (chart a) = 0)
    (hmax : ∀ x, restriction x = 0 → f x ≤ f (chart u))
    (hf : HasFDerivAt f (innerSL ℝ (score (chart u))) (chart u))
    (hj : HasFDerivAt chart J u) : J.adjoint (score (chart u)) = 0 := by
  apply chart_maximum_score_zero hf hj
  apply IsMaxOn.isLocalMax (s := D') _ hD'
  intro a ha
  exact hmax (chart a) (hnull a ha)

/-- Full rank of the derivative of p restrictions identifies the tangent
kernel's codimension with p. Set-theoretic nonredundancy alone is not this
local regularity condition. -/
theorem full_rank_restriction_codimension {d p : ℕ}
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (hA : Function.Surjective A) :
    d - Module.finrank ℝ A.ker = p := by
  have hr : A.toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr hA
  have hd := A.toLinearMap.finrank_range_add_finrank_ker
  rw [hr] at hd
  have he : p + Module.finrank ℝ A.ker = d := by simpa using hd
  omega

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {d : ℕ}

/-- L10's curved-null Wilks limit in identity-information coordinates.
The null is parametrized locally by a smooth chart over its tangent space.
Both estimates are consistent stationary roots; the restricted score is
explicitly the gradient of the composed likelihood, not an independent
estimating equation. Actual derivative envelopes imply the likelihood
expansion, while the joint score-root limit and chart derivative imply the
normal-space projection and its chi-square law. -/
theorem curved_constraint_wilks_from_score_roots
    (K₀ : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (chart : K₀ → EuclideanSpace ℝ (Fin d))
    (J : K₀ → K₀ →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hchart : Continuous chart) (hJ : Continuous J)
    (hchart0 : chart 0 = 0) (hJ0 : J 0 = K₀.subtypeL)
    (f : ℕ → Ω → EuclideanSpace ℝ (Fin d) → ℝ)
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
    (hfm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => f n p.1 p.2))
    (hLm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => L n p.1 p.2))
    (hBm : ∀ n, AEMeasurable (B n) P)
    (hsm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => score n p.1 p.2))
    (hB0 : ∀ n ω, 0 ≤ B n ω) (hC0 : ∀ n ω, 0 ≤ C n ω)
    (hf : ∀ n ω x, x ∈ D → HasFDerivWithinAt (f n ω) (innerSL ℝ (score n ω x)) D x)
    (hd : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hd' : ∀ n ω u, u ∈ D' → HasFDerivWithinAt
      (fun a => (J a).adjoint (score n ω (chart a))) (K n ω u) D' u)
    (hL : ∀ n ω x y, x ∈ D → y ∈ D → ‖L n ω x - L n ω y‖ ≤ B n ω * ‖x - y‖)
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
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin d))) Q) :
    ConvergesInDistribution P Q
      (fun n ω => 2 * rate n ^ 2 * (f n ω (T n ω) - f n ω (chart (U n ω))))
      (fun ω => ‖Z ω - K₀.starProjection (Z ω)‖ ^ 2) ∧
    HasLaw (fun ω => ‖Z ω - K₀.starProjection (Z ω)‖ ^ 2)
      (chiSquared (d - Module.finrank ℝ K₀)) Q := by
  let I := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))
  let restrictedScore n ω u := (J u).adjoint (score n ω (chart u))
  let Uₑ : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun n ω => chart (U n ω)
  have hUₑm n : Measurable (Uₑ n) := hchart.measurable.comp (hUm n)
  have hUₑ : TendstoInMeasure P Uₑ atTop (fun _ => 0) := by
    simpa only [hchart0] using!
      continuous_mapping_probability_const_metric hchart.continuousAt hU
  have hrm n : Measurable (fun p : Ω × K₀ => restrictedScore n p.1 p.2) := by
    have hss := (hsm n).comp (measurable_fst.prodMk (hchart.measurable.comp measurable_snd))
    have ha : Continuous (fun u => (J u).adjoint) := ContinuousLinearMap.adjoint.continuous.comp hJ
    have hev : Continuous (fun p :
        (EuclideanSpace ℝ (Fin d) →L[ℝ] K₀) × EuclideanSpace ℝ (Fin d) => p.1 p.2) := by
      fun_prop
    exact hev.measurable.comp ((ha.measurable.comp measurable_snd).prodMk hss)
  have hlink n ω : restrictedScore n ω 0 = K₀.orthogonalProjectionOnto (score n ω 0) := by
    simp only [restrictedScore, hchart0, hJ0, Submodule.adjoint_subtypeL]
  have hpair := consistent_joint_vector_score_root_limit score L restrictedScore K T U B C rate
    D D' hD hD' 0 0 (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin d)))
    (ContinuousLinearEquiv.refl ℝ K₀) K₀.orthogonalProjectionOnto M N h0 h0'
    hTin hUin hTm hUm hsm hrm hB0 hC0 hd hd'
    (fun n ω x hx => hL n ω x 0 hx h0) hK hroot hroot' hlink hT hU hB hC hc hc' hs
  let A : (EuclideanSpace ℝ (Fin d) × K₀) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    ContinuousLinearMap.fst ℝ _ _ - K₀.subtypeL.comp (ContinuousLinearMap.snd ℝ _ _)
  have hdg : HasFDerivAt (fun p : EuclideanSpace ℝ (Fin d) × K₀ => p.1 - chart p.2) A (0, 0) := by
    have hj0 : HasFDerivAt chart K₀.subtypeL 0 := by simpa only [hJ0] using hjd 0 h0'
    exact (hasFDerivAt_fst (𝕜 := ℝ)).sub (hj0.comp (0, 0) hasFDerivAt_snd)
  have hJoint : TendstoInDistribution
      (fun n ω => rate n • ((T n ω, U n ω) - (0, 0))) atTop
      (fun ω => (Z ω, K₀.orthogonalProjectionOnto (Z ω))) (fun _ => P) Q := by
    simpa only [sub_zero, ContinuousLinearEquiv.refl_apply, Prod.smul_mk,
      Prod.mk_zero_zero] using! hpair
  have hDelta := normed_delta_method
    (fun n => ((hTm n).prodMk (hUm n)).aemeasurable) (probability_product_const hT hU)
    hJoint (continuous_fst.sub (hchart.comp continuous_snd)) hdg
  have hE : TendstoInDistribution (fun n ω => rate n • (T n ω - Uₑ n ω))
      atTop (fun ω => Z ω - K₀.starProjection (Z ω)) (fun _ => P) Q := by
    simpa [hchart0, A, Uₑ, Function.comp_def, Pi.sub_apply] using! hDelta
  have hTU : TendstoInMeasure P (fun n ω => T n ω - Uₑ n ω) atTop (fun _ => 0) := by
    simpa using continuous_mapping_probability_const_metric
      (g := fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 - p.2)
      (by fun_prop) (probability_product_const hT hUₑ)
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
        simpa only [sub_zero] using hL n ω (Uₑ n ω) 0 (hmap (hUin n ω)) h0
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
  refine ⟨?_, ?_⟩
  · simpa only [I, Uₑ, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] using!
      vector_likelihood_ratio_limit f score L T Uₑ B rate D hD M I (by intros; rfl)
        hTin (fun n ω => hmap (hUin n ω)) hTm hUₑm hfm hBm
        (fun n => ((hLm n).comp (measurable_id.prodMk (hUₑm n))).aemeasurable)
        hB0 hf hd (fun n ω x hx => hL n ω x (Uₑ n ω) hx (hmap (hUin n ω)))
        hroot hTU hB hAtU hE
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

/-- Curved-null Wilks for actual full and restricted maximizers in open
neighborhoods. The constrained model is the chart image; stationarity is
derived from these maximum properties and the actual derivatives. -/
theorem curved_constraint_wilks_of_maxima
    (K₀ : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (chart : K₀ → EuclideanSpace ℝ (Fin d))
    (J : K₀ → K₀ →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hchart : Continuous chart) (hJ : Continuous J)
    (hchart0 : chart 0 = 0) (hJ0 : J 0 = K₀.subtypeL)
    (f : ℕ → Ω → EuclideanSpace ℝ (Fin d) → ℝ)
    (score : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℕ → Ω → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (K : ℕ → Ω → K₀ → K₀ →L[ℝ] K₀)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (U : ℕ → Ω → K₀)
    (B C : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (D' : Set K₀)
    (hD : Convex ℝ D) (hD' : Convex ℝ D') (hDopen : IsOpen D) (hDopen' : IsOpen D')
    (M N : ℝ)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ D) (h0' : (0 : K₀) ∈ D')
    (hmap : MapsTo chart D' D)
    (hjd : ∀ u ∈ D', HasFDerivAt chart (J u) u)
    (hTin : ∀ n ω, T n ω ∈ D) (hUin : ∀ n ω, U n ω ∈ D')
    (hTm : ∀ n, Measurable (T n)) (hUm : ∀ n, Measurable (U n))
    (hfm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => f n p.1 p.2))
    (hLm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => L n p.1 p.2))
    (hBm : ∀ n, AEMeasurable (B n) P)
    (hsm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => score n p.1 p.2))
    (hB0 : ∀ n ω, 0 ≤ B n ω) (hC0 : ∀ n ω, 0 ≤ C n ω)
    (hf : ∀ n ω x, x ∈ D → HasFDerivWithinAt (f n ω) (innerSL ℝ (score n ω x)) D x)
    (hd : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hd' : ∀ n ω u, u ∈ D' → HasFDerivWithinAt
      (fun a => (J a).adjoint (score n ω (chart a))) (K n ω u) D' u)
    (hL : ∀ n ω x y, x ∈ D → y ∈ D → ‖L n ω x - L n ω y‖ ≤ B n ω * ‖x - y‖)
    (hK : ∀ n ω u, u ∈ D' → ‖K n ω u - K n ω 0‖ ≤ C n ω * ‖u - 0‖)
    (hmax : ∀ n ω, IsMaxOn (f n ω) D (T n ω))
    (hmax' : ∀ n ω, IsMaxOn (f n ω) (chart '' D') (chart (U n ω)))
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
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin d))) Q) :
    ConvergesInDistribution P Q
      (fun n ω => 2 * rate n ^ 2 * (f n ω (T n ω) - f n ω (chart (U n ω))))
      (fun ω => ‖Z ω - K₀.starProjection (Z ω)‖ ^ 2) ∧
    HasLaw (fun ω => ‖Z ω - K₀.starProjection (Z ω)‖ ^ 2)
      (chiSquared (d - Module.finrank ℝ K₀)) Q := by
  have hroot n ω : score n ω (T n ω) = 0 := by
    have hfAt := (hf n ω (T n ω) (hTin n ω)).hasFDerivAt (hDopen.mem_nhds (hTin n ω))
    have hlocal := (hmax n ω).isLocalMax (hDopen.mem_nhds (hTin n ω))
    have hz := hlocal.hasFDerivAt_eq_zero hfAt
    have h := congrArg (fun A : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => A (score n ω (T n ω))) hz
    simpa only [innerSL_apply_apply, zero_apply, real_inner_self_eq_norm_sq,
      sq_eq_zero_iff, norm_eq_zero] using h
  have hroot' n ω : (J (U n ω)).adjoint (score n ω (chart (U n ω))) = 0 := by
    have hfAt := (hf n ω (chart (U n ω)) (hmap (hUin n ω))).hasFDerivAt
      (hDopen.mem_nhds (hmap (hUin n ω)))
    apply chart_maximum_score_zero hfAt (hjd (U n ω) (hUin n ω))
    apply IsMaxOn.isLocalMax (s := D') _ (hDopen'.mem_nhds (hUin n ω))
    intro a ha
    exact hmax' n ω ⟨a, ha, rfl⟩
  exact curved_constraint_wilks_from_score_roots K₀ chart J hchart hJ hchart0 hJ0
    f score L K T U B C rate D D' hD hD' M N h0 h0' hmap hjd hTin hUin
    hTm hUm hfm hLm hBm hsm hB0 hC0 hf hd hd' hL hK hroot hroot'
    hT hU hB hC hc hc' hs hZ

/-- The nonlinear-equation formulation of L10: p smooth restrictions with
full-rank derivative, a supplied local chart of exactly their zero set, and
actual full/restricted maximizers give the chi-square-p likelihood-ratio
limit. The chart and analytical regularity are explicit sufficient conditions;
set-theoretic irredundancy of equations is not substituted for derivative rank. -/
theorem nonlinear_restriction_wilks_of_maxima {p : ℕ}
    (restriction : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin p))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (_hrestriction : HasFDerivAt restriction A 0) (hA : Function.Surjective A)
    (chart : (A.ker) → EuclideanSpace ℝ (Fin d))
    (J : (A.ker) → (A.ker) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hchart : Continuous chart) (hJ : Continuous J)
    (hchart0 : chart 0 = 0) (hJ0 : J 0 = (A.ker).subtypeL)
    (f : ℕ → Ω → EuclideanSpace ℝ (Fin d) → ℝ)
    (score : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℕ → Ω → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (K : ℕ → Ω → (A.ker) → (A.ker) →L[ℝ] (A.ker))
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (U : ℕ → Ω → (A.ker))
    (B C : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (D' : Set (A.ker))
    (hD : Convex ℝ D) (hD' : Convex ℝ D') (hDopen : IsOpen D) (hDopen' : IsOpen D')
    (M N : ℝ)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ D) (h0' : (0 : (A.ker)) ∈ D')
    (hchartImage : chart '' D' = {x | x ∈ D ∧ restriction x = 0})
    (hjd : ∀ u ∈ D', HasFDerivAt chart (J u) u)
    (hTin : ∀ n ω, T n ω ∈ D) (hUin : ∀ n ω, U n ω ∈ D')
    (hTm : ∀ n, Measurable (T n)) (hUm : ∀ n, Measurable (U n))
    (hfm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => f n p.1 p.2))
    (hLm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => L n p.1 p.2))
    (hBm : ∀ n, AEMeasurable (B n) P)
    (hsm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => score n p.1 p.2))
    (hB0 : ∀ n ω, 0 ≤ B n ω) (hC0 : ∀ n ω, 0 ≤ C n ω)
    (hf : ∀ n ω x, x ∈ D → HasFDerivWithinAt (f n ω) (innerSL ℝ (score n ω x)) D x)
    (hd : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hd' : ∀ n ω u, u ∈ D' → HasFDerivWithinAt
      (fun a => (J a).adjoint (score n ω (chart a))) (K n ω u) D' u)
    (hL : ∀ n ω x y, x ∈ D → y ∈ D → ‖L n ω x - L n ω y‖ ≤ B n ω * ‖x - y‖)
    (hK : ∀ n ω u, u ∈ D' → ‖K n ω u - K n ω 0‖ ≤ C n ω * ‖u - 0‖)
    (hmax : ∀ n ω, IsMaxOn (f n ω) D (T n ω))
    (hmax' : ∀ n ω, IsMaxOn (f n ω) {x | x ∈ D ∧ restriction x = 0} (chart (U n ω)))
    (hT : TendstoInMeasure P T atTop (fun _ => 0))
    (hU : TendstoInMeasure P U atTop (fun _ => 0))
    (hB : TendstoInMeasure P B atTop (fun _ => M))
    (hC : TendstoInMeasure P C atTop (fun _ => N))
    (hc : TendstoInMeasure P (fun n ω => L n ω 0) atTop
      (fun _ => -(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))))
    (hc' : TendstoInMeasure P (fun n ω => K n ω 0) atTop
      (fun _ => -(ContinuousLinearMap.id ℝ (A.ker))))
    {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    (hs : TendstoInDistribution (fun n ω => rate n • score n ω 0) atTop Z (fun _ => P) Q)
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin d))) Q) :
    ConvergesInDistribution P Q
      (fun n ω => 2 * rate n ^ 2 * (f n ω (T n ω) - f n ω (chart (U n ω))))
      (fun ω => ‖Z ω - (A.ker).starProjection (Z ω)‖ ^ 2) ∧
    HasLaw (fun ω => ‖Z ω - (A.ker).starProjection (Z ω)‖ ^ 2)
      (chiSquared p) Q := by
  have hmap : MapsTo chart D' D := by
    intro u hu
    have h : chart u ∈ chart '' D' := ⟨u, hu, rfl⟩
    rw [hchartImage] at h
    exact h.1
  have hmaxChart n ω : IsMaxOn (f n ω) (chart '' D') (chart (U n ω)) := by
    rw [hchartImage]
    exact hmax' n ω
  have h := curved_constraint_wilks_of_maxima A.ker chart J hchart hJ hchart0 hJ0
    f score L K T U B C rate D D' hD hD' hDopen hDopen' M N h0 h0' hmap hjd hTin hUin
    hTm hUm hfm hLm hBm hsm hB0 hC0 hf hd hd' hL hK hmax hmaxChart
    hT hU hB hC hc hc' hs hZ
  simpa only [full_rank_restriction_codimension A hA] using! h

end LectureNotes
