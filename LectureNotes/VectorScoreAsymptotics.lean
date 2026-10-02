import LectureNotes.VectorWald
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

/-! L7: the multivariate score-root argument. A measurable rank-one correction
encodes the exact score difference. Derivative bounds prove convergence of this
operator; no random intermediate point or assumed linear expansion is needed. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An exact effective negative derivative between the two parameter values. -/
def effectiveVectorCurvature (score : E → E) (θ t : E) (H : E →L[ℝ] E) : E →L[ℝ] E :=
  H + (‖t - θ‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ
    (score θ - score t - H (t - θ)) (t - θ)

theorem effectiveVectorCurvature_identity (score : E → E) (θ t : E)
    (H : E →L[ℝ] E) :
    effectiveVectorCurvature score θ t H (t - θ) = score θ - score t := by
  by_cases h : t - θ = 0
  · have ht : t = θ := sub_eq_zero.mp h
    simp [ht]
  · have hn : ‖t - θ‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr h)
    simp only [effectiveVectorCurvature, add_apply,
      smul_apply, InnerProductSpace.rankOne_apply,
      real_inner_self_eq_norm_sq, smul_smul, inv_mul_cancel₀ hn, one_smul]
    abel

/-- A local Lipschitz bound for the derivative controls the exact effective
operator in operator norm. -/
theorem effectiveVectorCurvature_bound {score : E → E} {L : E → E →L[ℝ] E}
    {D : Set E} (hD : Convex ℝ D) {θ t : E} {H : E →L[ℝ] E} {B : ℝ}
    (hθ : θ ∈ D) (ht : t ∈ D) (hB : 0 ≤ B)
    (hd : ∀ x ∈ D, HasFDerivWithinAt score (L x) D x)
    (hL : ∀ x ∈ D, ‖L x - L θ‖ ≤ B * ‖x - θ‖) :
    ‖effectiveVectorCurvature score θ t H - H‖ ≤ B * ‖t - θ‖ + ‖L θ + H‖ := by
  have hsub : segment ℝ θ t ⊆ D := hD.segment_subset hθ ht
  have hd' (x) (hx : x ∈ segment ℝ θ t) :
      HasFDerivWithinAt (fun x => score x + H x) (L x + H) (segment ℝ θ t) x :=
    ((hd x (hsub hx)).mono hsub).add H.hasFDerivAt.hasFDerivWithinAt
  have hb (x) (hx : x ∈ segment ℝ θ t) :
      ‖L x + H‖ ≤ B * ‖t - θ‖ + ‖L θ + H‖ := by
    calc
      ‖L x + H‖ = ‖(L x - L θ) + (L θ + H)‖ := by congr 1; abel
      _ ≤ ‖L x - L θ‖ + ‖L θ + H‖ := norm_add_le _ _
      _ ≤ B * ‖t - θ‖ + ‖L θ + H‖ := by
        gcongr
        exact (hL x (hsub hx)).trans
          (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hx) hB)
  have hm := (convex_segment θ t).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd' hb (left_mem_segment ℝ θ t) (right_mem_segment ℝ θ t)
  have hr : ‖score θ - score t - H (t - θ)‖ ≤
      (B * ‖t - θ‖ + ‖L θ + H‖) * ‖t - θ‖ := by
    rw [← norm_neg]
    convert hm using 1
    simp only [map_sub]
    congr 1
    abel
  by_cases h : t - θ = 0
  · simp [effectiveVectorCurvature, h]
  · have hn : 0 < ‖t - θ‖ := norm_pos_iff.mpr h
    simp only [effectiveVectorCurvature, add_sub_cancel_left, norm_smul,
      norm_inv, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖t - θ‖),
      InnerProductSpace.norm_rankOne]
    calc
      (‖t - θ‖ ^ 2)⁻¹ * (‖score θ - score t - H (t - θ)‖ * ‖t - θ‖) ≤
          (‖t - θ‖ ^ 2)⁻¹ *
            (((B * ‖t - θ‖ + ‖L θ + H‖) * ‖t - θ‖) * ‖t - θ‖) := by gcongr
      _ = B * ‖t - θ‖ + ‖L θ + H‖ := by field_simp

theorem effectiveVectorCurvature_bound_of_second_derivative
    {score : E → E} {L : E → E →L[ℝ] E} {L' : E → E →L[ℝ] (E →L[ℝ] E)}
    {D : Set E} (hD : Convex ℝ D) {θ t : E} {H : E →L[ℝ] E} {B : ℝ}
    (hθ : θ ∈ D) (ht : t ∈ D) (hB : 0 ≤ B)
    (hd : ∀ x ∈ D, HasFDerivWithinAt score (L x) D x)
    (hd' : ∀ x ∈ D, HasFDerivWithinAt L (L' x) D x)
    (hb : ∀ x ∈ D, ‖L' x‖ ≤ B) :
    ‖effectiveVectorCurvature score θ t H - H‖ ≤ B * ‖t - θ‖ + ‖L θ + H‖ := by
  apply effectiveVectorCurvature_bound hD hθ ht hB hd
  intro x hx
  exact hD.norm_image_sub_le_of_norm_hasFDerivWithin_le hd' hb hθ hx

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
/-- The total inverse on continuous endomorphisms is measurable. -/
theorem measurable_endomorphism_inverse :
    Measurable (Ring.inverse : (F →L[ℝ] F) → F →L[ℝ] F) := by
  classical
  have hc : ContinuousOn (Ring.inverse : (F →L[ℝ] F) → F →L[ℝ] F) {A | IsUnit A} := by
    rintro A ⟨u, rfl⟩
    exact (NormedRing.inverse_continuousAt u).continuousWithinAt
  have hm := hc.measurable_piecewise (g := fun _ => 0) continuous_const.continuousOn
    Units.isOpen.measurableSet
  convert hm using 1
  funext A
  by_cases h : IsUnit A
  · simp [Set.piecewise, h]
  · simp [Set.piecewise, h]

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- Inversion is continuous at the nonsingular limiting operator. -/
theorem endomorphism_inverse_consistency {A : ℕ → Ω → F →L[ℝ] F}
    (H : F ≃L[ℝ] F) (hA : TendstoInMeasure P A atTop (fun _ => H.toContinuousLinearMap)) :
    TendstoInMeasure P (fun n ω => Ring.inverse (A n ω)) atTop
      (fun _ => H.symm.toContinuousLinearMap) := by
  have h := continuous_mapping_probability_const_metric
    (NormedRing.inverse_continuousAt H.toUnit) hA
  have he : Ring.inverse H.toContinuousLinearMap = H.symm.toContinuousLinearMap :=
    Ring.inverse_unit H.toUnit
  simp only [ContinuousLinearEquiv.toUnit] at h
  simpa only [he] using! h

/-- The exact root equation agrees with total inverse multiplication except
on events whose probabilities vanish as the operator approaches a unit. -/
theorem vector_root_inverse_error {S V : ℕ → Ω → F} {A : ℕ → Ω → F →L[ℝ] F}
    (H : F ≃L[ℝ] F)
    (hA : TendstoInMeasure P A atTop (fun _ => H.toContinuousLinearMap))
    (hroot : ∀ n, ∀ᵐ ω ∂P, A n ω (V n ω) = S n ω) :
    TendstoInMeasure P (fun n ω => V n ω - Ring.inverse (A n ω) (S n ω))
      atTop (fun _ => 0) := by
  obtain ⟨δ, hδ, hunit⟩ := Metric.mem_nhds_iff.mp (Units.nhds H.toUnit)
  have herr : TendstoInMeasure P (fun n ω => V n ω - Ring.inverse (A n ω) (S n ω))
      atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_measureReal_norm]
    intro ε hε
    have hb n : P.real {ω | ε ≤ ‖V n ω - Ring.inverse (A n ω) (S n ω) - 0‖} ≤
        P.real {ω | δ ≤ ‖A n ω - H.toContinuousLinearMap‖} := by
      apply ENNReal.toReal_mono (measure_ne_top P _)
      apply measure_mono_ae
      filter_upwards [hroot n] with ω hr
      intro hω
      change ε ≤ ‖V n ω - Ring.inverse (A n ω) (S n ω) - 0‖ at hω
      change δ ≤ ‖A n ω - H.toContinuousLinearMap‖
      by_contra hn
      have hu : IsUnit (A n ω) := hunit (by simpa only [Metric.mem_ball, dist_eq_norm, ContinuousLinearEquiv.toUnit] using! lt_of_not_ge hn)
      have he : Ring.inverse (A n ω) (S n ω) = V n ω := by
        rw [← hr]
        have hc := congrArg (fun L : F →L[ℝ] F => L (V n ω)) (Ring.inverse_mul_cancel (A n ω) hu)
        exact hc
      simp only [he, sub_self, sub_zero, norm_zero] at hω
      exact not_le_of_gt hε hω
    exact squeeze_zero (fun _ => measureReal_nonneg) hb
      (tendstoInMeasure_iff_measureReal_norm.mp hA δ hδ)
  exact herr

/-- An exact score equation transfers a vector limit through a nonsingular
limiting curvature. Finite-sample operators may be singular. -/
theorem vector_score_root_limit {S V : ℕ → Ω → F} {A : ℕ → Ω → F →L[ℝ] F}
    {Z : Ω' → F} (H : F ≃L[ℝ] F)
    (hS : TendstoInDistribution S atTop Z (fun _ => P) Q)
    (hA : TendstoInMeasure P A atTop (fun _ => H.toContinuousLinearMap))
    (hAm : ∀ n, AEMeasurable (A n) P) (hVm : ∀ n, AEMeasurable (V n) P)
    (hroot : ∀ n, ∀ᵐ ω ∂P, A n ω (V n ω) = S n ω) :
    TendstoInDistribution V atTop (fun ω => H.symm (Z ω)) (fun _ => P) Q := by
  have hi := endomorphism_inverse_consistency H hA
  have hlim : TendstoInDistribution (fun n ω => Ring.inverse (A n ω) (S n ω))
      atTop (fun ω => H.symm (Z ω)) (fun _ => P) Q := by
    exact hS.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : F × (F →L[ℝ] F) => p.2 p.1) (by fun_prop) hi
      (fun n => measurable_endomorphism_inverse.comp_aemeasurable (hAm n))
  have herr := vector_root_inverse_error H hA hroot
  exact tendstoInDistribution_of_tendstoInMeasure_sub V (fun ω => H.symm (Z ω)) hlim herr hVm

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 1200000 in
/-- Joint limits for two root equations driven by the same score. Applying
this to a full model and a restricted model preserves their dependence. -/
theorem paired_vector_score_root_limit
    {S V : ℕ → Ω → E} {W : ℕ → Ω → F}
    {A : ℕ → Ω → E →L[ℝ] E} {C : ℕ → Ω → F →L[ℝ] F} {Z : Ω' → E}
    (R : E →L[ℝ] F) (H : E ≃L[ℝ] E) (G : F ≃L[ℝ] F)
    (hS : TendstoInDistribution S atTop Z (fun _ => P) Q)
    (hA : TendstoInMeasure P A atTop (fun _ => H.toContinuousLinearMap))
    (hC : TendstoInMeasure P C atTop (fun _ => G.toContinuousLinearMap))
    (hAm : ∀ n, AEMeasurable (A n) P) (hCm : ∀ n, AEMeasurable (C n) P)
    (hVm : ∀ n, AEMeasurable (V n) P) (hWm : ∀ n, AEMeasurable (W n) P)
    (hroot : ∀ n, ∀ᵐ ω ∂P, A n ω (V n ω) = S n ω)
    (hroot' : ∀ n, ∀ᵐ ω ∂P, C n ω (W n ω) = R (S n ω)) :
    TendstoInDistribution (fun n ω => (V n ω, W n ω)) atTop
      (fun ω => (H.symm (Z ω), G.symm (R (Z ω)))) (fun _ => P) Q := by
  have hi := endomorphism_inverse_consistency H hA
  have hj := endomorphism_inverse_consistency G hC
  have hlim : TendstoInDistribution
      (fun n ω => (Ring.inverse (A n ω) (S n ω), Ring.inverse (C n ω) (R (S n ω))))
      atTop (fun ω => (H.symm (Z ω), G.symm (R (Z ω)))) (fun _ => P) Q := by
    exact hS.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : E × ((E →L[ℝ] E) × (F →L[ℝ] F)) =>
        (p.2.1 p.1, p.2.2 (R p.1))) (by fun_prop)
      (probability_product_const hi hj)
      (fun n => (measurable_endomorphism_inverse.comp_aemeasurable (hAm n)).prodMk
        (measurable_endomorphism_inverse.comp_aemeasurable (hCm n)))
  have herr := probability_product_const (vector_root_inverse_error H hA hroot)
    (vector_root_inverse_error G hC hroot')
  have hdiff : TendstoInMeasure P
      ((fun n ω => (V n ω, W n ω)) -
        (fun n ω => (Ring.inverse (A n ω) (S n ω), Ring.inverse (C n ω) (R (S n ω)))))
      atTop 0 := by
    simpa only [Pi.sub_apply, Prod.mk_sub_mk] using! herr
  exact tendstoInDistribution_of_tendstoInMeasure_sub (fun n ω => (V n ω, W n ω))
    (fun ω => (H.symm (Z ω), G.symm (R (Z ω)))) hlim hdiff
    (fun n => (hVm n).prodMk (hWm n))

set_option maxHeartbeats 1200000 in
/-- Derivative control and consistency prove convergence and measurability of
the exact effective negative derivative. -/
theorem effective_vector_curvature_regular
    (score : ℕ → Ω → E → E) (L : ℕ → Ω → E → E →L[ℝ] E)
    (T : ℕ → Ω → E) (B : ℕ → Ω → ℝ)
    (D : Set E) (hD : Convex ℝ D) (θ : E) (H : E ≃L[ℝ] E) (M : ℝ)
    (hθ : θ ∈ D) (hTin : ∀ n ω, T n ω ∈ D) (hTm : ∀ n, Measurable (T n))
    (hsm : ∀ n, Measurable (fun p : Ω × E => score n p.1 p.2))
    (hB0 : ∀ n ω, 0 ≤ B n ω)
    (hd : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hL : ∀ n ω x, x ∈ D → ‖L n ω x - L n ω θ‖ ≤ B n ω * ‖x - θ‖)
    (hT : TendstoInMeasure P T atTop (fun _ => θ))
    (hB : TendstoInMeasure P B atTop (fun _ => M))
    (hc : TendstoInMeasure P (fun n ω => L n ω θ) atTop
      (fun _ => -H.toContinuousLinearMap))
    : TendstoInMeasure P
        (fun n ω => effectiveVectorCurvature (score n ω) θ (T n ω) H.toContinuousLinearMap)
        atTop (fun _ => H.toContinuousLinearMap) ∧
      ∀ n, AEMeasurable
        (fun ω => effectiveVectorCurvature (score n ω) θ (T n ω) H.toContinuousLinearMap) P := by
  let A n ω := effectiveVectorCurvature (score n ω) θ (T n ω) H.toContinuousLinearMap
  let err n ω := B n ω * ‖T n ω - θ‖ + ‖L n ω θ + H.toContinuousLinearMap‖
  have hprod : TendstoInMeasure P (fun n ω => B n ω * ‖T n ω - θ‖) atTop
      (fun _ => 0) := by
    simpa using continuous_mapping_probability_const_metric
      (g := fun p : ℝ × E => p.1 * ‖p.2 - θ‖) (by fun_prop)
      (probability_product_const hB hT)
  have hcerr : TendstoInMeasure P (fun n ω => ‖L n ω θ + H.toContinuousLinearMap‖)
      atTop (fun _ => 0) := by
    simpa using continuous_mapping_probability_const_metric
      (g := fun C : E →L[ℝ] E => ‖C + H.toContinuousLinearMap‖) (by fun_prop) hc
  have herr : TendstoInMeasure P err atTop (fun _ => 0) := by
    simpa only [err, add_zero] using continuous_mapping_probability_const_metric
      (g := fun p : ℝ × ℝ => p.1 + p.2) (by fun_prop)
      (probability_product_const hprod hcerr)
  have hbound n ω : ‖A n ω - H.toContinuousLinearMap‖ ≤ err n ω :=
    effectiveVectorCurvature_bound hD hθ (hTin n ω) (hB0 n ω) (hd n ω) (hL n ω)
  have hA : TendstoInMeasure P A atTop (fun _ => H.toContinuousLinearMap) := by
    rw [tendstoInMeasure_iff_measureReal_norm]
    intro ε hε
    have hb n : P.real {ω | ε ≤ ‖A n ω - H.toContinuousLinearMap‖} ≤
        P.real {ω | ε ≤ ‖err n ω - 0‖} := by
      apply measureReal_mono _ (measure_ne_top P _)
      intro ω hω
      exact hω.trans ((hbound n ω).trans (by simpa using le_abs_self (err n ω)))
    exact squeeze_zero (fun _ => measureReal_nonneg) hb
      (tendstoInMeasure_iff_measureReal_norm.mp herr ε hε)
  have hAm n : AEMeasurable (A n) P := by
    have hsθ : Measurable (fun ω => score n ω θ) :=
      (hsm n).comp (measurable_id.prodMk measurable_const)
    have hst : Measurable (fun ω => score n ω (T n ω)) :=
      (hsm n).comp (measurable_id.prodMk (hTm n))
    have ht : Measurable (fun ω => T n ω - θ) := (hTm n).sub_const θ
    have hr := (hsθ.sub hst).sub (H.continuous.measurable.comp ht)
    have hrank : Measurable (fun ω => InnerProductSpace.rankOne ℝ
        (score n ω θ - score n ω (T n ω) - H (T n ω - θ)) (T n ω - θ)) := by
      have hi := (innerSL ℝ (E := E)).continuous.measurable.comp ht
      simpa only [InnerProductSpace.rankOne_def] using!
        (ContinuousLinearMap.smulRightL ℝ E E).continuous₂.measurable.comp (hi.prodMk hr)
    exact (measurable_const.add ((ht.norm.pow_const 2).inv.smul hrank)).aemeasurable
  exact ⟨hA, hAm⟩

set_option maxHeartbeats 1200000 in
/-- Consistency and derivative control imply the multivariate linearization
and hence the transformed score limit. The derivatives are evaluated at the
fixed parameter for their probabilistic limit. -/
theorem consistent_vector_score_root_limit
    (score : ℕ → Ω → E → E) (L : ℕ → Ω → E → E →L[ℝ] E)
    (T : ℕ → Ω → E) (B : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set E) (hD : Convex ℝ D) (θ : E) (H : E ≃L[ℝ] E) (M : ℝ)
    (hθ : θ ∈ D) (hTin : ∀ n ω, T n ω ∈ D) (hTm : ∀ n, Measurable (T n))
    (hsm : ∀ n, Measurable (fun p : Ω × E => score n p.1 p.2))
    (hB0 : ∀ n ω, 0 ≤ B n ω)
    (hd : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hL : ∀ n ω x, x ∈ D → ‖L n ω x - L n ω θ‖ ≤ B n ω * ‖x - θ‖)
    (hroot : ∀ n ω, score n ω (T n ω) = 0)
    (hT : TendstoInMeasure P T atTop (fun _ => θ))
    (hB : TendstoInMeasure P B atTop (fun _ => M))
    (hc : TendstoInMeasure P (fun n ω => L n ω θ) atTop
      (fun _ => -H.toContinuousLinearMap))
    {Z : Ω' → E}
    (hs : TendstoInDistribution (fun n ω => rate n • score n ω θ) atTop Z (fun _ => P) Q) :
    TendstoInDistribution (fun n ω => rate n • (T n ω - θ)) atTop
      (fun ω => H.symm (Z ω)) (fun _ => P) Q := by
  obtain ⟨hA, hAm⟩ := effective_vector_curvature_regular score L T B D hD θ H M
    hθ hTin hTm hsm hB0 hd hL hT hB hc
  let A n ω := effectiveVectorCurvature (score n ω) θ (T n ω) H.toContinuousLinearMap
  apply vector_score_root_limit H hs hA hAm
    (fun n => (measurable_const.smul ((hTm n).sub_const θ)).aemeasurable)
  intro n
  apply ae_of_all
  intro ω
  change A n ω (rate n • (T n ω - θ)) = rate n • score n ω θ
  rw [map_smul]
  simp only [A, effectiveVectorCurvature_identity, hroot n ω, sub_zero]

end LectureNotes
