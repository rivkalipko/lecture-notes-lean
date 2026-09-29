import LectureNotes.AsymptoticTests

set_option autoImplicit false

/-! L7's local curvature argument. A measurable divided difference replaces
an unspecified random mean-value point. Derivative bounds, consistency, and
fixed-parameter curvature limits establish convergence of that difference. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

/-- Effective negative curvature of a score between θ₀ and an estimate t.
At a coincident endpoint choose the limiting information I. -/
def effectiveScoreCurvature (score : ℝ → ℝ) (θ₀ t I : ℝ) : ℝ :=
  if t = θ₀ then I else (score θ₀ - score t) / (t - θ₀)

theorem effectiveScoreCurvature_identity (score : ℝ → ℝ) (θ₀ t I : ℝ) :
    effectiveScoreCurvature score θ₀ t I * (t - θ₀) = score θ₀ - score t := by
  by_cases ht : t = θ₀
  · simp [effectiveScoreCurvature, ht]
  · simp [effectiveScoreCurvature, ht, sub_ne_zero.mpr ht]

/-- The deterministic bound behind the random-curvature consistency argument.
It follows from the mean value inequality, without choosing a mean-value point. -/
theorem effectiveScoreCurvature_bound {score curvature : ℝ → ℝ} {D : Set ℝ}
    (hD : Convex ℝ D) {θ₀ t I B : ℝ} (hθ : θ₀ ∈ D) (ht : t ∈ D) (hB : 0 ≤ B)
    (hderiv : ∀ θ ∈ D, HasDerivWithinAt score (curvature θ) D θ)
    (hcurv : ∀ θ ∈ D, |curvature θ - curvature θ₀| ≤ B * |θ - θ₀|) :
    |effectiveScoreCurvature score θ₀ t I - I| ≤
      B * |t - θ₀| + |curvature θ₀ + I| := by
  by_cases heq : t = θ₀
  · simp [effectiveScoreCurvature, heq]
  have hsub : uIcc θ₀ t ⊆ D := hD.ordConnected.uIcc_subset hθ ht
  have hd (θ) (hθseg : θ ∈ uIcc θ₀ t) :
      HasDerivWithinAt (fun θ => score θ + I * θ) (curvature θ + I) (uIcc θ₀ t) θ := by
    simpa using! ((hderiv θ (hsub hθseg)).mono hsub).add
      ((hasDerivAt_id θ).const_mul I).hasDerivWithinAt
  have hb (θ) (hθseg : θ ∈ uIcc θ₀ t) :
      ‖curvature θ + I‖ ≤ B * |t - θ₀| + |curvature θ₀ + I| := by
    have h₁ := hcurv θ (hsub hθseg)
    have h₂ := mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hθseg) hB
    rw [Real.norm_eq_abs]
    have h₃ := abs_add_le (curvature θ - curvature θ₀) (curvature θ₀ + I)
    have he : curvature θ - curvature θ₀ + (curvature θ₀ + I) = curvature θ + I := by ring
    rw [he] at h₃
    linarith
  have hm := (convex_uIcc θ₀ t).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hb (left_mem_uIcc) (right_mem_uIcc)
  have he : effectiveScoreCurvature score θ₀ t I - I =
      -((score t + I * t) - (score θ₀ + I * θ₀)) / (t - θ₀) := by
    rw [effectiveScoreCurvature, if_neg heq]
    field_simp
    <;> ring
  rw [he, abs_div, abs_neg, div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr heq))]
  simpa only [Real.norm_eq_abs] using hm

/-- A bound on the derivative of the curvature supplies the preceding
Lipschitz hypothesis. For a log likelihood this is its third derivative. -/
theorem effectiveScoreCurvature_bound_of_third_derivative
    {score curvature third : ℝ → ℝ} {D : Set ℝ} (hD : Convex ℝ D)
    {θ₀ t I B : ℝ} (hθ : θ₀ ∈ D) (ht : t ∈ D) (hB : 0 ≤ B)
    (hscore : ∀ θ ∈ D, HasDerivWithinAt score (curvature θ) D θ)
    (hcurvature : ∀ θ ∈ D, HasDerivWithinAt curvature (third θ) D θ)
    (hthird : ∀ θ ∈ D, |third θ| ≤ B) :
    |effectiveScoreCurvature score θ₀ t I - I| ≤
      B * |t - θ₀| + |curvature θ₀ + I| := by
  apply effectiveScoreCurvature_bound hD hθ ht hB hscore
  intro θ hθ'
  simpa only [Real.norm_eq_abs] using hD.norm_image_sub_le_of_norm_hasDerivWithin_le
    hcurvature (by simpa only [Real.norm_eq_abs] using hthird) hθ hθ'

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- A score-root limit needs nonzero limiting information, but the finite
sample curvature is allowed to vanish on events whose probabilities tend to
zero. This avoids an unnecessary assumption at every sample size. -/
theorem score_root_limit_allow_zero_curvature {S H E : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {I : ℝ}
    (hI : 0 < I) (hS : ConvergesInDistribution P Q S Z)
    (hH : ConvergesInProbability P H (fun _ => I))
    (hHm : ∀ n, AEMeasurable (H n) P) (hEm : ∀ n, AEMeasurable (E n) P)
    (hroot : ∀ n, ∀ᵐ ω ∂P, H n ω * E n ω = S n ω) :
    ConvergesInDistribution P Q E (fun ω => Z ω / I) := by
  have hdiff : ConvergesInProbability P (fun n ω => E n ω - S n ω / H n ω) (fun _ => 0) := by
    rw [ConvergesInProbability, tendstoInMeasure_iff_measureReal_norm]
    intro ε hε
    have hb n : P.real {ω | ε ≤ ‖E n ω - S n ω / H n ω - 0‖} ≤
        P.real {ω | I ≤ ‖H n ω - I‖} := by
      apply ENNReal.toReal_mono (measure_ne_top P _)
      apply measure_mono_ae
      filter_upwards [hroot n] with ω hr
      intro hω
      change ε ≤ ‖E n ω - S n ω / H n ω - 0‖ at hω
      change I ≤ ‖H n ω - I‖
      by_cases hz : H n ω = 0
      · simp [hz, Real.norm_eq_abs, abs_of_pos hI]
      · have he : S n ω / H n ω = E n ω := (div_eq_iff hz).mpr (by linarith)
        simp only [he, sub_self, sub_zero, norm_zero] at hω
        exact False.elim (not_le_of_gt hε hω)
    exact squeeze_zero (fun _ => measureReal_nonneg) hb
      (tendstoInMeasure_iff_measureReal_norm.mp hH I hI)
  exact tendstoInDistribution_of_tendstoInMeasure_sub E (fun ω => Z ω / I)
    (slutsky_div hI.ne' hS hH hHm) hdiff hEm

/-- L7's analytic and probabilistic argument for a consistent scalar score
root. Curvature is evaluated at the fixed true parameter only. A Lipschitz
bound and consistency prove that the effective curvature along the random
estimation interval has the same limit. -/
theorem consistent_score_root_limit
    (score curvature : ℕ → Ω → ℝ → ℝ) (T B : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set ℝ) (hD : Convex ℝ D) (θ₀ I M : ℝ) (hI : 0 < I) (hθ : θ₀ ∈ D)
    (hTin : ∀ n ω, T n ω ∈ D) (hTm : ∀ n, Measurable (T n))
    (hsm : ∀ n, Measurable (fun p : Ω × ℝ => score n p.1 p.2))
    (hBm : ∀ n, AEMeasurable (B n) P)
    (hcm : ∀ n, AEMeasurable (fun ω => curvature n ω θ₀) P)
    (hB0 : ∀ n ω, 0 ≤ B n ω)
    (hderiv : ∀ n ω θ, θ ∈ D → HasDerivWithinAt (score n ω) (curvature n ω θ) D θ)
    (hcurv : ∀ n ω θ, θ ∈ D →
      |curvature n ω θ - curvature n ω θ₀| ≤ B n ω * |θ - θ₀|)
    (hroot : ∀ n ω, score n ω (T n ω) = 0)
    (hT : ConvergesInProbability P T (fun _ => θ₀))
    (hB : ConvergesInProbability P B (fun _ => M))
    (hc : ConvergesInProbability P (fun n ω => curvature n ω θ₀) (fun _ => -I))
    {Z : Ω' → ℝ}
    (hscore : ConvergesInDistribution P Q (fun n ω => rate n * score n ω θ₀) Z) :
    ConvergesInDistribution P Q (fun n ω => rate n * (T n ω - θ₀)) (fun ω => Z ω / I) := by
  let H n ω := effectiveScoreCurvature (score n ω) θ₀ (T n ω) I
  let err n ω := B n ω * |T n ω - θ₀| + |curvature n ω θ₀ + I|
  have hTm' n : AEMeasurable (fun ω => |T n ω - θ₀|) P :=
    ((hTm n).sub_const θ₀).abs.aemeasurable
  have hTabs : ConvergesInProbability P (fun n ω => |T n ω - θ₀|) (fun _ => 0) := by
    simpa using continuous_mapping_probability_const
      (g := fun x => |x - θ₀|) (by fun_prop) hT
  have hprod : ConvergesInProbability P (fun n ω => B n ω * |T n ω - θ₀|) (fun _ => 0) :=
    slutsky_mul_zero (probability_implies_distribution hBm hB) hTabs hTm'
  have hcerr : ConvergesInProbability P (fun n ω => |curvature n ω θ₀ + I|) (fun _ => 0) := by
    simpa using continuous_mapping_probability_const (g := fun x => |x + I|) (by fun_prop) hc
  have herr : ConvergesInProbability P err (fun _ => 0) := by
    apply distribution_to_constant_implies_probability (Q := P)
    simpa only [err, add_zero, Pi.mul_apply] using! slutsky_add
      (probability_implies_distribution (fun n => (hBm n).mul (hTm' n)) hprod)
      hcerr (fun n => ((hcm n).add_const I).abs)
  have hbound n ω : |H n ω - I| ≤ err n ω :=
    effectiveScoreCurvature_bound hD hθ (hTin n ω) (hB0 n ω) (hderiv n ω) (hcurv n ω)
  have hH : ConvergesInProbability P H (fun _ => I) := by
    rw [ConvergesInProbability, tendstoInMeasure_iff_measureReal_norm]
    intro ε hε
    have hb n : P.real {ω | ε ≤ ‖H n ω - I‖} ≤ P.real {ω | ε ≤ ‖err n ω - 0‖} := by
      apply measureReal_mono _ (measure_ne_top P _)
      intro ω hω
      simp only [mem_setOf_eq, Real.norm_eq_abs, sub_zero] at hω ⊢
      exact hω.trans ((hbound n ω).trans (le_abs_self _))
    exact squeeze_zero (fun _ => measureReal_nonneg) hb
      (tendstoInMeasure_iff_measureReal_norm.mp herr ε hε)
  have hHm n : AEMeasurable (H n) P := by
    have hs₀ : Measurable (fun ω => score n ω θ₀) :=
      (hsm n).comp (measurable_id.prodMk measurable_const)
    have hst : Measurable (fun ω => score n ω (T n ω)) :=
      (hsm n).comp (measurable_id.prodMk (hTm n))
    apply Measurable.aemeasurable
    exact Measurable.ite (measurableSet_eq_fun (hTm n) measurable_const)
      measurable_const ((hs₀.sub hst).div ((hTm n).sub_const θ₀))
  apply score_root_limit_allow_zero_curvature hI hscore hH hHm
    (fun n => ((hTm n).sub_const θ₀).aemeasurable.const_mul (rate n))
  intro n
  apply ae_of_all
  intro ω
  change H n ω * (rate n * (T n ω - θ₀)) = rate n * score n ω θ₀
  rw [mul_left_comm, effectiveScoreCurvature_identity, hroot n ω, sub_zero]

end LectureNotes
