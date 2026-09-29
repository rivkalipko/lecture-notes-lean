import LectureNotes.IIDScoreAsymptotics

set_option autoImplicit false

/-! L10 scalar likelihood-ratio asymptotics. The quadratic approximation is
derived from first and second derivatives, with an explicit curvature error.
No measurable choice of a Taylor remainder point is needed. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

/-- Two applications of the mean value inequality prove a quadratic error
bound around a stationary point. The leading coefficient I/2 is exact; the
inessential factor 2 in the remainder avoids selecting a Taylor point. -/
theorem likelihood_quadratic_error {f score curvature : ℝ → ℝ} {D : Set ℝ}
    (hD : Convex ℝ D) {θ₀ t I B : ℝ} (hθ : θ₀ ∈ D) (ht : t ∈ D) (hB : 0 ≤ B)
    (hf : ∀ θ ∈ D, HasDerivWithinAt f (score θ) D θ)
    (hs : ∀ θ ∈ D, HasDerivWithinAt score (curvature θ) D θ)
    (hcurv : ∀ θ ∈ D, |curvature θ - curvature θ₀| ≤ B * |θ - θ₀|)
    (hroot : score t = 0) :
    |2 * (f t - f θ₀) - I * (t - θ₀) ^ 2| ≤
      2 * (B * |t - θ₀| + |curvature θ₀ + I|) * (t - θ₀) ^ 2 := by
  let err := B * |t - θ₀| + |curvature θ₀ + I|
  let g θ := f θ + I / 2 * (θ - t) ^ 2
  let g' θ := score θ + I * (θ - t)
  have hsub : uIcc θ₀ t ⊆ D := hD.ordConnected.uIcc_subset hθ ht
  have herr : 0 ≤ err := by dsimp [err]; positivity
  have hg θ (hseg : θ ∈ uIcc θ₀ t) : HasDerivWithinAt g (g' θ) (uIcc θ₀ t) θ := by
    have hd := ((hf θ (hsub hseg)).mono hsub).add
      ((((hasDerivAt_id θ).sub_const t).pow 2).const_mul (I / 2)).hasDerivWithinAt
    convert! hd using 1 <;> dsimp [g, g'] <;> ring
  have hg' θ (hseg : θ ∈ uIcc θ₀ t) :
      HasDerivWithinAt g' (curvature θ + I) (uIcc θ₀ t) θ := by
    simpa [g'] using! ((hs θ (hsub hseg)).mono hsub).add
      (((hasDerivAt_id θ).sub_const t).const_mul I).hasDerivWithinAt
  have hcb θ (hseg : θ ∈ uIcc θ₀ t) : ‖curvature θ + I‖ ≤ err := by
    have h₁ := hcurv θ (hsub hseg)
    have h₂ := mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hseg) hB
    have h₃ := abs_add_le (curvature θ - curvature θ₀) (curvature θ₀ + I)
    have he : curvature θ - curvature θ₀ + (curvature θ₀ + I) = curvature θ + I := by ring
    rw [he] at h₃
    rw [Real.norm_eq_abs]
    dsimp [err]
    linarith
  have hgb θ (hseg : θ ∈ uIcc θ₀ t) : ‖g' θ‖ ≤ err * |t - θ₀| := by
    have h := (convex_uIcc θ₀ t).norm_image_sub_le_of_norm_hasDerivWithin_le
      hg' hcb right_mem_uIcc hseg
    have hg't : g' t = 0 := by simp [g', hroot]
    rw [hg't, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ herr
    rw [abs_sub_comm θ t]
    exact abs_sub_right_of_mem_uIcc hseg
  have h := (convex_uIcc θ₀ t).norm_image_sub_le_of_norm_hasDerivWithin_le
    hg hgb right_mem_uIcc left_mem_uIcc
  simp only [Real.norm_eq_abs] at h
  have he : 2 * (f t - f θ₀) - I * (t - θ₀) ^ 2 = -2 * (g θ₀ - g t) := by
    dsimp [g]
    ring
  rw [he, abs_mul]
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |g θ₀ - g t| ≤ 2 * ((err * |t - θ₀|) * |θ₀ - t|) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 2 * err * (t - θ₀) ^ 2 := by
      rw [abs_sub_comm θ₀ t, mul_assoc err, ← pow_two, sq_abs]
      ring

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

theorem curvature_error_limit {T B C : ℕ → Ω → ℝ} {θ₀ I M : ℝ}
    (hTm : ∀ n, AEMeasurable (T n) P) (hBm : ∀ n, AEMeasurable (B n) P)
    (hCm : ∀ n, AEMeasurable (C n) P)
    (hT : ConvergesInProbability P T (fun _ => θ₀))
    (hB : ConvergesInProbability P B (fun _ => M))
    (hC : ConvergesInProbability P C (fun _ => -I)) :
    ConvergesInProbability P (fun n ω => B n ω * |T n ω - θ₀| + |C n ω + I|)
      (fun _ => 0) := by
  have ht : ConvergesInProbability P (fun n ω => |T n ω - θ₀|) (fun _ => 0) := by
    simpa using continuous_mapping_probability_const (g := fun x => |x - θ₀|) (by fun_prop) hT
  have hp := slutsky_mul_zero (probability_implies_distribution hBm hB) ht
    (fun n => ((hTm n).sub_const θ₀).abs)
  have hc : ConvergesInProbability P (fun n ω => |C n ω + I|) (fun _ => 0) := by
    simpa using continuous_mapping_probability_const (g := fun x => |x + I|) (by fun_prop) hC
  apply distribution_to_constant_implies_probability (Q := P)
  simpa only [add_zero, Pi.mul_apply] using! slutsky_add
    (probability_implies_distribution (fun n => (hBm n).mul (((hTm n).sub_const θ₀).abs)) hp)
    hc (fun n => ((hCm n).add_const I).abs)

theorem probability_zero_of_abs_le {U V : ℕ → Ω → ℝ}
    (hbound : ∀ n ω, |U n ω| ≤ V n ω)
    (hV : ConvergesInProbability P V (fun _ => 0)) :
    ConvergesInProbability P U (fun _ => 0) := by
  rw [ConvergesInProbability, tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hb n : P.real {ω | ε ≤ ‖U n ω - 0‖} ≤ P.real {ω | ε ≤ ‖V n ω - 0‖} := by
    apply measureReal_mono _ (measure_ne_top P _)
    intro ω hω
    simp only [mem_setOf_eq, Real.norm_eq_abs, sub_zero] at hω ⊢
    exact hω.trans ((hbound n ω).trans (le_abs_self _))
  exact squeeze_zero (fun _ => measureReal_nonneg) hb
    (tendstoInMeasure_iff_measureReal_norm.mp hV ε hε)

theorem information_scaled_normal_square {Z : Ω' → ℝ} (I : ℝ≥0) (hI : 0 < I)
    (hZ : HasLaw Z (gaussianReal 0 I⁻¹) Q) :
    HasLaw (fun ω => (I : ℝ) * Z ω ^ 2) (chiSquared 1) Q := by
  have hI0 : (I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  have hstd : HasLaw (fun ω => Real.sqrt I * Z ω) (gaussianReal 0 1) Q := by
    have h := gaussianReal_const_mul hZ (Real.sqrt I)
    convert! h using 1
    simp only [mul_zero]
    congr 1
    apply Subtype.ext
    change 1 = (Real.sqrt I) ^ 2 * (I : ℝ)⁻¹
    rw [Real.sq_sqrt I.coe_nonneg, mul_inv_cancel₀ hI0]
  simpa only [mul_pow, Real.sq_sqrt I.coe_nonneg] using standard_normal_square hstd

/-- Scalar Wilks from actual derivatives and likelihood values. The quadratic
expansion is proved from curvature control, and the limiting estimation law
can be supplied by `iid_mle_asymptotic_normality`. For rate = √n and f the
average log likelihood, the statistic is exactly 2n(f(Tₙ)−f(θ₀)). -/
theorem scalar_wilks_from_derivatives
    (f score curvature : ℕ → Ω → ℝ → ℝ) (T B : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set ℝ) (hD : Convex ℝ D) (θ₀ M : ℝ) (hθ : θ₀ ∈ D)
    (I : ℝ≥0) (hI : 0 < I)
    (hTin : ∀ n ω, T n ω ∈ D) (hTm : ∀ n, Measurable (T n))
    (hfm : ∀ n, Measurable (fun p : Ω × ℝ => f n p.1 p.2))
    (hBm : ∀ n, AEMeasurable (B n) P)
    (hcm : ∀ n, AEMeasurable (fun ω => curvature n ω θ₀) P)
    (hB0 : ∀ n ω, 0 ≤ B n ω)
    (hf : ∀ n ω θ, θ ∈ D → HasDerivWithinAt (f n ω) (score n ω θ) D θ)
    (hs : ∀ n ω θ, θ ∈ D → HasDerivWithinAt (score n ω) (curvature n ω θ) D θ)
    (hcurv : ∀ n ω θ, θ ∈ D →
      |curvature n ω θ - curvature n ω θ₀| ≤ B n ω * |θ - θ₀|)
    (hroot : ∀ n ω, score n ω (T n ω) = 0)
    (hT : ConvergesInProbability P T (fun _ => θ₀))
    (hB : ConvergesInProbability P B (fun _ => M))
    (hc : ConvergesInProbability P (fun n ω => curvature n ω θ₀) (fun _ => -(I : ℝ)))
    {Z : Ω' → ℝ}
    (hE : ConvergesInDistribution P Q (fun n ω => rate n * (T n ω - θ₀)) Z)
    (hZ : HasLaw Z (gaussianReal 0 I⁻¹) Q) :
    ConvergesInDistribution P Q
      (fun n ω => 2 * rate n ^ 2 * (f n ω (T n ω) - f n ω θ₀))
      (fun ω => (I : ℝ) * Z ω ^ 2) ∧
        HasLaw (fun ω => (I : ℝ) * Z ω ^ 2) (chiSquared 1) Q := by
  let err n ω := B n ω * |T n ω - θ₀| + |curvature n ω θ₀ + I|
  let E n ω := rate n * (T n ω - θ₀)
  let LR n ω := 2 * rate n ^ 2 * (f n ω (T n ω) - f n ω θ₀)
  have herr : ConvergesInProbability P err (fun _ => 0) :=
    curvature_error_limit (fun n => (hTm n).aemeasurable) hBm hcm hT hB hc
  have herrm n : AEMeasurable (err n) P :=
    ((hBm n).mul (((hTm n).aemeasurable.sub_const θ₀).abs)).add ((hcm n).add_const I).abs
  have hp : ConvergesInProbability P (fun n ω => E n ω ^ 2 * err n ω) (fun _ => 0) :=
    quadratic_statistics_equivalent hE herr herrm
  have htwo : ConvergesInProbability P (fun n ω => 2 * err n ω * E n ω ^ 2) (fun _ => 0) := by
    have h := continuous_mapping_probability_const (g := fun x => 2 * x) (by fun_prop) hp
    convert! h using 1 <;> try simp only [mul_zero]
    funext n ω
    ring
  have herror : ConvergesInProbability P (fun n ω => LR n ω - (I : ℝ) * E n ω ^ 2)
      (fun _ => 0) := by
    apply probability_zero_of_abs_le (V := fun n ω => 2 * err n ω * E n ω ^ 2) _ htwo
    intro n ω
    have h := likelihood_quadratic_error hD hθ (hTin n ω) (hB0 n ω)
      (hf n ω) (hs n ω) (hcurv n ω) (hroot n ω) (I := (I : ℝ))
    have he : LR n ω - (I : ℝ) * E n ω ^ 2 =
        rate n ^ 2 * (2 * (f n ω (T n ω) - f n ω θ₀) - I * (T n ω - θ₀) ^ 2) := by
      dsimp [LR, E]
      ring
    rw [he, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hm := mul_le_mul_of_nonneg_left h (sq_nonneg (rate n))
    calc
      _ ≤ rate n ^ 2 * (2 * err n ω * (T n ω - θ₀) ^ 2) := hm
      _ = 2 * err n ω * E n ω ^ 2 := by dsimp [E]; ring
  refine ⟨?_, information_scaled_normal_square I hI hZ⟩
  have hbase := continuous_mapping_distribution (g := fun x => (I : ℝ) * x ^ 2) (by fun_prop) hE
  apply tendstoInDistribution_of_tendstoInMeasure_sub LR (fun ω => (I : ℝ) * Z ω ^ 2)
    hbase herror
  intro n
  have hft : Measurable (fun ω => f n ω (T n ω)) :=
    (hfm n).comp (measurable_id.prodMk (hTm n))
  have hfθ : Measurable (fun ω => f n ω θ₀) :=
    (hfm n).comp (measurable_id.prodMk measurable_const)
  exact ((hft.sub hfθ).const_mul (2 * rate n ^ 2)).aemeasurable

/-- L10 T1 in the scalar IID case. The model hypotheses are the same explicit
derivative, information, envelope, and consistency conditions as the scalar
MLE theorem. This result derives the estimator limit and the likelihood
expansion instead of taking either as a premise. -/
theorem iid_scalar_wilks
    {Ξ : Type*} [MeasurableSpace Ξ]
    (X : ℕ → Ω → Ξ) (logDensity score curvature third : Ξ → ℝ → ℝ)
    (envelope : Ξ → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (D : Set ℝ) (hD : Convex ℝ D) (hDopen : IsOpen D) (θ₀ : ℝ) (hθ : θ₀ ∈ D)
    (I : ℝ≥0) (hI : 0 < I)
    (hlm : Measurable (Function.uncurry logDensity))
    (hsm : Measurable (Function.uncurry score))
    (hcm : Measurable (fun x => curvature x θ₀)) (hem : Measurable envelope)
    (he0 : ∀ x, 0 ≤ envelope x)
    (hld : ∀ x θ, θ ∈ D → HasDerivWithinAt (logDensity x) (score x θ) D θ)
    (hsd : ∀ x θ, θ ∈ D → HasDerivWithinAt (score x) (curvature x θ) D θ)
    (hcd : ∀ x θ, θ ∈ D → HasDerivWithinAt (curvature x) (third x θ) D θ)
    (hthird : ∀ x θ, θ ∈ D → |third x θ| ≤ envelope x)
    (hs₂ : MemLp (fun ω => score (X 0 ω) θ₀) 2 P)
    (hsmean : (∫ ω, score (X 0 ω) θ₀ ∂P) = 0)
    (hsvar : Var[fun ω => score (X 0 ω) θ₀; P] = I)
    (hcint : Integrable (fun ω => curvature (X 0 ω) θ₀) P)
    (hcmean : (∫ ω, curvature (X 0 ω) θ₀ ∂P) = -(I : ℝ))
    (heint : Integrable (fun ω => envelope (X 0 ω)) P)
    (T : ℕ → Ω → ℝ) (hTin : ∀ n ω, T n ω ∈ D) (hTm : ∀ n, Measurable (T n))
    (hT : ConvergesInProbability P T (fun _ => θ₀))
    (hmax : ∀ n ω θ, θ ∈ D → sampleCriterionAverage X logDensity n ω θ ≤
      sampleCriterionAverage X logDensity n ω (T n ω))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 I) Q) :
    ConvergesInDistribution P Q
      (fun n ω => 2 * n * (sampleCriterionAverage X logDensity n ω (T n ω) -
        sampleCriterionAverage X logDensity n ω θ₀))
      (fun ω => (I : ℝ) * (Z ω / I) ^ 2) ∧
        HasLaw (fun ω => (I : ℝ) * (Z ω / I) ^ 2) (chiSquared 1) Q := by
  obtain ⟨hE, hEZ⟩ := iid_mle_asymptotic_normality X logDensity score curvature third envelope
    hX hind hident D hD hDopen θ₀ hθ I hI hsm hcm hem he0 hld hsd hcd hthird
    hs₂ hsmean hsvar hcint hcmean heint T hTin hTm hT hmax hZ
  let B n ω := (∑ i ∈ Finset.range n, envelope (X i ω)) / n
  have hBmeas n : Measurable (B n) :=
    (Finset.measurable_sum _ (fun i _ => hem.comp (hX i))).div_const (n : ℝ)
  have hCmeas n : Measurable (fun ω => sampleCriterionAverage X curvature n ω θ₀) :=
    (Finset.measurable_sum _ (fun i _ => hcm.comp (hX i))).div_const (n : ℝ)
  have hcurv x θ (hθ' : θ ∈ D) :
      |curvature x θ - curvature x θ₀| ≤ envelope x * |θ - θ₀| := by
    simpa only [Real.norm_eq_abs] using hD.norm_image_sub_le_of_norm_hasDerivWithin_le
      (hcd x) (by simpa only [Real.norm_eq_abs] using hthird x) hθ hθ'
  have hBlim := iid_statistic_average_limit X envelope hX hem hind hident heint
  have hClim : ConvergesInProbability P (fun n ω => sampleCriterionAverage X curvature n ω θ₀)
      (fun _ => -(I : ℝ)) := by
    simpa only [sampleCriterionAverage, hcmean] using
      iid_statistic_average_limit X (fun x => curvature x θ₀) hX hcm hind hident hcint
  have h := scalar_wilks_from_derivatives
    (sampleCriterionAverage X logDensity) (sampleCriterionAverage X score)
    (sampleCriterionAverage X curvature) T B (fun n => Real.sqrt n) D hD θ₀
    (∫ ω, envelope (X 0 ω) ∂P) hθ I hI hTin hTm
    (sampleCriterionAverage_measurable X logDensity hX hlm)
    (fun n => (hBmeas n).aemeasurable) (fun n => (hCmeas n).aemeasurable)
    (fun n ω => div_nonneg (Finset.sum_nonneg (fun i _ => he0 (X i ω))) (Nat.cast_nonneg n))
    (sampleCriterionAverage_derivative X logDensity score D hld)
    (sampleCriterionAverage_derivative X score curvature D hsd)
    (sampleCriterionAverage_lipschitz X curvature envelope D θ₀ hcurv)
    (fun n ω => sample_score_zero_at_interior_maximum X logDensity score D hDopen hld
      n ω (T n ω) (hTin n ω) (hmax n ω)) hT hBlim hClim hE hEZ
  simpa only [Real.sq_sqrt (Nat.cast_nonneg _)] using h

end LectureNotes
