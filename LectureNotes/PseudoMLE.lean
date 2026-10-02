import LectureNotes.IIDScoreAsymptotics

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

/-- Expected log density ratio under the true observation law. When this law
has density `g`, this is the usual relative-entropy contrast against `f`. -/
def expectedLogDensityRatio {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (g f : Ξ → ℝ) : ℝ := ∫ x, Real.log (g x / f x) ∂μ

theorem expectedLogDensityRatio_eq {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (g f : Ξ → ℝ)
    (hg : ∀ᵐ x ∂μ, 0 < g x) (hf : ∀ᵐ x ∂μ, 0 < f x)
    (hgi : Integrable (fun x => Real.log (g x)) μ)
    (hfi : Integrable (fun x => Real.log (f x)) μ) :
    expectedLogDensityRatio μ g f = (∫ x, Real.log (g x) ∂μ) - ∫ x, Real.log (f x) ∂μ := by
  unfold expectedLogDensityRatio
  rw [← integral_sub hgi hfi]
  apply integral_congr_ae
  filter_upwards [hg, hf] with x hx hy
  exact Real.log_div hx.ne' hy.ne'

/-- Maximizing the population log likelihood is equivalent to minimizing the
log-density-ratio contrast, under explicit integrability and positivity. -/
theorem population_log_max_iff_log_ratio_min {Ξ Θ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (g : Ξ → ℝ) (f : Θ → Ξ → ℝ) (θ₀ : Θ)
    (hg : ∀ᵐ x ∂μ, 0 < g x) (hf : ∀ θ, ∀ᵐ x ∂μ, 0 < f θ x)
    (hgi : Integrable (fun x => Real.log (g x)) μ)
    (hfi : ∀ θ, Integrable (fun x => Real.log (f θ x)) μ) :
    (∀ θ, (∫ x, Real.log (f θ x) ∂μ) ≤ ∫ x, Real.log (f θ₀ x) ∂μ) ↔
      ∀ θ, expectedLogDensityRatio μ g (f θ₀) ≤ expectedLogDensityRatio μ g (f θ) := by
  simp_rw [expectedLogDensityRatio_eq μ g _ hg (hf _) hgi (hfi _)]
  constructor <;> intro h θ <;> have hh := h θ <;> linarith

variable {Ω Ω' Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ξ]
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- A consistent scalar score root has sandwich variance `J/H²`. The IID
score CLT and curvature/envelope LLNs are derived from explicit moments;
score variance and negative mean curvature may differ. -/
theorem iid_consistent_score_root_sandwich
    (X : ℕ → Ω → Ξ) (score curvature third : Ξ → ℝ → ℝ) (envelope : Ξ → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (D : Set ℝ) (hD : Convex ℝ D) (θ₀ : ℝ) (hθ : θ₀ ∈ D)
    (H J : ℝ≥0) (hH : 0 < H)
    (hsm : Measurable (Function.uncurry score))
    (hcm : Measurable (fun x => curvature x θ₀)) (hem : Measurable envelope)
    (he0 : ∀ x, 0 ≤ envelope x)
    (hsd : ∀ x θ, θ ∈ D → HasDerivWithinAt (score x) (curvature x θ) D θ)
    (hcd : ∀ x θ, θ ∈ D → HasDerivWithinAt (curvature x) (third x θ) D θ)
    (hthird : ∀ x θ, θ ∈ D → |third x θ| ≤ envelope x)
    (hs₂ : MemLp (fun ω => score (X 0 ω) θ₀) 2 P)
    (hsmean : (∫ ω, score (X 0 ω) θ₀ ∂P) = 0)
    (hsvar : Var[fun ω => score (X 0 ω) θ₀; P] = J)
    (hcint : Integrable (fun ω => curvature (X 0 ω) θ₀) P)
    (hcmean : (∫ ω, curvature (X 0 ω) θ₀ ∂P) = -(H : ℝ))
    (heint : Integrable (fun ω => envelope (X 0 ω)) P)
    (T : ℕ → Ω → ℝ) (hTin : ∀ n ω, T n ω ∈ D) (hTm : ∀ n, Measurable (T n))
    (hT : ConvergesInProbability P T (fun _ => θ₀))
    (hroot : ∀ n ω, sampleCriterionAverage X score n ω (T n ω) = 0)
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 J) Q) :
    ConvergesInDistribution P Q (fun n ω => Real.sqrt n * (T n ω - θ₀))
      (fun ω => Z ω / H) ∧
        HasLaw (fun ω => Z ω / H) (gaussianReal 0 (J / H ^ 2)) Q := by
  let B n ω := (∑ i ∈ Finset.range n, envelope (X i ω)) / n
  have hBmeas n : Measurable (B n) :=
    (Finset.measurable_sum _ (fun i _ => hem.comp (hX i))).div_const (n : ℝ)
  have hCmeas n : Measurable (fun ω => sampleCriterionAverage X curvature n ω θ₀) :=
    (Finset.measurable_sum _ (fun i _ => hcm.comp (hX i))).div_const (n : ℝ)
  have hscore0 : Measurable (fun x => score x θ₀) :=
    hsm.comp (measurable_id.prodMk measurable_const)
  have hcurv x θ (hθ' : θ ∈ D) :
      |curvature x θ - curvature x θ₀| ≤ envelope x * |θ - θ₀| := by
    simpa only [Real.norm_eq_abs] using hD.norm_image_sub_le_of_norm_hasDerivWithin_le
      (hcd x) (by simpa only [Real.norm_eq_abs] using hthird x) hθ hθ'
  refine ⟨?_, ?_⟩
  · apply consistent_score_root_limit
      (sampleCriterionAverage X score) (sampleCriterionAverage X curvature) T B
      (fun n => Real.sqrt n) D hD θ₀ H (∫ ω, envelope (X 0 ω) ∂P)
      (by exact_mod_cast hH) hθ hTin hTm
      (sampleCriterionAverage_measurable X score hX hsm)
      (fun n => (hBmeas n).aemeasurable) (fun n => (hCmeas n).aemeasurable)
    · intro n ω
      exact div_nonneg (Finset.sum_nonneg (fun i _ => he0 (X i ω))) (Nat.cast_nonneg n)
    · exact sampleCriterionAverage_derivative X score curvature D hsd
    · exact sampleCriterionAverage_lipschitz X curvature envelope D θ₀ hcurv
    · exact hroot
    · exact hT
    · exact iid_statistic_average_limit X envelope hX hem hind hident heint
    · simpa only [sampleCriterionAverage, hcmean] using
        iid_statistic_average_limit X (fun x => curvature x θ₀) hX hcm hind hident hcint
    · exact iid_zero_mean_score_clt X (fun x => score x θ₀) hscore0 hind hident
        hs₂ hsmean hsvar hZ
  · simpa only [zero_div] using! gaussianReal_div_const hZ (H : ℝ)

/-- Scalar pseudo-MLE asymptotic normality from maximization of a supplied
criterion. Consistency and interior maximization are explicit; the first-order
equation and asymptotic variance are proved without an information identity. -/
theorem iid_pseudo_mle_asymptotic_normality
    (X : ℕ → Ω → Ξ) (logDensity score curvature third : Ξ → ℝ → ℝ)
    (envelope : Ξ → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (D : Set ℝ) (hD : Convex ℝ D) (hDopen : IsOpen D) (θ₀ : ℝ) (hθ : θ₀ ∈ D)
    (H J : ℝ≥0) (hH : 0 < H)
    (hsm : Measurable (Function.uncurry score))
    (hcm : Measurable (fun x => curvature x θ₀)) (hem : Measurable envelope)
    (he0 : ∀ x, 0 ≤ envelope x)
    (hld : ∀ x θ, θ ∈ D → HasDerivWithinAt (logDensity x) (score x θ) D θ)
    (hsd : ∀ x θ, θ ∈ D → HasDerivWithinAt (score x) (curvature x θ) D θ)
    (hcd : ∀ x θ, θ ∈ D → HasDerivWithinAt (curvature x) (third x θ) D θ)
    (hthird : ∀ x θ, θ ∈ D → |third x θ| ≤ envelope x)
    (hs₂ : MemLp (fun ω => score (X 0 ω) θ₀) 2 P)
    (hsmean : (∫ ω, score (X 0 ω) θ₀ ∂P) = 0)
    (hsvar : Var[fun ω => score (X 0 ω) θ₀; P] = J)
    (hcint : Integrable (fun ω => curvature (X 0 ω) θ₀) P)
    (hcmean : (∫ ω, curvature (X 0 ω) θ₀ ∂P) = -(H : ℝ))
    (heint : Integrable (fun ω => envelope (X 0 ω)) P)
    (T : ℕ → Ω → ℝ) (hTin : ∀ n ω, T n ω ∈ D) (hTm : ∀ n, Measurable (T n))
    (hT : ConvergesInProbability P T (fun _ => θ₀))
    (hmax : ∀ n ω θ, θ ∈ D → sampleCriterionAverage X logDensity n ω θ ≤
      sampleCriterionAverage X logDensity n ω (T n ω))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 J) Q) :
    ConvergesInDistribution P Q (fun n ω => Real.sqrt n * (T n ω - θ₀))
      (fun ω => Z ω / H) ∧
        HasLaw (fun ω => Z ω / H) (gaussianReal 0 (J / H ^ 2)) Q := by
  exact iid_consistent_score_root_sandwich X score curvature third envelope hX hind hident
    D hD θ₀ hθ H J hH hsm hcm hem he0 hsd hcd hthird hs₂ hsmean hsvar hcint hcmean heint
    T hTin hTm hT
    (fun n ω => sample_score_zero_at_interior_maximum X logDensity score D hDopen hld
      n ω (T n ω) (hTin n ω) (hmax n ω)) hZ

end LectureNotes
