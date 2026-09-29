import LectureNotes.Foundations

set_option autoImplicit false

/-! L12 updating by a likelihood. Normalization is proved and explicitly
requires positive finite evidence. Null *sets* under the prior stay null;
zero prior mass at a point in a continuous model is not an inconsistency result. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
variable {Θ : Type*} [MeasurableSpace Θ]

def evidence (π : Measure Θ) (L : Θ → ℝ) : ℝ := ∫ θ, L θ ∂π

def bayesUpdate (π : Measure Θ) (L : Θ → ℝ) : Measure Θ :=
  π.withDensity (fun θ => ENNReal.ofReal (L θ / evidence π L))

theorem bayesUpdate_isProbabilityMeasure (π : Measure Θ) (L : Θ → ℝ)
    (hi : Integrable L π) (hn : ∀ᵐ θ ∂π, 0 ≤ L θ) (he : 0 < evidence π L) :
    IsProbabilityMeasure (bayesUpdate π L) := by
  constructor
  rw [bayesUpdate, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (hn.mono (fun θ hθ => div_nonneg hθ he.le)), integral_div]
  change ENNReal.ofReal (evidence π L / evidence π L) = 1
  simp [he.ne']

theorem bayesUpdate_integral (π : Measure Θ) (L g : Θ → ℝ)
    (hL : AEMeasurable L π) (hn : ∀ᵐ θ ∂π, 0 ≤ L θ) (he : 0 < evidence π L) :
    (∫ θ, g θ ∂bayesUpdate π L) = (∫ θ, g θ * L θ ∂π) / evidence π L := by
  rw [bayesUpdate, integral_withDensity_eq_integral_toReal_smul₀
    (hL.div_const _).ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [hn] with θ hθ
  simp [ENNReal.toReal_ofReal (div_nonneg hθ he.le), smul_eq_mul]
  ring

theorem bayesUpdate_absolutelyContinuous (π : Measure Θ) (L : Θ → ℝ) :
    bayesUpdate π L ≪ π := withDensity_absolutelyContinuous _ _

theorem prior_null_set_stays_null (π : Measure Θ) (L : Θ → ℝ)
    {A : Set Θ} (hA : π A = 0) : bayesUpdate π L A = 0 :=
  bayesUpdate_absolutelyContinuous π L hA

/-- Multiplicative constants independent of θ cancel from Bayesian updating. -/
theorem bayesUpdate_scale (π : Measure Θ) (L : Θ → ℝ) {c : ℝ} (hc : c ≠ 0) :
    bayesUpdate π (fun θ => c * L θ) = bayesUpdate π L := by
  unfold bayesUpdate evidence
  rw [integral_const_mul]
  congr 1
  funext θ
  congr 1
  exact mul_div_mul_left (L θ) (∫ x, L x ∂π) hc

/-- L12 normal-normal parameters, expressed using precision. Positive prior
and sampling precisions prevent a degenerate denominator. -/
def normalPosteriorMean (samplePrecision priorPrecision sampleMean priorMean : ℝ) : ℝ :=
  (samplePrecision * sampleMean + priorPrecision * priorMean) /
    (samplePrecision + priorPrecision)

def normalPosteriorVariance (samplePrecision priorPrecision : ℝ) : ℝ :=
  1 / (samplePrecision + priorPrecision)

theorem normal_posterior_weight_sum (a b : ℝ) (h : a + b ≠ 0) :
    a / (a + b) + b / (a + b) = 1 := by rw [← add_div, div_self h]

theorem normal_posterior_complete_square (a b m μ θ : ℝ) (h : a + b ≠ 0) :
    a * (θ - m) ^ 2 + b * (θ - μ) ^ 2 =
      (a + b) * (θ - normalPosteriorMean a b m μ) ^ 2 +
        (a * b / (a + b)) * (m - μ) ^ 2 := by
  unfold normalPosteriorMean
  field_simp
  <;> ring

/-- Gamma parameters in the notes use shape and *scale*, not rate. -/
def gammaPosteriorShape (α sumX : ℝ) : ℝ := α + sumX
def gammaPosteriorScale (β n : ℝ) : ℝ := β / (n * β + 1)

theorem gamma_posterior_scale (β n : ℝ) (hβ : β ≠ 0) :
    gammaPosteriorScale β n = 1 / (n + 1 / β) := by
  unfold gammaPosteriorScale
  field_simp
  <;> ring

theorem gamma_posterior_mean_weighted (α β n m : ℝ) :
    gammaPosteriorShape α (n * m) * gammaPosteriorScale β n =
      (n * β / (n * β + 1)) * m + (1 / (n * β + 1)) * (α * β) := by
  unfold gammaPosteriorShape gammaPosteriorScale
  ring

end LectureNotes
