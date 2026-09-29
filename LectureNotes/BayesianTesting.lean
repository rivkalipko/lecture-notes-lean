import LectureNotes.BayesianDecision

set_option autoImplicit false

/-! L12 posterior-odds decisions. Comparing posterior probabilities at cutoff
one is optimal for equal error costs. Unequal costs change the comparison. -/
noncomputable section
namespace LectureNotes
open MeasureTheory Set
variable {Θ : Type*} [MeasurableSpace Θ]

/-- `true` is rejection of H₀. A false rejection costs c₀; a false acceptance
costs c₁; correct decisions cost zero. -/
def binaryTestingLoss (H₀ : Set Θ) (c₀ c₁ : ℝ) (reject : Bool) (θ : Θ) : ℝ :=
  if reject then H₀.indicator (fun _ => c₀) θ else H₀ᶜ.indicator (fun _ => c₁) θ

theorem binaryTestingLoss_nonneg (H₀ : Set Θ) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (reject : Bool) (θ : Θ) :
    0 ≤ binaryTestingLoss H₀ c₀ c₁ reject θ := by
  cases reject <;> simp only [binaryTestingLoss, Bool.false_eq_true, ↓reduceIte]
  · exact indicator_nonneg (fun _ _ => hc₁) _
  · exact indicator_nonneg (fun _ _ => hc₀) _

theorem binary_posterior_risk (post : Measure Θ) (H₀ : Set Θ) (hH₀ : MeasurableSet H₀)
    (c₀ c₁ : ℝ) (reject : Bool) :
    (∫ θ, binaryTestingLoss H₀ c₀ c₁ reject θ ∂post) =
      if reject then post.real H₀ * c₀ else post.real H₀ᶜ * c₁ := by
  cases reject <;> simp only [binaryTestingLoss, Bool.false_eq_true, ↓reduceIte]
  · rw [integral_indicator_const _ hH₀.compl, smul_eq_mul]
  · rw [integral_indicator_const _ hH₀, smul_eq_mul]

def posteriorOddsReject (post : Measure Θ) (H₀ : Set Θ) (c₀ c₁ : ℝ) : Bool := by
  classical
  exact decide (post.real H₀ * c₀ < post.real H₀ᶜ * c₁)

/-- The posterior-odds rule minimizes actual expected testing loss. With a
probability posterior and finite costs these integrals are always finite. -/
theorem posterior_odds_minimizes_risk (post : Measure Θ) [IsProbabilityMeasure post]
    (H₀ : Set Θ) (hH₀ : MeasurableSet H₀) (c₀ c₁ : ℝ) (reject : Bool) :
    (∫ θ, binaryTestingLoss H₀ c₀ c₁ (posteriorOddsReject post H₀ c₀ c₁) θ ∂post) ≤
      ∫ θ, binaryTestingLoss H₀ c₀ c₁ reject θ ∂post := by
  rw [binary_posterior_risk post H₀ hH₀, binary_posterior_risk post H₀ hH₀]
  classical
  by_cases h : post.real H₀ * c₀ < post.real H₀ᶜ * c₁
  · cases reject <;> simp [posteriorOddsReject, h, h.le]
  · cases reject <;> simp [posteriorOddsReject, h, le_of_not_gt h]

/-- The source's accept-if-null-probability-is-larger rule uses equal costs.
Equality is resolved in favor of accepting the null. -/
theorem posterior_odds_symmetric (post : Measure Θ) (H₀ : Set Θ) :
    posteriorOddsReject post H₀ 1 1 = false ↔ post.real H₀ᶜ ≤ post.real H₀ := by
  classical
  simp [posteriorOddsReject]

end LectureNotes
