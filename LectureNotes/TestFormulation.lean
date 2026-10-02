import LectureNotes.LikelihoodRatio
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open Set

/-- Equivalent formulations of a null set give the same actual likelihood
ratio, since its constrained supremum depends only on that set. -/
theorem likelihoodRatio_null_formulation {Θ Ω A B : Type*} [Zero A] [Zero B]
    (L : Ω → Θ → ℝ) (g : Θ → A) (h : Θ → B)
    (he : ∀ θ, g θ = 0 ↔ h θ = 0) (x : Ω) :
    likelihoodRatio L {θ | g θ = 0} x = likelihoodRatio L {θ | h θ = 0} x := by
  have hs : {θ | g θ = 0} = {θ | h θ = 0} := by ext θ; exact he θ
  rw [hs]

/-- The LM statistic depends on the selected restricted estimate, its score
and information; relabeling equations defining the same null changes none
of these quantities. -/
theorem scalarScoreStatistic_restricted_estimate_congr {Θ : Type*}
    (S I : Θ → ℝ) {u v : Θ} (huv : u = v) :
    scalarScoreStatistic (S u) (I u) = scalarScoreStatistic (S v) (I v) := by rw [huv]

/-- A smooth change in a scalar restriction, retaining its same zero set. -/
def cubicRestriction (θ : ℝ) : ℝ := θ + θ ^ 3

theorem cubicRestriction_zero_iff (θ : ℝ) : cubicRestriction θ = 0 ↔ θ = 0 := by
  have hp : 0 < 1 + θ ^ 2 := by positivity
  rw [cubicRestriction, show θ + θ ^ 3 = θ * (1 + θ ^ 2) by ring, mul_eq_zero]
  simp [hp.ne']

theorem cubicRestriction_hasDerivAt (θ : ℝ) :
    HasDerivAt cubicRestriction (1 + 3 * θ ^ 2) θ := by
  simpa [cubicRestriction] using! (hasDerivAt_id θ).add ((hasDerivAt_id θ).pow 3)

/-- Both restrictions have nonzero derivative at the null and at the given
estimate. Nevertheless their plug-in Wald values differ: the delta covariance
is evaluated at the estimate, as in the lecture. -/
theorem wald_not_invariant_under_null_formulation {n : ℝ} (hn : 0 < n) :
    (∀ θ, cubicRestriction θ = 0 ↔ θ = 0) ∧
    deriv cubicRestriction 0 = 1 ∧
    scalarWald n 1 0 1 = n ∧
    scalarWald n (cubicRestriction 1) 0 ((deriv cubicRestriction 1) ^ 2) = n / 4 ∧
    scalarWald n (cubicRestriction 1) 0 ((deriv cubicRestriction 1) ^ 2) <
      scalarWald n 1 0 1 := by
  have hd0 := (cubicRestriction_hasDerivAt 0).deriv
  have hd1 := (cubicRestriction_hasDerivAt 1).deriv
  norm_num at hd0 hd1
  refine ⟨cubicRestriction_zero_iff, hd0, ?_, ?_, ?_⟩
  · simp [scalarWald]
  · simp [scalarWald, cubicRestriction, hd1]
    ring
  · simp [scalarWald, cubicRestriction, hd1]
    linarith

end LectureNotes
