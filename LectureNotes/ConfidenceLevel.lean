import LectureNotes.ConfidenceSets

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory Set

/-- L11 Definition 2: the confidence level is the infimum of coverage over
all true parameters. A minimum need not be attained. The statistical theorems
below use a nonempty parameter space. -/
def confidenceLevel {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (P : Θ → Measure Ω) (C : Ω → Set Θ) : ℝ :=
  ⨅ θ, coverage P C θ

/-- Confidence level never exceeds coverage at any given parameter. -/
theorem confidenceLevel_le_coverage {Ω Θ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ]
    (P : Θ → Measure Ω) (C : Ω → Set Θ) (θ : Θ) :
    confidenceLevel P C ≤ coverage P C θ := by
  apply ciInf_le
  exact ⟨0, fun _ ⟨θ, hθ⟩ => hθ ▸ ENNReal.toReal_nonneg⟩

/-- The numerical infimum agrees with the project's coverage-level predicate. -/
theorem hasConfidenceLevel_iff_le_confidenceLevel {Ω Θ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [Nonempty Θ]
    (P : Θ → Measure Ω) (C : Ω → Set Θ) (γ : ℝ) :
    HasConfidenceLevel P C γ ↔ γ ≤ confidenceLevel P C := by
  constructor
  · intro h
    exact le_ciInf h
  · intro h θ
    exact h.trans (confidenceLevel_le_coverage P C θ)

/-- A confidence level is a probability, even if its infimum is unattained. -/
theorem confidenceLevel_bounds {Ω Θ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [Nonempty Θ]
    (P : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (P θ)] (C : Ω → Set Θ) :
    0 ≤ confidenceLevel P C ∧ confidenceLevel P C ≤ 1 := by
  refine ⟨le_ciInf (fun _ => ENNReal.toReal_nonneg), ?_⟩
  obtain ⟨θ⟩ := ‹Nonempty Θ›
  exact (confidenceLevel_le_coverage P C θ).trans (prob_bounds (P θ) _).2

/-- Exact parameter-independent coverage gives that exact confidence level. -/
theorem confidenceLevel_eq_of_coverage_const {Ω Θ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [Nonempty Θ]
    (P : Θ → Measure Ω) (C : Ω → Set Θ) {γ : ℝ}
    (h : ∀ θ, coverage P C θ = γ) : confidenceLevel P C = γ := by
  unfold confidenceLevel
  simp_rw [h]
  exact ciInf_const

end LectureNotes
