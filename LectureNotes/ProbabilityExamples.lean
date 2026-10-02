import LectureNotes.Foundations

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory Set
open scoped NNReal

/-- The number unemployed among ten surveyed people is an integer from 0 to 10. -/
abbrev EmploymentCount := Fin 11

/-- Strictly more than thirty percent of ten respondents are unemployed. -/
def unemploymentAboveThirtyPercent : Set EmploymentCount :=
  {k | (3 : ℝ) / 10 < (k.val : ℝ) / 10}

theorem unemployment_event_exact :
    unemploymentAboveThirtyPercent = {4, 5, 6, 7, 8, 9, 10} := by
  ext k
  fin_cases k <;> norm_num [unemploymentAboveThirtyPercent, Fin.ext_iff]

theorem unemployment_event_measurable : MeasurableSet unemploymentAboveThirtyPercent :=
  (Set.to_countable _).measurableSet

/-- Nonnegative income and the closed income band in the source example. -/
def incomeBand : Set ℝ≥0 := Icc 30000 40000

theorem incomeBand_mem (income : ℝ≥0) :
    income ∈ incomeBand ↔ 30000 ≤ (income : ℝ) ∧ (income : ℝ) ≤ 40000 := by
  rfl

theorem incomeBand_measurable : MeasurableSet incomeBand := measurableSet_Icc

/-- The two sigma-algebra closure consequences stated immediately after
L1 Definition 1, using the actual measurable-space structure. -/
theorem sigma_algebra_empty_and_countable_intersections {Ω : Type*} [MeasurableSpace Ω]
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n)) :
    MeasurableSet (∅ : Set Ω) ∧ MeasurableSet (⋂ n, A n) :=
  ⟨MeasurableSet.empty, MeasurableSet.iInter hA⟩

end LectureNotes
