import LectureNotes.ProbabilityLaws

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- L1 Definition 4: the real conditional-probability ratio is the event
probability under the normalized restriction measure. The equality respects
the shared zero convention when the conditioning event is null. -/
theorem conditionalProbability_eq_cond_real {A B : Set Ω} (hB : MeasurableSet B) :
    conditionalProbability P A B = (P[|B]).real A := by
  simp [conditionalProbability, Measure.real, cond_apply hB, ENNReal.toReal_mul,
    ENNReal.toReal_inv, div_eq_mul_inv, inter_comm, mul_comm]

/-- A positive conditioning event gives an actual probability measure. -/
theorem conditionalProbability_measure_probability {B : Set Ω} (hB : P.real B ≠ 0) :
    IsProbabilityMeasure (P[|B]) := by
  apply cond_isProbabilityMeasure
  intro hz
  exact hB (by simp [Measure.real, hz])

/-- Complementation for conditional probabilities requires a nonnull
conditioning event. -/
theorem conditionalProbability_complement {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hpos : P.real B ≠ 0) :
    conditionalProbability P Aᶜ B = 1 - conditionalProbability P A B := by
  have : IsProbabilityMeasure (P[|B]) := conditionalProbability_measure_probability P hpos
  simpa only [conditionalProbability_eq_cond_real P hB] using
    (probReal_compl_eq_one_sub (μ := P[|B]) hA)

/-- The two-event partition used in the denominator of L1 Theorem 3's
displayed Bayes formula. Both conditional terms have positive denominators. -/
theorem total_probability_complement {A B : Set Ω} (hB : MeasurableSet B)
    (hpos : P.real B ≠ 0) (hcomp : P.real Bᶜ ≠ 0) :
    P.real A = conditionalProbability P A B * P.real B +
      conditionalProbability P A Bᶜ * P.real Bᶜ := by
  rw [conditional_probability P hpos, conditional_probability P hcomp]
  simpa only [sdiff_eq] using (measureReal_inter_add_sdiff (μ := P) (s := A) hB).symm

/-- L1 Theorem 3, in the exact displayed two-event form. -/
theorem bayes_complement_denominator {A B : Set Ω} (hB : MeasurableSet B)
    (hApos : P.real A ≠ 0) (hBpos : P.real B ≠ 0) (hBcpos : P.real Bᶜ ≠ 0) :
    conditionalProbability P B A =
      conditionalProbability P A B * P.real B /
        (conditionalProbability P A B * P.real B +
          conditionalProbability P A Bᶜ * P.real Bᶜ) := by
  rw [← total_probability_complement P hB hBpos hBcpos]
  exact bayes P hBpos hApos

/-- The first CDF identity following L1 Definition 8, including atoms and
coincident endpoints: the left endpoint is open and the right endpoint closed. -/
theorem cdfOf_sub_eq_interval_probability {X : Ω → ℝ} (hX : Measurable X)
    {a b : ℝ} (hab : a ≤ b) :
    cdfOf P X b - cdfOf P X a = P.real {ω | a < X ω ∧ X ω ≤ b} := by
  have hs : {ω | X ω ≤ a} ⊆ {ω | X ω ≤ b} := fun ω hω => hω.trans hab
  have he : {ω | X ω ≤ b} \ {ω | X ω ≤ a} = {ω | a < X ω ∧ X ω ≤ b} := by
    ext ω
    simp only [mem_sdiff, mem_ofPred_eq, not_le]
    exact and_comm
  have hm := measureReal_sdiff (μ := P) hs (measurableSet_le hX measurable_const)
  rw [he] at hm
  exact hm.symm

end LectureNotes
