import LectureNotes.Foundations

set_option autoImplicit false

/-! L8–L9: tests, power, level, p-values, and multiplicity.
The notes use `C` for the acceptance set. Here rejection sets are named explicitly.
Randomization is a measurable rejection probability in the closed unit interval. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

structure StatisticalTest (Ω : Type*) [MeasurableSpace Ω] where
  reject : Ω → ℝ
  measurable_reject : Measurable reject
  nonneg : ∀ x, 0 ≤ reject x
  le_one : ∀ x, reject x ≤ 1

namespace StatisticalTest
variable {Ω : Type*} [MeasurableSpace Ω]

def power (φ : StatisticalTest Ω) (P : Measure Ω) : ℝ := ∫ x, φ.reject x ∂P

theorem integrable (φ : StatisticalTest Ω) (P : Measure Ω) [IsFiniteMeasure P] :
    Integrable φ.reject P := by
  apply Integrable.of_bound φ.measurable_reject.aestronglyMeasurable 1
  exact ae_of_all _ (fun x => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (φ.nonneg x)] using φ.le_one x)

theorem power_nonneg (φ : StatisticalTest Ω) (P : Measure Ω) : 0 ≤ φ.power P :=
  integral_nonneg φ.nonneg

theorem power_le_one (φ : StatisticalTest Ω) (P : Measure Ω) [IsProbabilityMeasure P] :
    φ.power P ≤ 1 := by
  simpa [power] using integral_mono (φ.integrable P) (integrable_const (1 : ℝ)) φ.le_one

def ofRejectionSet (R : Set Ω) (hR : MeasurableSet R) : StatisticalTest Ω where
  reject := R.indicator (fun _ => 1)
  measurable_reject := measurable_const.indicator hR
  nonneg x := by simp only [indicator]; split_ifs <;> norm_num
  le_one x := by simp only [indicator]; split_ifs <;> norm_num

theorem power_ofRejectionSet (R : Set Ω) (hR : MeasurableSet R)
    (P : Measure Ω) [IsProbabilityMeasure P] :
    (ofRejectionSet R hR).power P = P.real R := by
  simp [power, ofRejectionSet, integral_indicator hR, measureReal_def]

def HasLevel {Θ : Type*} (φ : StatisticalTest Ω) (P : Θ → Measure Ω)
    (null : Set Θ) (α : ℝ) : Prop := ∀ θ ∈ null, φ.power (P θ) ≤ α

def IsUMP {Θ : Type*} (φ : StatisticalTest Ω) (P : Θ → Measure Ω)
    (null alternative : Set Θ) (α : ℝ) : Prop :=
  φ.HasLevel P null α ∧ ∀ ψ : StatisticalTest Ω, ψ.HasLevel P null α →
    ∀ θ ∈ alternative, ψ.power (P θ) ≤ φ.power (P θ)

def IsUnbiased {Θ : Type*} (φ : StatisticalTest Ω) (P : Θ → Measure Ω)
    (null alternative : Set Θ) : Prop :=
  ∃ α ∈ Icc (0 : ℝ) 1, φ.HasLevel P null α ∧
    ∀ θ ∈ alternative, α ≤ φ.power (P θ)

def typeIIError (φ : StatisticalTest Ω) (P : Measure Ω) : ℝ := 1 - φ.power P

theorem power_add_typeIIError (φ : StatisticalTest Ω) (P : Measure Ω) :
    φ.power P + φ.typeIIError P = 1 := by unfold typeIIError; ring

end StatisticalTest

/-- Superuniformity is the validity requirement, including composite nulls. -/
def IsValidPValue {Ω Θ : Type*} [MeasurableSpace Ω] (p : Ω → ℝ)
    (P : Θ → Measure Ω) (null : Set Θ) : Prop :=
  Measurable p ∧ (∀ x, p x ∈ Icc (0 : ℝ) 1) ∧
    ∀ θ ∈ null, ∀ α ∈ Icc (0 : ℝ) 1, (P θ).real {x | p x ≤ α} ≤ α

theorem pvalue_test_has_level {Ω Θ : Type*} [MeasurableSpace Ω]
    {p : Ω → ℝ} {P : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (P θ)]
    {null : Set Θ} (hp : IsValidPValue p P null) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    (StatisticalTest.ofRejectionSet {x | p x ≤ α}
      (measurableSet_le hp.1 measurable_const)).HasLevel P null α := by
  intro θ hθ
  rw [StatisticalTest.power_ofRejectionSet]
  exact hp.2.2 θ hθ α hα

/-- Bonferroni needs no independence and permits unequal error allocations. -/
theorem bonferroni {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (s : Finset ι) (R : ι → Set Ω) (α : ι → ℝ)
    (h : ∀ i ∈ s, P.real (R i) ≤ α i) :
    P.real (⋃ i ∈ s, R i) ≤ ∑ i ∈ s, α i :=
  (measureReal_biUnion_finset_le s R).trans (Finset.sum_le_sum h)

/-- Unbiased power has a local minimum at a simple null, so its derivative vanishes. -/
theorem unbiased_power_derivative_zero {β : ℝ → ℝ} {θ₀ α : ℝ}
    (hnull : β θ₀ ≤ α) (halt : ∀ θ, θ ≠ θ₀ → α ≤ β θ) : deriv β θ₀ = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply IsMinOn.isLocalMin (s := univ) _ (by simp)
  intro θ _
  by_cases h : θ = θ₀
  · simp [h]
  · exact hnull.trans (halt θ h)

end LectureNotes
