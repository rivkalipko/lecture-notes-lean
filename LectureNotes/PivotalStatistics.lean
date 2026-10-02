import LectureNotes.ConfidenceSets
import LectureNotes.QuantileIntervals

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- L8's pivotal property: evaluating the statistic at the true parameter gives
one common law for the whole model. A null model with nuisance parameters can
be represented by taking the parameter type to be that null family. -/
def IsPivotalFamily {Ω Θ E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Θ → Measure Ω) (T : Θ → Ω → E) (ν : Measure E) : Prop :=
  ∀ θ, HasLaw (T θ) ν (P θ)

/-- L11's pivotal inversion: retain exactly the parameters for which the
observed pivot belongs to a fixed acceptance region of the common law. -/
def pivotConfidenceSet {Ω Θ E : Type*} (T : Θ → Ω → E) (A : Set E)
    (x : Ω) : Set Θ := {θ | T θ x ∈ A}

theorem pivotal_event_probability {Ω Θ E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Θ → Measure Ω} {T : Θ → Ω → E} {ν : Measure E}
    (h : IsPivotalFamily P T ν) {A : Set E} (hA : MeasurableSet A) (θ : Θ) :
    (P θ).real {x | T θ x ∈ A} = ν.real A :=
  (h θ).measureReal_eq hA

/-- Any measurable calibrated acceptance region gives its exact coverage,
including discrete pivotal laws. No continuity or symmetry is required. -/
theorem pivotConfidenceSet_coverage {Ω Θ E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace E]
    {P : Θ → Measure Ω} {T : Θ → Ω → E} {ν : Measure E}
    (h : IsPivotalFamily P T ν) {A : Set E} (hA : MeasurableSet A) (θ : Θ) :
    coverage P (pivotConfidenceSet T A) θ = ν.real A :=
  pivotal_event_probability h hA θ

theorem pivotConfidenceSet_hasLevel {Ω Θ E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace E]
    {P : Θ → Measure Ω} {T : Θ → Ω → E} {ν : Measure E}
    (h : IsPivotalFamily P T ν) {A : Set E} (hA : MeasurableSet A)
    {γ : ℝ} (hγ : γ ≤ ν.real A) :
    HasConfidenceLevel P (pivotConfidenceSet T A) γ := by
  intro θ
  rwa [pivotConfidenceSet_coverage h hA]

/-- For an atomless real pivotal law, generalized-inverse quantiles yield
exact coverage equal to the difference of the tail probabilities. -/
theorem pivot_quantile_interval_coverage {Ω Θ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Θ → Measure Ω} {T : Θ → Ω → ℝ} {ν : Measure ℝ}
    [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (h : IsPivotalFamily P T ν) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) (θ : Θ) :
    coverage P (pivotConfidenceSet T
      (Icc (distributionQuantile ν a) (distributionQuantile ν b))) θ = b - a := by
  rw [pivotConfidenceSet_coverage h measurableSet_Icc]
  exact quantile_interval_probability ν ha hb hab

end LectureNotes
