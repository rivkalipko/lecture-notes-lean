import LectureNotes.DominatedSufficiency
import Mathlib.Probability.Independence.Integration

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Under a dominated experiment, a sufficient statistic cannot be independent
of a statistic carrying parameter information: independence under one dominating
model forces the latter statistic to have the same law in every model. -/
theorem sufficient_independent_statistic_law {Θ Ω S R : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace S] [StandardBorelSpace S] [MeasurableSpace R]
    (P : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (P θ)]
    {T : Ω → S} (hT : IsSufficientStatistic P T) (θ₀ : Θ)
    (hdom : ∀ θ, P θ ≪ P θ₀) {U : Ω → R} (hU : Measurable U)
    (hind : IndepFun T U (P θ₀)) (θ : Θ) : (P θ).map U = (P θ₀).map U := by
  obtain ⟨g, hg, he⟩ := (sufficient_iff_reference_factorization hT.1 θ₀ hdom).mp hT θ
  have hmass : (∫⁻ x, g (T x) ∂P θ₀) = 1 := by
    have hh := congrArg (fun μ : Measure Ω => μ univ) he
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, measure_univ] at hh
    exact hh
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hU, ← he,
    lintegral_withDensity_eq_lintegral_mul _ (f := fun x => g (T x))
      (g := fun x => f (U x)) (hg.comp hT.1) (hf.comp hU)]
  change (∫⁻ x, g (T x) * f (U x) ∂P θ₀) = _
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (f := fun x => g (T x)) (g := fun x => f (U x))
    (hg.comp hT.1).aemeasurable (hf.comp hU).aemeasurable
    (hind.comp hg hf), hmass, one_mul, lintegral_map hf hU]

end LectureNotes
