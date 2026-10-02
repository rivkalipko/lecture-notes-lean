import LectureNotes.RaoBlackwell
import LectureNotes.Testing

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

namespace StatisticalTest
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- A randomized test based only on a measurable statistic is a randomized
test of the original data. -/
def pullback (ψ : StatisticalTest S) (T : Ω → S) (hT : Measurable T) : StatisticalTest Ω where
  reject := fun ω => ψ.reject (T ω)
  measurable_reject := ψ.measurable_reject.comp hT
  nonneg := fun ω => ψ.nonneg (T ω)
  le_one := fun ω => ψ.le_one (T ω)

/-- Pulling a test back through a statistic preserves its power under the
statistic's actual pushforward distribution. -/
theorem pullback_power (ψ : StatisticalTest S) (T : Ω → S) (hT : Measurable T)
    (P : Measure Ω) :
    (ψ.pullback T hT).power P = ψ.power (P.map T) := by
  symm
  exact integral_map hT.aemeasurable ψ.measurable_reject.aestronglyMeasurable

/-- Average a test's rejection probability against a common conditional law.
The resulting measurable function still takes values in [0,1] everywhere. -/
def raoBlackwellTest (φ : StatisticalTest Ω) (K : Kernel S Ω) [IsMarkovKernel K] :
    StatisticalTest S where
  reject := raoBlackwellEstimator K φ.reject
  measurable_reject := raoBlackwellEstimator_measurable K φ.measurable_reject
  nonneg := fun s => integral_nonneg φ.nonneg
  le_one := fun s => φ.power_le_one (K s)

/-- Sufficient-statistic averaging preserves every parameter's rejection
probability, not merely the size at one null model. -/
theorem raoBlackwellTest_power {Θ : Type*} [StandardBorelSpace Ω] [Nonempty Ω]
    (φ : StatisticalTest Ω) {P : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (P θ)]
    {T : Ω → S} {K : Kernel S Ω} [IsMarkovKernel K]
    (hT : Measurable T) (hK : IsSufficientKernel P T K) (θ : Θ) :
    (φ.raoBlackwellTest K).power ((P θ).map T) = φ.power (P θ) := by
  change (∫ s, raoBlackwellEstimator K φ.reject s ∂(P θ).map T) = _
  rw [integral_map hT.aemeasurable
    (raoBlackwellEstimator_measurable K φ.measurable_reject).aestronglyMeasurable]
  have hc := sufficientKernel_condExp hT hK θ (φ.integrable (P θ))
  exact (integral_congr_ae hc.symm).trans (integral_condExp hT.comap_le)

end StatisticalTest

/-- Every measurable randomized full-data test has a measurable randomized
test of a sufficient statistic with identical power at every parameter. -/
theorem sufficient_statistic_preserves_test_power {Θ Ω S : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace S]
    {P : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (P θ)] {T : Ω → S}
    (hT : IsSufficientStatistic P T) (φ : StatisticalTest Ω) :
    ∃ ψ : StatisticalTest S, ∀ θ, ψ.power ((P θ).map T) = φ.power (P θ) := by
  obtain ⟨hTm, K, hKM, hK⟩ := hT
  letI : IsMarkovKernel K := hKM
  exact ⟨φ.raoBlackwellTest K, fun θ => φ.raoBlackwellTest_power hTm hK θ⟩

/-- A UMP test in the sufficient-statistic experiment is UMP among all
measurable randomized tests of the full data. -/
theorem isUMP_pullback_of_sufficient {Θ Ω S : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace S]
    {P : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (P θ)] {T : Ω → S}
    (hT : IsSufficientStatistic P T) (ψ : StatisticalTest S)
    {null alternative : Set Θ} {α : ℝ}
    (hψ : ψ.IsUMP (fun θ => (P θ).map T) null alternative α) :
    (ψ.pullback T hT.1).IsUMP P null alternative α := by
  constructor
  · intro θ hθ
    rw [StatisticalTest.pullback_power]
    exact hψ.1 θ hθ
  · intro φ hφ θ hθ
    obtain ⟨η, hη⟩ := sufficient_statistic_preserves_test_power hT φ
    have hηlevel : η.HasLevel (fun θ => (P θ).map T) null α := by
      intro ξ hξ
      rw [hη]
      exact hφ ξ hξ
    rw [StatisticalTest.pullback_power, ← hη]
    exact hψ.2 η hηlevel θ hθ

/-- Existence of a UMP randomized test is equivalent before and after
sufficient-statistic reduction. No completeness assumption is needed. -/
theorem exists_ump_iff_of_sufficient {Θ Ω S : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace S]
    {P : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (P θ)] {T : Ω → S}
    (hT : IsSufficientStatistic P T) (null alternative : Set Θ) (α : ℝ) :
    (∃ φ : StatisticalTest Ω, φ.IsUMP P null alternative α) ↔
      ∃ ψ : StatisticalTest S, ψ.IsUMP (fun θ => (P θ).map T) null alternative α := by
  constructor
  · rintro ⟨φ, hφ⟩
    obtain ⟨ψ, hψ⟩ := sufficient_statistic_preserves_test_power hT φ
    refine ⟨ψ, ?_, ?_⟩
    · intro θ hθ
      rw [hψ]
      exact hφ.1 θ hθ
    · intro η hη θ hθ
      have hηlevel : (η.pullback T hT.1).HasLevel P null α := by
        intro ξ hξ
        rw [StatisticalTest.pullback_power]
        exact hη ξ hξ
      have hh := hφ.2 (η.pullback T hT.1) hηlevel θ hθ
      rw [StatisticalTest.pullback_power, ← hψ] at hh
      exact hh
  · rintro ⟨ψ, hψ⟩
    exact ⟨ψ.pullback T hT.1, isUMP_pullback_of_sufficient hT ψ hψ⟩

end LectureNotes
