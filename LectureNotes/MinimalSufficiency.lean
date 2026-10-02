import LectureNotes.DominatedSufficiency

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
universe u v

/-- Minimality among standard Borel data reductions: every sufficient statistic
measurably determines this one, up to each model's null sets, using one common
reconstruction function for the whole parameter family. -/
def IsMinimalSufficientStatistic {Θ Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace S] [StandardBorelSpace S]
    (P : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (P θ)] (T : Ω → S) : Prop :=
  IsSufficientStatistic P T ∧
    ∀ (R : Type v) [MeasurableSpace R] [StandardBorelSpace R] (U : Ω → R),
      IsSufficientStatistic P U → ∃ r : R → S, Measurable r ∧
        ∀ θ, (fun x => r (U x)) =ᵐ[P θ] T

/-- A finite set of likelihood ratios can certify minimality. The hypotheses
are a separately proved sufficiency result and an explicit measurable recovery
of the statistic from those ratios, not a conditional-law assumption. -/
theorem minimal_sufficient_of_likelihood_ratio_recovery {Θ Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace S] [StandardBorelSpace S]
    (P : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (P θ)] {T : Ω → S}
    (hT : IsSufficientStatistic P T) (θ₀ : Θ) (hdom : ∀ θ, P θ ≪ P θ₀)
    {k : ℕ} (parameters : Fin k → Θ) (decode : (Fin k → ℝ≥0∞) → S)
    (hd : Measurable decode)
    (hrecover : (fun x => decode (fun i => (P (parameters i)).rnDeriv (P θ₀) x)) =ᵐ[P θ₀] T) :
    IsMinimalSufficientStatistic P T := by
  refine ⟨hT, ?_⟩
  intro R _ _ U hU
  let r (s : R) := decode (fun i => ((P (parameters i)).map U).rnDeriv ((P θ₀).map U) s)
  have hr : Measurable r := hd.comp (measurable_pi_lambda _ (fun _ => Measure.measurable_rnDeriv _ _))
  refine ⟨r, hr, fun θ => (hdom θ).ae_eq ?_⟩
  have hs : ∀ᵐ x ∂P θ₀, ∀ i, (P (parameters i)).rnDeriv (P θ₀) x =
      ((P (parameters i)).map U).rnDeriv ((P θ₀).map U) (U x) :=
    ae_all_iff.mpr (fun i => sufficient_rnDeriv_factors hU θ₀ (parameters i))
  filter_upwards [hs, hrecover] with x hx hrec
  dsimp only [r]
  rw [← funext hx]
  exact hrec

end LectureNotes
