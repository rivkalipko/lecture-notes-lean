import LectureNotes.MinimalSufficiency

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
universe u v w

/-- A countable collection of likelihood ratios that separates statistic values
certifies minimality. The measurable decoder follows from the standard Borel
embedding theorem, rather than being an additional recovery hypothesis. -/
theorem minimal_sufficient_of_injective_ratio_representation
    {Θ Ω : Type u} {S : Type v} {ι : Type w}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace S] [StandardBorelSpace S] [Countable ι]
    (P : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (P θ)] {T : Ω → S}
    (hT : IsSufficientStatistic P T) (θ₀ : Θ) (hdom : ∀ θ, P θ ≪ P θ₀)
    (parameters : ι → Θ) (g : S → ι → ℝ≥0∞)
    (hg : Measurable g) (hginj : Function.Injective g)
    (hrep : ∀ i, (P (parameters i)).rnDeriv (P θ₀) =ᵐ[P θ₀] (fun x => g (T x) i)) :
    IsMinimalSufficientStatistic P T := by
  classical
  obtain ⟨decode, hd, hdec⟩ := (hg.measurableEmbedding hginj).exists_measurable_extend
    (g := id) measurable_id (fun _ => ⟨T (Classical.arbitrary Ω)⟩)
  refine ⟨hT, ?_⟩
  intro R _ _ U hU
  let r (s : R) := decode (fun i => ((P (parameters i)).map U).rnDeriv ((P θ₀).map U) s)
  have hr : Measurable r := hd.comp (measurable_pi_lambda _ (fun _ => Measure.measurable_rnDeriv _ _))
  refine ⟨r, hr, fun θ => (hdom θ).ae_eq ?_⟩
  have hs : ∀ᵐ x ∂P θ₀, ∀ i, (P (parameters i)).rnDeriv (P θ₀) x =
      ((P (parameters i)).map U).rnDeriv ((P θ₀).map U) (U x) :=
    ae_all_iff.mpr (fun i => sufficient_rnDeriv_factors hU θ₀ (parameters i))
  filter_upwards [hs, ae_all_iff.mpr hrep] with x hx he
  dsimp only [r]
  have hcoord : (fun i => ((P (parameters i)).map U).rnDeriv ((P θ₀).map U) (U x)) = g (T x) :=
    funext (fun i => (hx i).symm.trans (he i))
  rw [hcoord]
  exact congrFun hdec (T x)

end LectureNotes
