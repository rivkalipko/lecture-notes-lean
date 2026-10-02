import LectureNotes.MinimalSufficiency
import LectureNotes.MixtureSufficiency

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
universe u v

/-- Likelihood-ratio recovery proves minimality even when supports vary and
there is no dominating model member. A countable collection of ratios is
permitted, all recovered by one measurable decoding map. -/
theorem minimal_sufficient_of_mixture_ratio_recovery {Θ Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace S] [StandardBorelSpace S]
    (P : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (P θ)] {T : Ω → S}
    (hT : IsSufficientStatistic P T) (μ : Measure Ω) [IsFiniteMeasure μ]
    {ι : Type*} [Countable ι] (mixtureParameters : ι → Θ) (w : ι → ℝ≥0∞)
    (hmix : μ = Measure.sum (fun i => w i • P (mixtureParameters i)))
    (hdom : ∀ θ, P θ ≪ μ)
    {J : Type*} [Countable J] (parameters : J → Θ) (decode : (J → ℝ≥0∞) → S)
    (hd : Measurable decode)
    (hrecover : (fun x => decode (fun j => (P (parameters j)).rnDeriv μ x)) =ᵐ[μ] T) :
    IsMinimalSufficientStatistic P T := by
  refine ⟨hT, ?_⟩
  intro R _ _ U hU
  obtain ⟨hUm, K, hMarkov, hK⟩ := hU
  letI : IsMarkovKernel K := hMarkov
  have hμ : μ.map (fun x => (U x, x)) = μ.map U ⊗ₘ K := by
    rw [hmix]
    exact sufficientKernel_mixture_disintegration hUm hK mixtureParameters w
  let r (s : R) := decode (fun j => ((P (parameters j)).map U).rnDeriv (μ.map U) s)
  have hr : Measurable r := hd.comp (measurable_pi_lambda _ (fun _ => Measure.measurable_rnDeriv _ _))
  refine ⟨r, hr, fun θ => (hdom θ).ae_eq ?_⟩
  have hs : ∀ᵐ x ∂μ, ∀ j, (P (parameters j)).rnDeriv μ x =
      ((P (parameters j)).map U).rnDeriv (μ.map U) (U x) := ae_all_iff.mpr (fun j =>
    rnDeriv_factors_of_common_disintegration (P (parameters j)) μ hUm K
      (sufficientKernel_disintegration hUm hK _) hμ)
  filter_upwards [hs, hrecover] with x hx hrec
  dsimp only [r]
  rw [← funext hx]
  exact hrec

end LectureNotes
