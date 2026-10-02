import LectureNotes.DominatedSufficiency

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- A common conditional kernel also disintegrates a countable mixture of the
models. The reference need not itself be a member of the parameter family. -/
theorem sufficientKernel_mixture_disintegration {Θ Ω S ι : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace S] [StandardBorelSpace S] [Countable ι]
    {P : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (P θ)]
    {T : Ω → S} (hT : Measurable T) {K : Kernel S Ω} [IsMarkovKernel K]
    (hK : IsSufficientKernel P T K) (parameters : ι → Θ) (w : ι → ℝ≥0∞) :
    (Measure.sum (fun i => w i • P (parameters i))).map (fun x => (T x, x)) =
      (Measure.sum (fun i => w i • P (parameters i))).map T ⊗ₘ K := by
  rw [Measure.map_sum (f := fun x => (T x, x)) (hT.prodMk measurable_id).aemeasurable,
    Measure.map_sum hT.aemeasurable, Measure.compProd_sum_left]
  congr 1
  funext i
  rw [Measure.map_smul, Measure.map_smul, Measure.compProd_smul_left,
    sufficientKernel_disintegration hT hK]

/-- Sufficiency identifies the full-data likelihood ratio with the marginal
ratio for any finite reference that has the same disintegration. -/
theorem rnDeriv_factors_of_common_disintegration {Ω S : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace S] [StandardBorelSpace S]
    (ν μ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {T : Ω → S} (hT : Measurable T) (K : Kernel S Ω) [IsMarkovKernel K]
    (hν : ν.map (fun x => (T x, x)) = ν.map T ⊗ₘ K)
    (hμ : μ.map (fun x => (T x, x)) = μ.map T ⊗ₘ K) :
    ν.rnDeriv μ =ᵐ[μ] (fun x => (ν.map T).rnDeriv (μ.map T) (T x)) := by
  have hemb : MeasurableEmbedding (fun x => (T x, x)) :=
    (hT.prodMk measurable_id).measurableEmbedding (fun _ _ h => congrArg Prod.snd h)
  have hj := rnDeriv_measure_compProd_left (ν.map T) (μ.map T) K
  rw [← hν, ← hμ] at hj
  exact (hemb.rnDeriv_map ν μ).symm.trans
    (ae_of_ae_map (hT.prodMk measurable_id).aemeasurable hj)

/-- The general reference-mixture factorization theorem. Densities may vanish,
and no model member is required to dominate the others. -/
theorem sufficient_iff_mixture_factorization {Θ Ω S ι : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace S] [StandardBorelSpace S] [Countable ι]
    {P : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (P θ)]
    {T : Ω → S} (hT : Measurable T) (μ : Measure Ω) [IsFiniteMeasure μ]
    (parameters : ι → Θ) (w : ι → ℝ≥0∞)
    (hmix : μ = Measure.sum (fun i => w i • P (parameters i))) (hdom : ∀ θ, P θ ≪ μ) :
    IsSufficientStatistic P T ↔
      ∀ θ, ∃ g : S → ℝ≥0∞, Measurable g ∧ μ.withDensity (fun x => g (T x)) = P θ := by
  constructor
  · rintro ⟨hTm, K, hMarkov, hK⟩ θ
    letI : IsMarkovKernel K := hMarkov
    have hμ : μ.map (fun x => (T x, x)) = μ.map T ⊗ₘ K := by
      rw [hmix]
      exact sufficientKernel_mixture_disintegration hTm hK parameters w
    refine ⟨((P θ).map T).rnDeriv (μ.map T), Measure.measurable_rnDeriv _ _, ?_⟩
    calc
      _ = μ.withDensity ((P θ).rnDeriv μ) := withDensity_congr_ae
        (rnDeriv_factors_of_common_disintegration (P θ) μ hTm K
          (sufficientKernel_disintegration hTm hK θ) hμ).symm
      _ = P θ := Measure.withDensity_rnDeriv_eq _ _ (hdom θ)
  · exact sufficient_of_reference_factorization μ hT

end LectureNotes
