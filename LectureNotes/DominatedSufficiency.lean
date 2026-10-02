import LectureNotes.RaoBlackwell
import Mathlib.Probability.Kernel.Composition.RadonNikodym

set_option autoImplicit false

/-! L5 factorization for standard Borel experiments. Densities and
factorizations are identified up to reference-null sets. Conditional laws on
continuous statistic fibers are obtained by disintegration, not by dividing
a joint density by a marginal density with respect to the original volume. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- A density depending only on the image passes through a measurable map. -/
theorem map_weighted_by_statistic {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (μ : Measure Ω) {T : Ω → S} (hT : Measurable T) {g : S → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity (fun x => g (T x))).map T = (μ.map T).withDensity g := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hT, lintegral_withDensity_eq_lintegral_mul μ (f := fun x => g (T x))
      (g := fun x => f (T x)) (hg.comp hT) (hf.comp hT),
    lintegral_withDensity_eq_lintegral_mul _ hg hf, lintegral_map (hg.mul hf) hT]
  rfl

/-- Weighting only the first coordinate leaves the conditional kernel unchanged. -/
theorem compProd_weighted_left {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (μ : Measure S) [IsFiniteMeasure μ] (K : Kernel S Ω) [IsMarkovKernel K]
    {g : S → ℝ≥0∞} (hg : Measurable g) [IsFiniteMeasure (μ.withDensity g)] :
    (μ.withDensity g) ⊗ₘ K = (μ ⊗ₘ K).withDensity (fun p => g p.1) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_compProd hf,
    lintegral_withDensity_eq_lintegral_mul _ hg hf.lintegral_kernel_prod_right',
    lintegral_withDensity_eq_lintegral_mul (μ ⊗ₘ K) (f := fun p => g p.1)
      (hg.comp measurable_fst) hf,
    Measure.lintegral_compProd (μ := μ) (κ := K)
      (f := (fun p : S × Ω => g p.1) * f) ((hg.comp measurable_fst).mul hf)]
  apply lintegral_congr
  intro s
  simpa only [Pi.mul_apply, Function.comp_apply] using
    (lintegral_const_mul (g s) (hf.comp measurable_prodMk_left)).symm

section Experiment
variable {Θ Ω S : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [MeasurableSpace S] [StandardBorelSpace S]
  {P : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (P θ)] {T : Ω → S}

/-- The common-conditional-law definition implies the joint-law disintegration
identity, without choosing a density on any zero-volume fiber. -/
theorem sufficientKernel_disintegration (hT : Measurable T) {K : Kernel S Ω}
    [IsMarkovKernel K] (hK : IsSufficientKernel P T K) (θ : Θ) :
    (P θ).map (fun x => (T x, x)) = (P θ).map T ⊗ₘ K := by
  have hc : (P θ).map (fun x => (T x, x)) = (P θ).map T ⊗ₘ condDistrib id T (P θ) :=
    (compProd_map_condDistrib (X := T) (Y := id) aemeasurable_id).symm
  rw [hc]
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_compProd hf, Measure.lintegral_compProd hf,
    lintegral_map hf.lintegral_kernel_prod_right' hT,
    lintegral_map hf.lintegral_kernel_prod_right' hT]
  apply lintegral_congr_ae
  filter_upwards [hK θ] with x hx
  exact congrArg (fun ν : Measure Ω => ∫⁻ y, f (T x, y) ∂ν) hx

/-- A factorization relative to any finite reference measure constructs
one conditional kernel valid simultaneously for the entire experiment. -/
theorem sufficient_of_reference_factorization (μ : Measure Ω) [IsFiniteMeasure μ]
    (hT : Measurable T)
    (hfact : ∀ θ, ∃ g : S → ℝ≥0∞, Measurable g ∧
      μ.withDensity (fun x => g (T x)) = P θ) : IsSufficientStatistic P T := by
  refine ⟨hT, condDistrib id T μ, inferInstance, ?_⟩
  apply sufficientKernel_of_disintegration hT
  intro θ
  obtain ⟨g, hg, he⟩ := hfact θ
  have hmap : (μ.map T).withDensity g = (P θ).map T := by
    rw [← map_weighted_by_statistic μ hT hg, he]
  have : IsFiniteMeasure ((μ.map T).withDensity g) := by rw [hmap]; infer_instance
  have hgraph := map_weighted_by_statistic μ (hT.prodMk measurable_id)
    (hg.comp measurable_fst)
  change (μ.withDensity (fun x => g (T x))).map (fun x => (T x, x)) =
    (μ.map (fun x => (T x, x))).withDensity (fun p => g p.1) at hgraph
  have hc : μ.map (fun x => (T x, x)) = μ.map T ⊗ₘ condDistrib id T μ :=
    (compProd_map_condDistrib (X := T) (Y := id) aemeasurable_id).symm
  rw [he, hc,
    ← compProd_weighted_left (μ.map T) (condDistrib id T μ) hg, hmap] at hgraph
  exact hgraph

/-- A density factorization relative to one model density is sufficient.
The factorization is an equality of actual densities, and its measurable
statistic-dependent factor is converted to the common conditional kernel. -/
theorem sufficient_of_density_factorization (ν : Measure Ω) (θ₀ : Θ)
    (f : Θ → Ω → ℝ≥0∞) (hf : ∀ θ, Measurable (f θ))
    (hP : ∀ θ, ν.withDensity (f θ) = P θ)
    (hT : Measurable T) (g : Θ → S → ℝ≥0∞) (hg : ∀ θ, Measurable (g θ))
    (hfact : ∀ θ, f θ =ᵐ[ν] (fun x => f θ₀ x * g θ (T x))) :
    IsSufficientStatistic P T := by
  apply sufficient_of_reference_factorization (P θ₀) hT
  intro θ
  refine ⟨g θ, hg θ, ?_⟩
  rw [← hP θ₀, ← withDensity_mul ν (g := fun x => g θ (T x)) (hf θ₀) ((hg θ).comp hT)]
  change ν.withDensity (fun x => f θ₀ x * g θ (T x)) = P θ
  rw [withDensity_congr_ae (hfact θ).symm, hP θ]

/-- Under sufficiency, the density relative to a dominating model member is
the marginal density of the statistic, composed with that statistic. -/
theorem sufficient_rnDeriv_factors (hT : IsSufficientStatistic P T) (θ₀ θ : Θ) :
    (P θ).rnDeriv (P θ₀) =ᵐ[P θ₀]
      (fun x => ((P θ).map T).rnDeriv ((P θ₀).map T) (T x)) := by
  obtain ⟨hTm, K, hMarkov, hK⟩ := hT
  letI : IsMarkovKernel K := hMarkov
  have hemb : MeasurableEmbedding (fun x => (T x, x)) :=
    (hTm.prodMk measurable_id).measurableEmbedding (fun _ _ h => congrArg Prod.snd h)
  have hj := rnDeriv_measure_compProd_left ((P θ).map T) ((P θ₀).map T) K
  rw [← sufficientKernel_disintegration hTm hK θ,
    ← sufficientKernel_disintegration hTm hK θ₀] at hj
  have hp := ae_of_ae_map (hTm.prodMk measurable_id).aemeasurable hj
  exact (hemb.rnDeriv_map (P θ) (P θ₀)).symm.trans hp

/-- L5 factorization iff on standard Borel spaces with a dominating model
member. Unlike finite-support versions, this includes continuous experiments.
The densities may vanish; all equality statements use the reference null sets. -/
theorem sufficient_iff_reference_factorization (hT : Measurable T) (θ₀ : Θ)
    (hdom : ∀ θ, P θ ≪ P θ₀) :
    IsSufficientStatistic P T ↔
      ∀ θ, ∃ g : S → ℝ≥0∞, Measurable g ∧
        (P θ₀).withDensity (fun x => g (T x)) = P θ := by
  constructor
  · intro hs θ
    refine ⟨((P θ).map T).rnDeriv ((P θ₀).map T), Measure.measurable_rnDeriv _ _, ?_⟩
    calc
      _ = (P θ₀).withDensity ((P θ).rnDeriv (P θ₀)) :=
        withDensity_congr_ae (sufficient_rnDeriv_factors hs θ₀ θ).symm
      _ = P θ := Measure.withDensity_rnDeriv_eq (P θ) (P θ₀) (hdom θ)
  · exact sufficient_of_reference_factorization (P θ₀) hT

end Experiment
end LectureNotes
