import LectureNotes.DecisionTheory

set_option autoImplicit false

/-! L12 posterior distributions and L13 Theorem 1. The posterior is Mathlib's
regular conditional Markov kernel. Losses are nonnegative extended reals, so
Tonelli applies even when the Bayes risk is infinite. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Θ Ω A : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω] [MeasurableSpace A]
  [StandardBorelSpace Θ] [Nonempty Θ]

def posteriorRisk (κ : Kernel Θ Ω) [IsMarkovKernel κ]
    (π : Measure Θ) [IsProbabilityMeasure π] (loss : A → Θ → ℝ≥0∞)
    (a : A) (x : Ω) : ℝ≥0∞ := ∫⁻ θ, loss a θ ∂((κ†π) x)

/-- Integrated sampling risk equals expected posterior risk under the prior
predictive law. This is an equality of actual conditional distributions. -/
theorem bayes_risk_eq_expected_posterior_risk (κ : Kernel Θ Ω) [IsMarkovKernel κ]
    (π : Measure Θ) [IsProbabilityMeasure π] (loss : A → Θ → ℝ≥0∞)
    (hloss : Measurable (Function.uncurry loss)) (δ : Ω → A) (hδ : Measurable δ) :
    integratedRisk (fun θ => κ θ) loss π δ =
      ∫⁻ x, posteriorRisk κ π loss (δ x) x ∂(κ ∘ₘ π) := by
  have hf : Measurable (fun z : Θ × Ω => loss (δ z.2) z.1) :=
    hloss.comp ((hδ.comp measurable_snd).prodMk measurable_fst)
  have hg : Measurable (fun z : Ω × Θ => loss (δ z.1) z.2) :=
    hloss.comp ((hδ.comp measurable_fst).prodMk measurable_snd)
  calc
    integratedRisk (fun θ => κ θ) loss π δ =
        ∫⁻ z : Θ × Ω, loss (δ z.2) z.1 ∂(π ⊗ₘ κ) :=
      (Measure.lintegral_compProd hf).symm
    _ = ∫⁻ z : Ω × Θ, loss (δ z.1) z.2 ∂((π ⊗ₘ κ).map Prod.swap) := by
      rw [lintegral_map hg measurable_swap]
      rfl
    _ = ∫⁻ z : Ω × Θ, loss (δ z.1) z.2 ∂((κ ∘ₘ π) ⊗ₘ κ†π) := by
      rw [compProd_posterior_eq_map_swap]
    _ = ∫⁻ x, posteriorRisk κ π loss (δ x) x ∂(κ ∘ₘ π) :=
      Measure.lintegral_compProd hg

/-- L13 Theorem 1. A measurable posterior-risk minimizer is a Bayes rule.
Existence of a measurable minimizer is not automatic and is not asserted here. -/
theorem posterior_minimizer_is_bayes (κ : Kernel Θ Ω) [IsMarkovKernel κ]
    (π : Measure Θ) [IsProbabilityMeasure π] (loss : A → Θ → ℝ≥0∞)
    (hloss : Measurable (Function.uncurry loss))
    (δ : Ω → A) (hδ : Measurable δ)
    (hmin : ∀ᵐ x ∂(κ ∘ₘ π), ∀ a, posteriorRisk κ π loss (δ x) x ≤
      posteriorRisk κ π loss a x)
    (ε : Ω → A) (hε : Measurable ε) :
    integratedRisk (fun θ => κ θ) loss π δ ≤ integratedRisk (fun θ => κ θ) loss π ε := by
  rw [bayes_risk_eq_expected_posterior_risk κ π loss hloss δ hδ,
    bayes_risk_eq_expected_posterior_risk κ π loss hloss ε hε]
  exact lintegral_mono_ae (hmin.mono (fun x hx => hx (ε x)))

def IsCredibleSet (κ : Kernel Θ Ω) [IsMarkovKernel κ]
    (π : Measure Θ) [IsProbabilityMeasure π] (x : Ω) (C : Set Θ) (γ : ℝ≥0∞) : Prop :=
  MeasurableSet C ∧ γ ≤ (κ†π) x C

/-- Posterior probabilities, averaged over the data, recover the prior. -/
theorem posterior_averages_to_prior (κ : Kernel Θ Ω) [IsMarkovKernel κ]
    (π : Measure Θ) [IsProbabilityMeasure π] : (κ†π) ∘ₘ (κ ∘ₘ π) = π :=
  posterior_comp_self

end LectureNotes
