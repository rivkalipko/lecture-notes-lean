import LectureNotes.DominatingMixture
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Fisher–Neyman factorization for a sigma-finitely dominated standard Borel
experiment. A finite carrier factor can always be chosen, by taking a positive
countable combination of model densities. All density equalities are almost
everywhere with respect to the original dominating measure. -/
theorem fisherNeyman_factorization {Θ Ω S : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace S] [StandardBorelSpace S]
    (P : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (P θ)]
    (ν : Measure Ω) [SigmaFinite ν] (f : Θ → Ω → ℝ≥0∞)
    (hf : ∀ θ, Measurable (f θ)) (hP : ∀ θ, ν.withDensity (f θ) = P θ)
    {T : Ω → S} (hT : Measurable T) :
    IsSufficientStatistic P T ↔
      ∃ h : Ω → ℝ≥0∞, Measurable h ∧ IsFiniteMeasure (ν.withDensity h) ∧
        ∀ θ, ∃ g : S → ℝ≥0∞, Measurable g ∧
          f θ =ᵐ[ν] (fun x => h x * g (T x)) := by
  have hdom (θ : Θ) : P θ ≪ ν := by
    rw [← hP θ]
    exact withDensity_absolutelyContinuous _ _
  constructor
  · intro hs
    obtain ⟨ι, hcount, parameters, w, μ, hfinite, hmix, hμν, hdomμ⟩ :=
      exists_dominating_countable_mixture P ν hdom
    letI : Countable ι := hcount
    letI : IsFiniteMeasure μ := hfinite
    have hm : ν.withDensity (μ.rnDeriv ν) = μ := Measure.withDensity_rnDeriv_eq _ _ hμν
    refine ⟨μ.rnDeriv ν, Measure.measurable_rnDeriv _ _, ?_, ?_⟩
    · rw [hm]
      infer_instance
    · intro θ
      obtain ⟨g, hg, he⟩ :=
        (sufficient_iff_mixture_factorization hT μ parameters w hmix hdomμ).mp hs θ
      refine ⟨g, hg, ?_⟩
      apply (withDensity_eq_iff_of_sigmaFinite (hf θ).aemeasurable
        ((Measure.measurable_rnDeriv _ _).mul (hg.comp hT)).aemeasurable).mp
      change ν.withDensity (f θ) = ν.withDensity
        ((μ.rnDeriv ν) * (fun x => g (T x)))
      rw [hP θ, withDensity_mul ν (g := fun x => g (T x))
        (Measure.measurable_rnDeriv _ _) (hg.comp hT), hm, he]
  · rintro ⟨h, hh, hfinite, hfact⟩
    letI : IsFiniteMeasure (ν.withDensity h) := hfinite
    apply sufficient_of_reference_factorization (ν.withDensity h) hT
    intro θ
    obtain ⟨g, hg, he⟩ := hfact θ
    refine ⟨g, hg, ?_⟩
    rw [← withDensity_mul ν (g := fun x => g (T x)) hh (hg.comp hT)]
    change ν.withDensity (fun x => h x * g (T x)) = P θ
    rw [withDensity_congr_ae he.symm, hP θ]

end LectureNotes
