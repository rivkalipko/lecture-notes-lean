import LectureNotes.SigmaFiniteFactorization

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The general Fisher–Neyman theorem (L5 Theorem 2): a measurable statistic is
sufficient exactly when every model density factors into a common measurable
carrier and a measurable function of the statistic. The carrier need not have
finite integral. Equalities use the original dominating measure's null sets. -/
theorem fisherNeyman_general {Θ Ω S : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace S] [StandardBorelSpace S]
    (P : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (P θ)]
    (ν : Measure Ω) [SigmaFinite ν] (f : Θ → Ω → ℝ≥0∞)
    (hf : ∀ θ, Measurable (f θ)) (hP : ∀ θ, ν.withDensity (f θ) = P θ)
    {T : Ω → S} (hT : Measurable T) :
    IsSufficientStatistic P T ↔
      ∃ h : Ω → ℝ≥0∞, Measurable h ∧
        ∀ θ, ∃ g : S → ℝ≥0∞, Measurable g ∧
          f θ =ᵐ[ν] (fun x => h x * g (T x)) := by
  constructor
  · intro hs
    obtain ⟨h, hh, _, hfact⟩ := (fisherNeyman_factorization P ν f hf hP hT).mp hs
    exact ⟨h, hh, hfact⟩
  · rintro ⟨h, hh, hfact⟩
    let h' (x : Ω) := if h x = ⊤ then (0 : ℝ≥0∞) else h x
    have hh' : Measurable h' := Measurable.ite
      (hh (measurableSet_singleton ⊤)) measurable_const hh
    have hfin : ∀ᵐ x ∂ν, h' x ≠ ⊤ := ae_of_all _ (fun x => by
      dsimp only [h']
      split_ifs with hx <;> simp [hx])
    apply sufficient_of_density_factorization_sigmaFinite ν f hP hT h' hh' hfin
    intro θ
    obtain ⟨g, hg, he⟩ := hfact θ
    refine ⟨g, hg, ?_⟩
    have hfinit : ∀ᵐ x ∂ν, f θ x ≠ ⊤ := by
      have hr := Measure.rnDeriv_withDensity ν (hf θ)
      rw [hP θ] at hr
      filter_upwards [hr, Measure.rnDeriv_ne_top (P θ) ν] with x hx hfinite
      exact hx ▸ hfinite
    filter_upwards [he, hfinit] with x hx hfinite
    by_cases hhx : h x = ⊤
    · have hgzero : g (T x) = 0 := by
        by_contra hgzero
        apply hfinite
        rw [hx, hhx, ENNReal.top_mul hgzero]
      simp only [h', hhx, if_true, zero_mul, hgzero, mul_zero] at hx ⊢
      exact hx
    · simpa only [h', hhx, if_false] using hx

end LectureNotes
