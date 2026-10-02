import LectureNotes.MixtureSufficiency

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
universe u

/-- Halmos–Savage domination: a dominated probability experiment has a finite
reference that is a positive countable combination of its model measures.
This permits varying supports and does not assume a dominating model member. -/
theorem exists_dominating_countable_mixture {Θ : Type*} {Ω : Type u} [MeasurableSpace Ω]
    (P : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (P θ)]
    (ν : Measure Ω) [SigmaFinite ν] (hdom : ∀ θ, P θ ≪ ν) :
    ∃ (ι : Type u) (_ : Countable ι) (parameters : ι → Θ) (w : ι → ℝ≥0∞)
      (μ : Measure Ω), IsFiniteMeasure μ ∧
      μ = Measure.sum (fun i => w i • P (parameters i)) ∧ μ ≪ ν ∧ ∀ θ, P θ ≪ μ := by
  classical
  let B (θ : Θ) : Set Ω := {x | (P θ).rnDeriv ν x ≠ 0}
  have hB (θ : Θ) : MeasurableSet (B θ) := (Measure.measurable_rnDeriv _ _ (measurableSet_singleton 0)).compl
  obtain ⟨D, hDC, hDcount, hcover⟩ := Measure.exists_ae_subset_biUnion_countable ν
    (C := Set.range B) (by rintro s ⟨θ, rfl⟩; exact hB θ)
  letI : Countable D := hDcount.to_subtype
  have hchoice (d : D) : ∃ θ, B θ = d.1 := hDC d.2
  choose parameters hparameters using hchoice
  obtain ⟨w, hw, hsum⟩ := ENNReal.exists_pos_sum_of_countable' (ε := ⊤) ENNReal.top_ne_zero D
  let μ : Measure Ω := Measure.sum (fun d : D => w d • P (parameters d))
  have hfinite : IsFiniteMeasure μ := ⟨by simpa [μ, Measure.sum_apply_of_countable] using hsum⟩
  refine ⟨↥D, inferInstance, parameters, w, μ, hfinite, rfl, ?_, ?_⟩
  · intro s hs
    simp only [μ, Measure.sum_apply_of_countable, Measure.smul_apply, smul_eq_mul]
    simp [fun d => hdom (parameters d) hs]
  · intro θ s hs
    have hnull (d : D) : P (parameters d) s = 0 := by
      have hz : ∑' d : D, w d * P (parameters d) s = 0 := by
        simpa only [μ, Measure.sum_apply_of_countable, Measure.smul_apply, smul_eq_mul] using hs
      exact (mul_eq_zero.mp ((ENNReal.tsum_eq_zero.mp hz) d)).resolve_left (hw d).ne'
    have hae (d : D) : ∀ᵐ x ∂ν, x ∈ B (parameters d) → x ∉ s := by
      change ∀ᵐ x ∂ν, (P (parameters d)).rnDeriv ν x ≠ 0 → x ∉ s
      rw [← ae_withDensity_iff (Measure.measurable_rnDeriv (P (parameters d)) ν),
        Measure.withDensity_rnDeriv_eq _ _ (hdom (parameters d))]
      simpa [ae_iff] using hnull d
    have hfull : ∀ᵐ x ∂ν, x ∈ B θ → x ∉ s := by
      filter_upwards [hcover (B θ) ⟨θ, rfl⟩, ae_all_iff.mpr hae] with x hx ha
      intro hxB
      obtain ⟨d, hd, hxd⟩ := hx hxB
      exact ha ⟨d, hd⟩ (by simpa only [hparameters] using hxd)
    rw [← Measure.withDensity_rnDeriv_eq (P θ) ν (hdom θ)]
    have := (ae_withDensity_iff (Measure.measurable_rnDeriv (P θ) ν)).mpr hfull
    simpa [ae_iff] using this

end LectureNotes
