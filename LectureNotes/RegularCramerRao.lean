import LectureNotes.RegularDensity

/-! L6: the statistical model, differentiated expectations, and Cramér–Rao. -/
noncomputable section
namespace LectureNotes.RegularDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
variable (D : LectureNotes.RegularDensity ν) {θ : ℝ} (hθ : θ ∈ D.domain)

def model (θ : ℝ) : Measure Ω := ν.withDensity (fun ω => ENNReal.ofReal (D.density θ ω))

include hθ
theorem model_isProbabilityMeasure : IsProbabilityMeasure (D.model θ) := by
  constructor
  rw [model, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (D.density_integrable θ hθ)
      ((D.positive θ hθ).mono (fun _ h => h.le)), D.normalized θ hθ]
  simp

theorem integral_model (T : Ω → ℝ) :
    (D.model θ)[T] = ∫ ω, T ω * D.density θ ω ∂ν := by
  rw [model, integral_withDensity_eq_integral_toReal_smul₀
    (D.density_measurable θ hθ).aemeasurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [D.positive θ hθ] with ω hω
  simp [ENNReal.toReal_ofReal hω.le, mul_comm]

theorem model_score_zero : (D.model θ)[D.score θ] = 0 := by
  rw [D.integral_model hθ]
  exact D.first_information_equality hθ

theorem model_fisherInformation :
    LectureNotes.FisherInformation (D.model θ) (D.score θ) = D.information θ :=
  D.integral_model hθ _

/-- Differentiation of an estimator's mean, with an integrable bound on the
estimator times the density derivative. The derivative identity is proved. -/
theorem differentiate_mean (T : Ω → ℝ) (hT : AEStronglyMeasurable T ν)
    (hTf : Integrable (fun ω => T ω * D.density θ ω) ν)
    (hbound : Integrable (fun ω => ‖T ω‖ * D.boundFirst ω) ν) :
    HasDerivAt (fun t => (D.model t)[T])
      ((D.model θ)[fun ω => T ω * D.score θ ω]) θ := by
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (D.isOpen_domain.mem_nhds hθ)
    (Filter.Eventually.mono (D.isOpen_domain.mem_nhds hθ)
      (fun t ht => hT.mul (D.density_measurable t ht))) hTf
    (hT.mul (D.first_measurable θ hθ))
    (D.first_bound.mono (fun ω hω t ht => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hω t ht) (norm_nonneg _)))
    hbound
    (D.first_derivative.mono (fun ω hω t ht => (hω t ht).const_mul (T ω)))
  have he : (fun t => (D.model t)[T]) =ᶠ[𝓝 θ]
      (fun t => ∫ ω, T ω * D.density t ω ∂ν) :=
    Filter.Eventually.mono (D.isOpen_domain.mem_nhds hθ)
      (fun t ht => D.integral_model ht T)
  have hs : (D.model θ)[fun ω => T ω * D.score θ ω] =
      ∫ ω, T ω * D.first θ ω ∂ν := by
    rw [D.integral_model hθ]
    apply integral_congr_ae
    filter_upwards [D.positive θ hθ] with ω hω
    dsimp [score]
    field_simp
  rw [hs]
  exact hd.2.congr_of_eventuallyEq he

/-- L6 Theorem 2 for an explicitly dominated regular density family. -/
theorem cramer_rao (T : Ω → ℝ) (hT : AEStronglyMeasurable T ν)
    (hTf : Integrable (fun ω => T ω * D.density θ ω) ν)
    (hbound : Integrable (fun ω => ‖T ω‖ * D.boundFirst ω) ν)
    (hT2 : MemLp T 2 (D.model θ)) (hS2 : MemLp (D.score θ) 2 (D.model θ))
    (hI : 0 < D.information θ) :
    (deriv (fun t => (D.model t)[T]) θ) ^ 2 / D.information θ ≤
      Var[T; D.model θ] := by
  letI := D.model_isProbabilityMeasure hθ
  rw [← D.model_fisherInformation hθ] at hI ⊢
  exact LectureNotes.cramer_rao_bound _ hT2 hS2 (D.model_score_zero hθ) hI
    (D.differentiate_mean hθ T hT hTf hbound)

/-- The unbiased Cramér–Rao bound. Unbiasedness is imposed throughout the
parameter domain, not just at the parameter where the bound is evaluated. -/
theorem cramer_rao_unbiased (T : Ω → ℝ) (hT : AEStronglyMeasurable T ν)
    (hTf : Integrable (fun ω => T ω * D.density θ ω) ν)
    (hbound : Integrable (fun ω => ‖T ω‖ * D.boundFirst ω) ν)
    (hT2 : MemLp T 2 (D.model θ)) (hS2 : MemLp (D.score θ) 2 (D.model θ))
    (hI : 0 < D.information θ)
    (hunbiased : ∀ t ∈ D.domain, LectureNotes.Unbiased (D.model t) T t) :
    1 / D.information θ ≤ Var[T; D.model θ] := by
  have hmean : (fun t => (D.model t)[T]) =ᶠ[𝓝 θ] (fun t => t) :=
    Filter.Eventually.mono (D.isOpen_domain.mem_nhds hθ) (fun t ht => (hunbiased t ht).2)
  have hd : deriv (fun t => (D.model t)[T]) θ = 1 :=
    ((hasDerivAt_id θ).congr_of_eventuallyEq hmean).deriv
  simpa only [hd, one_pow] using D.cramer_rao hθ T hT hTf hbound hT2 hS2 hI
end LectureNotes.RegularDensity
