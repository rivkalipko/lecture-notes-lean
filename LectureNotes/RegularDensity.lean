import LectureNotes.Information

/-! L6 information equalities with explicit dominated differentiation.
The base measure may be Lebesgue measure or a counting measure. The density is
positive on a common support (the underlying space). The bounds concern
derivatives of the density, which actually justify differentiating its integral. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

structure RegularDensity {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) where
  domain : Set ℝ
  isOpen_domain : IsOpen domain
  density : ℝ → Ω → ℝ
  first : ℝ → Ω → ℝ
  second : ℝ → Ω → ℝ
  boundFirst : Ω → ℝ
  boundSecond : Ω → ℝ
  density_measurable : ∀ θ ∈ domain, AEStronglyMeasurable (density θ) ν
  first_measurable : ∀ θ ∈ domain, AEStronglyMeasurable (first θ) ν
  second_measurable : ∀ θ ∈ domain, AEStronglyMeasurable (second θ) ν
  density_integrable : ∀ θ ∈ domain, Integrable (density θ) ν
  positive : ∀ θ ∈ domain, ∀ᵐ ω ∂ν, 0 < density θ ω
  normalized : ∀ θ ∈ domain, (∫ ω, density θ ω ∂ν) = 1
  first_derivative : ∀ᵐ ω ∂ν, ∀ θ ∈ domain,
    HasDerivAt (fun t => density t ω) (first θ ω) θ
  second_derivative : ∀ᵐ ω ∂ν, ∀ θ ∈ domain,
    HasDerivAt (fun t => first t ω) (second θ ω) θ
  first_bound : ∀ᵐ ω ∂ν, ∀ θ ∈ domain, ‖first θ ω‖ ≤ boundFirst ω
  second_bound : ∀ᵐ ω ∂ν, ∀ θ ∈ domain, ‖second θ ω‖ ≤ boundSecond ω
  integrable_first_bound : Integrable boundFirst ν
  integrable_second_bound : Integrable boundSecond ν

namespace RegularDensity
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
variable (D : RegularDensity ν) {θ : ℝ} (hθ : θ ∈ D.domain)

def score (θ : ℝ) (ω : Ω) : ℝ := D.first θ ω / D.density θ ω
def logHessian (θ : ℝ) (ω : Ω) : ℝ :=
  D.second θ ω / D.density θ ω - D.score θ ω ^ 2
def information (θ : ℝ) : ℝ :=
  ∫ ω, D.score θ ω ^ 2 * D.density θ ω ∂ν

include hθ
theorem differentiate_normalization :
    Integrable (D.first θ) ν ∧
      HasDerivAt (fun t => ∫ ω, D.density t ω ∂ν) (∫ ω, D.first θ ω ∂ν) θ :=
  hasDerivAt_integral_of_dominated_loc_of_deriv_le (D.isOpen_domain.mem_nhds hθ)
    (Filter.Eventually.mono (D.isOpen_domain.mem_nhds hθ)
      (fun t ht => D.density_measurable t ht))
    (D.density_integrable θ hθ) (D.first_measurable θ hθ)
    D.first_bound D.integrable_first_bound D.first_derivative

theorem integral_first_zero : (∫ ω, D.first θ ω ∂ν) = 0 := by
  have h := (D.differentiate_normalization hθ).2
  have he : (fun t => ∫ ω, D.density t ω ∂ν) =ᶠ[𝓝 θ] (fun _ => 1) :=
    Filter.Eventually.mono (D.isOpen_domain.mem_nhds hθ) (fun t ht => D.normalized t ht)
  have hc := (hasDerivAt_const θ (1 : ℝ)).congr_of_eventuallyEq he
  exact h.unique hc

theorem integral_second_zero : (∫ ω, D.second θ ω ∂ν) = 0 := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (D.isOpen_domain.mem_nhds hθ)
    (Filter.Eventually.mono (D.isOpen_domain.mem_nhds hθ)
      (fun t ht => D.first_measurable t ht))
    (D.differentiate_normalization hθ).1 (D.second_measurable θ hθ)
    D.second_bound D.integrable_second_bound D.second_derivative
  have he : (fun t => ∫ ω, D.first t ω ∂ν) =ᶠ[𝓝 θ] (fun _ => 0) :=
    Filter.Eventually.mono (D.isOpen_domain.mem_nhds hθ) (fun _ ht => D.integral_first_zero ht)
  exact h.2.unique ((hasDerivAt_const θ (0 : ℝ)).congr_of_eventuallyEq he)

theorem first_information_equality :
    (∫ ω, D.score θ ω * D.density θ ω ∂ν) = 0 := by
  calc
    _ = ∫ ω, D.first θ ω ∂ν := by
      apply integral_congr_ae
      filter_upwards [D.positive θ hθ] with ω hω
      exact div_mul_cancel₀ _ hω.ne'
    _ = 0 := D.integral_first_zero hθ

theorem score_is_log_derivative :
    ∀ᵐ ω ∂ν, HasDerivAt (fun t => Real.log (D.density t ω)) (D.score θ ω) θ := by
  filter_upwards [D.positive θ hθ, D.first_derivative] with ω hpos hd
  exact (hd θ hθ).log hpos.ne'

/-- The displayed second log-derivative is the derivative of the score. -/
theorem logHessian_is_score_derivative :
    ∀ᵐ ω ∂ν, HasDerivAt (fun t => D.score t ω) (D.logHessian θ ω) θ := by
  filter_upwards [D.positive θ hθ, D.first_derivative, D.second_derivative]
    with ω hpos hd1 hd2
  have h := (hd2 θ hθ).div (hd1 θ hθ) hpos.ne'
  have he : D.logHessian θ ω =
      (D.second θ ω * D.density θ ω - D.first θ ω * D.first θ ω) /
        D.density θ ω ^ 2 := by
    dsimp [score, logHessian]
    field_simp
  rw [he]
  simpa only [score, Pi.div_def] using h

theorem second_information_equality
    (hI : Integrable (fun ω => D.score θ ω ^ 2 * D.density θ ω) ν) :
    D.information θ = -(∫ ω, D.logHessian θ ω * D.density θ ω ∂ν) := by
  have hi2 : Integrable (D.second θ) ν :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (D.isOpen_domain.mem_nhds hθ)
      (Filter.Eventually.mono (D.isOpen_domain.mem_nhds hθ)
        (fun t ht => D.first_measurable t ht))
      (D.differentiate_normalization hθ).1 (D.second_measurable θ hθ)
      D.second_bound D.integrable_second_bound D.second_derivative).1
  have heq : (∫ ω, D.logHessian θ ω * D.density θ ω ∂ν) =
      (∫ ω, D.second θ ω ∂ν) - D.information θ := by
    unfold information
    rw [← integral_sub hi2 hI]
    apply integral_congr_ae
    filter_upwards [D.positive θ hθ] with ω hω
    dsimp [logHessian]
    rw [sub_mul, div_mul_cancel₀ _ hω.ne']
  rw [heq, D.integral_second_zero hθ]
  ring
end RegularDensity
end LectureNotes
