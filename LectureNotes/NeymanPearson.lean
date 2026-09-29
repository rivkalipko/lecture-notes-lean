import LectureNotes.Testing

set_option autoImplicit false

/-! L9 Theorem 1 on a general dominated measurable sample space.
Optimality conditions are almost everywhere; the threshold may be zero. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

theorem density_model_isProbabilityMeasure {f : Ω → ℝ}
    (hi : Integrable f ν) (hn : ∀ᵐ x ∂ν, 0 ≤ f x) (h : (∫ x, f x ∂ν) = 1) :
    IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (f x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hn, h]
  simp

namespace StatisticalTest

theorem integrable_mul_density (φ : StatisticalTest Ω) {f : Ω → ℝ}
    (hf : Integrable f ν) : Integrable (fun x => φ.reject x * f x) ν :=
  hf.bdd_mul φ.measurable_reject.aestronglyMeasurable
    (ae_of_all _ (fun x => show ‖φ.reject x‖ ≤ 1 by
      simpa [Real.norm_eq_abs, abs_of_nonneg (φ.nonneg x)] using φ.le_one x))

def densityPower (φ : StatisticalTest Ω) (ν : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ∫ x, φ.reject x * f x ∂ν

theorem densityPower_eq_power (φ : StatisticalTest Ω) {f : Ω → ℝ}
    (hf : AEMeasurable f ν) (hn : ∀ᵐ x ∂ν, 0 ≤ f x) :
    φ.densityPower ν f = φ.power (ν.withDensity (fun x => ENNReal.ofReal (f x))) := by
  rw [power, integral_withDensity_eq_integral_toReal_smul₀ hf.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hn] with x hx
  simp [ENNReal.toReal_ofReal hx, smul_eq_mul, mul_comm]

/-- The threshold is imposed directly on densities, so no division by zero occurs. -/
def HasLikelihoodThreshold (φ : StatisticalTest Ω) (ν : Measure Ω)
    (f₀ f₁ : Ω → ℝ) (k : ℝ) : Prop :=
  ∀ᵐ x ∂ν, (k * f₀ x < f₁ x → φ.reject x = 1) ∧
    (f₁ x < k * f₀ x → φ.reject x = 0)

theorem likelihood_threshold_contrast_nonneg (φ ψ : StatisticalTest Ω)
    {f₀ f₁ : Ω → ℝ} {k : ℝ} (h : φ.HasLikelihoodThreshold ν f₀ f₁ k) :
    0 ≤ᵐ[ν] fun x => (φ.reject x - ψ.reject x) * (f₁ x - k * f₀ x) := by
  filter_upwards [h] with x hx
  rcases lt_trichotomy (f₁ x) (k * f₀ x) with hlt | he | hgt
  · rw [hx.2 hlt]
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith [ψ.nonneg x]) (by linarith)
  · simp [he]
  · rw [hx.1 hgt]
    exact mul_nonneg (by linarith [ψ.le_one x]) (by linarith)

private theorem contrast_integrable (φ ψ : StatisticalTest Ω)
    {f₀ f₁ : Ω → ℝ} (h₀ : Integrable f₀ ν) (h₁ : Integrable f₁ ν) (k : ℝ) :
    Integrable (fun x => (φ.reject x - ψ.reject x) * (f₁ x - k * f₀ x)) ν := by
  have h := ((φ.integrable_mul_density h₁).sub (ψ.integrable_mul_density h₁)).sub
    (((φ.integrable_mul_density h₀).sub (ψ.integrable_mul_density h₀)).const_mul k)
  convert h using 1
  ext x
  simp only [Pi.sub_apply]
  ring

private theorem integral_contrast (φ ψ : StatisticalTest Ω)
    {f₀ f₁ : Ω → ℝ} (h₀ : Integrable f₀ ν) (h₁ : Integrable f₁ ν) (k : ℝ) :
    (∫ x, (φ.reject x - ψ.reject x) * (f₁ x - k * f₀ x) ∂ν) =
      φ.densityPower ν f₁ - ψ.densityPower ν f₁ -
        k * (φ.densityPower ν f₀ - ψ.densityPower ν f₀) := by
  have he (x) : (φ.reject x - ψ.reject x) * (f₁ x - k * f₀ x) =
      (φ.reject x * f₁ x - ψ.reject x * f₁ x) -
        k * (φ.reject x * f₀ x - ψ.reject x * f₀ x) := by ring
  simp_rw [he]
  have hi₁ : Integrable (fun x => φ.reject x * f₁ x - ψ.reject x * f₁ x) ν :=
    (φ.integrable_mul_density h₁).sub (ψ.integrable_mul_density h₁)
  have hi₀ : Integrable (fun x => φ.reject x * f₀ x - ψ.reject x * f₀ x) ν :=
    (φ.integrable_mul_density h₀).sub (ψ.integrable_mul_density h₀)
  rw [integral_sub hi₁ (hi₀.const_mul k), integral_const_mul,
    integral_sub (φ.integrable_mul_density h₁) (ψ.integrable_mul_density h₁),
    integral_sub (φ.integrable_mul_density h₀) (ψ.integrable_mul_density h₀)]
  rfl

/-- Neyman–Pearson sufficiency: every test of no larger size has no larger power.
Normalization of the densities is unnecessary for the integral comparison. -/
theorem neyman_pearson (φ ψ : StatisticalTest Ω) {f₀ f₁ : Ω → ℝ} {k : ℝ}
    (h₀ : Integrable f₀ ν) (h₁ : Integrable f₁ ν) (hk : 0 ≤ k)
    (hφ : φ.HasLikelihoodThreshold ν f₀ f₁ k)
    (hsize : ψ.densityPower ν f₀ ≤ φ.densityPower ν f₀) :
    ψ.densityPower ν f₁ ≤ φ.densityPower ν f₁ := by
  have h := integral_nonneg_of_ae (likelihood_threshold_contrast_nonneg φ ψ hφ)
  rw [integral_contrast φ ψ h₀ h₁ k] at h
  have := mul_nonneg hk (sub_nonneg.mpr hsize)
  linarith

/-- Necessity for a competitor attaining the same optimal power, including `k = 0`.
Conditions cannot in general be strengthened from almost everywhere to everywhere. -/
theorem neyman_pearson_necessity (φ ψ : StatisticalTest Ω) {f₀ f₁ : Ω → ℝ} {k : ℝ}
    (h₀ : Integrable f₀ ν) (h₁ : Integrable f₁ ν) (hk : 0 ≤ k)
    (hφ : φ.HasLikelihoodThreshold ν f₀ f₁ k)
    (hsize : ψ.densityPower ν f₀ ≤ φ.densityPower ν f₀)
    (hpower : ψ.densityPower ν f₁ = φ.densityPower ν f₁) :
    ψ.HasLikelihoodThreshold ν f₀ f₁ k := by
  have hnonneg := likelihood_threshold_contrast_nonneg φ ψ hφ
  have hz : (∫ x, (φ.reject x - ψ.reject x) * (f₁ x - k * f₀ x) ∂ν) = 0 := by
    have hi := integral_nonneg_of_ae hnonneg
    rw [integral_contrast φ ψ h₀ h₁ k] at hi ⊢
    have := mul_nonneg hk (sub_nonneg.mpr hsize)
    rw [hpower] at hi ⊢
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg
    (contrast_integrable φ ψ h₀ h₁ k)).mp hz
  filter_upwards [hae, hφ] with x hx hφx
  constructor
  · intro hgt
    rw [hφx.1 hgt] at hx
    have := (mul_eq_zero.mp hx).resolve_right (sub_ne_zero.mpr (ne_of_gt hgt))
    linarith
  · intro hlt
    rw [hφx.2 hlt] at hx
    have := (mul_eq_zero.mp hx).resolve_right (sub_ne_zero.mpr (ne_of_lt hlt))
    linarith

end StatisticalTest
end LectureNotes
