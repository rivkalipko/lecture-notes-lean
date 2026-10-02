import LectureNotes.GaussianStein
import LectureNotes.Testing

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

/-- Rejection weights define a finite submeasure of the null Gaussian law. -/
def normalTestWeightedMeasure (φ : StatisticalTest ℝ) (θ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  (gaussianReal θ v).withDensity (fun x => ENNReal.ofReal (φ.reject x))

theorem normalTestWeightedMeasure_le (φ : StatisticalTest ℝ) (θ : ℝ) (v : ℝ≥0) :
    normalTestWeightedMeasure φ θ v ≤ gaussianReal θ v := by
  have h := withDensity_mono (μ := gaussianReal θ v)
    (f := fun x => ENNReal.ofReal (φ.reject x)) (g := fun _ => 1)
    (ae_of_all _ (fun x => by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (φ.le_one x)))
  change (gaussianReal θ v).withDensity (fun x => ENNReal.ofReal (φ.reject x)) ≤
    (gaussianReal θ v).withDensity (1 : ℝ → ℝ≥0∞) at h
  simpa only [normalTestWeightedMeasure, withDensity_one] using h

instance normalTestWeightedMeasure_finite (φ : StatisticalTest ℝ) (θ : ℝ) (v : ℝ≥0) :
    IsFiniteMeasure (normalTestWeightedMeasure φ θ v) :=
  isFiniteMeasure_of_le _ (normalTestWeightedMeasure_le φ θ v)

theorem integral_normalTestWeightedMeasure (φ : StatisticalTest ℝ) (θ : ℝ) (v : ℝ≥0)
    (f : ℝ → ℝ) :
    (∫ x, f x ∂normalTestWeightedMeasure φ θ v) =
      ∫ x, φ.reject x * f x ∂gaussianReal θ v := by
  rw [normalTestWeightedMeasure, integral_withDensity_eq_integral_toReal_smul
    φ.measurable_reject.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (φ.nonneg _), smul_eq_mul]

/-- The weighted Gaussian has every exponential moment, so its MGF can be
 differentiated using the dominated integral theorem in the MGF library. -/
theorem normalTestWeightedMeasure_integrableExpSet (φ : StatisticalTest ℝ) (θ : ℝ) (v : ℝ≥0) :
    integrableExpSet id (normalTestWeightedMeasure φ θ v) = univ := by
  apply Set.eq_univ_of_forall
  intro t
  exact (integrable_exp_mul_gaussianReal t).mono_measure (normalTestWeightedMeasure_le φ θ v)

theorem normal_density_shift (θ₀ θ x : ℝ) (v : ℝ≥0) :
    gaussianPDFReal θ v x = Real.exp ((θ₀ ^ 2 - θ ^ 2) / (2 * v)) *
      (gaussianPDFReal θ₀ v x * Real.exp (((θ - θ₀) / v) * x)) := by
  unfold gaussianPDFReal
  rw [show -(x - θ) ^ 2 / (2 * v) =
    -(x - θ₀) ^ 2 / (2 * v) + ((θ - θ₀) / v) * x +
      (θ₀ ^ 2 - θ ^ 2) / (2 * v) by ring, Real.exp_add, Real.exp_add]
  ring

theorem normal_test_power_mgf (φ : StatisticalTest ℝ) (θ₀ θ : ℝ)
    {v : ℝ≥0} (hv : 0 < v) :
    φ.power (gaussianReal θ v) = Real.exp ((θ₀ ^ 2 - θ ^ 2) / (2 * v)) *
      mgf id (normalTestWeightedMeasure φ θ₀ v) ((θ - θ₀) / v) := by
  unfold StatisticalTest.power mgf
  rw [integral_normalTestWeightedMeasure]
  simp_rw [integral_gaussianReal_eq_integral_smul hv.ne', smul_eq_mul, id_eq]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [normal_density_shift θ₀ θ x v]
  ring

/-- Every measurable randomized test has differentiable Gaussian location
power, with the actual score-integral derivative. -/
theorem normal_test_power_hasDerivAt (φ : StatisticalTest ℝ) (θ₀ : ℝ)
    {v : ℝ≥0} (hv : 0 < v) :
    HasDerivAt (fun θ => φ.power (gaussianReal θ v))
      (∫ x, φ.reject x * ((x - θ₀) / v) ∂gaussianReal θ₀ v) θ₀ := by
  let ν := normalTestWeightedMeasure φ θ₀ v
  have ht : (0 : ℝ) ∈ interior (integrableExpSet id ν) := by
    rw [show integrableExpSet id ν = univ from normalTestWeightedMeasure_integrableExpSet φ θ₀ v]
    simp
  have hm : HasDerivAt (mgf id ν) (∫ x : ℝ, x ∂ν) 0 := by
    simpa only [id_eq, zero_mul, Real.exp_zero, mul_one] using hasDerivAt_mgf ht
  have hm' : HasDerivAt (fun θ : ℝ => mgf id ν ((θ - θ₀) / v))
      ((∫ x : ℝ, x ∂ν) / v) θ₀ := by
    have hm0 : HasDerivAt (mgf id ν) (∫ x : ℝ, x ∂ν) ((θ₀ - θ₀) / v) := by simpa using hm
    convert! hm0.comp θ₀ (((hasDerivAt_id θ₀).sub_const θ₀).div_const (v : ℝ)) using 1 <;> simp
    ring
  have hc : HasDerivAt (fun θ : ℝ => Real.exp ((θ₀ ^ 2 - θ ^ 2) / (2 * v)))
      (-θ₀ / v) θ₀ := by
    convert! ((((hasDerivAt_const θ₀ (θ₀ ^ 2)).sub ((hasDerivAt_id θ₀).pow 2)).div_const
      (2 * (v : ℝ))).exp) using 1 <;> simp
    ring
  have hh := hc.mul hm'
  have hmean : (∫ x : ℝ, x ∂ν) = ∫ x, φ.reject x * x ∂gaussianReal θ₀ v :=
    integral_normalTestWeightedMeasure φ θ₀ v _
  have hmass : mgf id ν 0 = φ.power (gaussianReal θ₀ v) := by
    simp only [mgf, zero_mul, Real.exp_zero, integral_normalTestWeightedMeasure,
      mul_one, StatisticalTest.power, ν]
  have hi : Integrable (fun x => φ.reject x * x) (gaussianReal θ₀ v) := by
    have hx : Integrable (fun x : ℝ => x) (gaussianReal θ₀ v) :=
      (memLp_id_gaussianReal 2).integrable (by norm_num)
    simpa only [mul_comm] using hx.mul_bdd φ.measurable_reject.aestronglyMeasurable
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (φ.nonneg x)] using φ.le_one x))
  have hs : (∫ x, φ.reject x * ((x - θ₀) / v) ∂gaussianReal θ₀ v) =
      ((∫ x, φ.reject x * x ∂gaussianReal θ₀ v) - θ₀ * φ.power (gaussianReal θ₀ v)) / v := by
    have he : (fun x : ℝ => φ.reject x * ((x - θ₀) / v)) =
        fun x => (φ.reject x * x - θ₀ * φ.reject x) / v := by funext x; ring
    rw [he, integral_div, integral_sub hi ((φ.integrable _).const_mul θ₀), integral_const_mul]
    rfl
  convert! hh using 1
  · funext θ
    exact normal_test_power_mgf φ θ₀ θ hv
  · simp only [sub_self, zero_div, Real.exp_zero, one_mul, hmass, hmean]
    rw [hs]
    ring

/-- A globally unbiased Gaussian location test has zero rejection-weighted
score at the null. Differentiability is proved above, not a side assumption. -/
theorem normal_unbiased_score_integral_zero (φ : StatisticalTest ℝ) (θ₀ α : ℝ)
    {v : ℝ≥0} (hv : 0 < v) (hnull : φ.power (gaussianReal θ₀ v) ≤ α)
    (halt : ∀ θ, θ ≠ θ₀ → α ≤ φ.power (gaussianReal θ v)) :
    (∫ x, φ.reject x * ((x - θ₀) / v) ∂gaussianReal θ₀ v) = 0 := by
  rw [← (normal_test_power_hasDerivAt φ θ₀ hv).deriv]
  exact unbiased_power_derivative_zero hnull halt

end LectureNotes
