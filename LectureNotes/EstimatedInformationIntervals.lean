import LectureNotes.QuantileIntervals
import LectureNotes.InformationEstimation
import LectureNotes.NormalHighestDensity

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

/-- The estimated-information interval has pointwise frequentist coverage
when the centered estimator has the claimed Gaussian limit and the positive
information estimate is consistent. Index `n` represents sample size `n+1`. -/
theorem estimated_information_interval_coverage {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T J : ℕ → Ω → ℝ} {θ : ℝ} {I : ℝ≥0} (hI : 0 < I)
    (hJpos : ∀ n, ∀ᵐ ω ∂P, 0 < J n ω)
    (hJm : ∀ n, AEMeasurable (J n) P)
    (hJ : ConvergesInProbability P J (fun _ => (I : ℝ)))
    {Z : Ω' → ℝ}
    (hT : ConvergesInDistribution P Q
      (fun (n : ℕ) ω => Real.sqrt (n + 1) * (T n ω - θ)) Z)
    (hZ : HasLaw Z (gaussianReal 0 I⁻¹) Q)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => P.real {ω | θ ∈ Icc
      (T n ω - distributionQuantile (gaussianReal 0 1) b *
        Real.sqrt (1 / ((n + 1) * J n ω)))
      (T n ω - distributionQuantile (gaussianReal 0 1) a *
        Real.sqrt (1 / ((n + 1) * J n ω)))}) atTop (𝓝 (b - a)) := by
  have hIreal : (0 : ℝ) < I := by exact_mod_cast hI
  have hscale : ConvergesInProbability P (fun n ω => Real.sqrt ((J n ω)⁻¹))
      (fun _ => Real.sqrt ((I : ℝ)⁻¹)) :=
    continuous_mapping_probability_const (g := fun x : ℝ => Real.sqrt x⁻¹)
      (Real.continuous_sqrt.continuousAt.comp (continuousAt_inv₀ hIreal.ne')) hJ
  have hscaleM n : AEMeasurable (fun ω => Real.sqrt ((J n ω)⁻¹)) P :=
    Real.continuous_sqrt.measurable.comp_aemeasurable (hJm n).inv
  have hnorm := slutsky_div (Real.sqrt_pos.mpr (inv_pos.mpr hIreal)).ne' hT hscale hscaleM
  have hz := normal_standardize (inv_pos.mpr hI) hZ
  simp only [sub_zero, NNReal.coe_inv] at hz
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hcov := asymptotic_quantile_coverage hnorm hz ha hb hab
  convert hcov using 1
  funext n
  apply measureReal_congr
  filter_upwards [hJpos n] with ω hω
  change (θ ∈ Icc _ _) = (_ ∈ Icc _ _)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hs : 0 < Real.sqrt (1 / (((n : ℝ) + 1) * J n ω)) := by positivity
  have he : Real.sqrt (1 / (((n : ℝ) + 1) * J n ω)) =
      Real.sqrt ((J n ω)⁻¹) / Real.sqrt ((n : ℝ) + 1) := by
    rw [← Real.sqrt_div (by positivity : (0 : ℝ) ≤ (J n ω)⁻¹)]
    congr 1
    simp only [mul_inv_rev, div_eq_mul_inv, one_mul]
  have hid : (T n ω - θ) / Real.sqrt (1 / (((n : ℝ) + 1) * J n ω)) =
      Real.sqrt ((n : ℝ) + 1) * (T n ω - θ) / Real.sqrt ((J n ω)⁻¹) := by
    rw [he, div_div_eq_mul_div]
    ring
  exact propext (by
    rw [← hid]
    exact (location_pivot_inversion _ _ _ _ _ hs).symm)

/-- The equal-tailed specialization is the interval displayed in L12. Its
frequentist assertion uses the sampling law, separately from posterior content. -/
theorem estimated_information_equalTailed_coverage {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T J : ℕ → Ω → ℝ} {θ : ℝ} {I : ℝ≥0} (hI : 0 < I)
    (hJpos : ∀ n, ∀ᵐ ω ∂P, 0 < J n ω)
    (hJm : ∀ n, AEMeasurable (J n) P)
    (hJ : ConvergesInProbability P J (fun _ => (I : ℝ)))
    {Z : Ω' → ℝ}
    (hT : ConvergesInDistribution P Q
      (fun (n : ℕ) ω => Real.sqrt (n + 1) * (T n ω - θ)) Z)
    (hZ : HasLaw Z (gaussianReal 0 I⁻¹) Q)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω | θ ∈ Icc
      (T n ω - distributionQuantile (gaussianReal 0 1) (1 - α / 2) *
        Real.sqrt (1 / ((n + 1) * J n ω)))
      (T n ω + distributionQuantile (gaussianReal 0 1) (1 - α / 2) *
        Real.sqrt (1 / ((n + 1) * J n ω)))}) atTop (𝓝 (1 - α)) := by
  have ha : α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hb : 1 - α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hsym : distributionQuantile (gaussianReal 0 1) (α / 2) =
      -distributionQuantile (gaussianReal 0 1) (1 - α / 2) := by
    have h := standardNormal_quantile_symmetry ha
    linarith
  have h := estimated_information_interval_coverage hI hJpos hJm hJ hT hZ
    ha hb (by linarith [hα.2])
  simp_rw [hsym, neg_mul, sub_neg_eq_add] at h
  convert h using 1
  congr 1
  ring

end LectureNotes
