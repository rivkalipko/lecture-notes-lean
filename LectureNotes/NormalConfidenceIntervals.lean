import LectureNotes.QuantileIntervals
import LectureNotes.SamplingAtomlessness

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- Positive random variables have positive interior quantiles. This prevents
division by zero in the variance interval. -/
theorem distributionQuantile_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hp : ∀ᵐ x ∂μ, 0 < x) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 < distributionQuantile μ q := by
  have hz : μ (Iic 0) = 0 := by
    change μ {x | x ≤ 0} = 0
    simpa only [ae_iff, not_lt] using hp
  by_contra h
  have he : μ (Iic (distributionQuantile μ q)) = 0 :=
    measure_mono_null (Iic_subset_Iic.mpr (le_of_not_gt h)) hz
  have hb := (distributionQuantile_bracket μ q hq).2
  rw [measureReal_def, he, ENNReal.toReal_zero] at hb
  exact not_le_of_gt hq.1 hb

/-- The exact Student interval, for arbitrary interior tail allocations.
This is coverage only; it does not claim unrestricted two-sided UMP optimality. -/
theorem normal_student_quantile_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 1 < n)
    {X : Fin n → Ω → ℝ} {θ : ℝ} {v : ℝ≥0} (hv : 0 < v)
    (hX : ∀ i, HasLaw (X i) (gaussianReal θ v) P) (hind : iIndepFun X P)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    P.real {ω | θ ∈ Icc
      (sampleMean (fun i => X i ω) - distributionQuantile (studentT (n - 1)) b *
        Real.sqrt (sampleVariance (fun i => X i ω) / n))
      (sampleMean (fun i => X i ω) - distributionQuantile (studentT (n - 1)) a *
        Real.sqrt (sampleVariance (fun i => X i ω) / n))} = b - a := by
  have : NullSingletonClass (studentT (n - 1)) := studentT_nullSingletonClass (by omega)
  apply location_quantile_coverage _ (normal_studentized_mean hn hv hX hind) ha hb hab
  filter_upwards [normal_sampleVariance_pos hn hv hX hind] with ω hω
  exact Real.sqrt_pos.mpr (div_pos hω (by exact_mod_cast (show 0 < n by omega)))

/-- L11 Example 2, including all unequal-tail allocations. The sample mean is
unknown, so the degrees of freedom are `n-1` and the numerator is `(n-1)s²`. -/
theorem normal_variance_quantile_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} (hn : 1 < n)
    {X : Fin n → Ω → ℝ} {θ : ℝ} {v : ℝ≥0} (hv : 0 < v)
    (hX : ∀ i, HasLaw (X i) (gaussianReal θ v) P) (hind : iIndepFun X P)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    P.real {ω | (v : ℝ) ∈ Icc
      (((n : ℝ) - 1) * sampleVariance (fun i => X i ω) / distributionQuantile (chiSquared (n - 1)) b)
      (((n : ℝ) - 1) * sampleVariance (fun i => X i ω) / distributionQuantile (chiSquared (n - 1)) a)}
      = b - a := by
  have hdf : 0 < n - 1 := by omega
  have : NullSingletonClass (chiSquared (n - 1)) := chiSquared_nullSingletonClass hdf
  have hqa := distributionQuantile_pos _ (chiSquared_ae_pos hdf) ha
  have hqb := distributionQuantile_pos _ (chiSquared_ae_pos hdf) hb
  have h := pivot_quantile_coverage (normal_sampleVariance hn hv hX hind) ha hb hab
  convert h using 2
  ext ω
  exact (variance_pivot_inversion _ _ _ _ (by exact_mod_cast hv) hqa hqb).symm

end LectureNotes
