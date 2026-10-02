import LectureNotes.NormalConfidenceIntervals
import LectureNotes.Testing

noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- L8 rejects a variance null for sufficiently small values of the actual
sample-variance pivot. The sample mean is unrestricted. -/
def gaussianVarianceLowerTest (n : ℕ) (v₀ c : ℝ) : StatisticalTest (Fin n → ℝ) :=
  StatisticalTest.ofRejectionSet {x | ((n : ℝ) - 1) * sampleVariance x / v₀ ≤ c}
    (measurableSet_le (by unfold sampleVariance sampleMean; fun_prop) measurable_const)

/-- Exact lower-tail power for any cutoff, with true variance v and null
variance v₀. No unknown-mean term remains in the result. -/
theorem normal_variance_lower_tail_power {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} (hn : 1 < n) {X : Fin n → Ω → ℝ}
    {μ : ℝ} {v : ℝ≥0} (hv : 0 < v) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hX : ∀ i, HasLaw (X i) (gaussianReal μ v) P) (hind : iIndepFun X P) (c : ℝ) :
    P.real {ω | ((n : ℝ) - 1) * sampleVariance (fun i => X i ω) / v₀ ≤ c} =
      cdf (chiSquared (n - 1)) (v₀ / v * c) := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have he : {ω | ((n : ℝ) - 1) * sampleVariance (fun i => X i ω) / v₀ ≤ c} =
      {ω | ((n : ℝ) - 1) * sampleVariance (fun i => X i ω) / v ≤ v₀ / v * c} := by
    ext ω
    simp only [mem_ofPred_eq, div_le_iff₀ hv₀, div_le_iff₀ hvR]
    field_simp
  rw [he, (normal_sampleVariance hn hv hX hind).measureReal_eq measurableSet_Iic,
    cdf_eq_real]
  rfl

/-- Exact size holds for every unknown mean μ, as required by the composite
variance null. The chi-square degrees of freedom are n−1. -/
theorem normal_variance_lower_quantile_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} (hn : 1 < n) {X : Fin n → Ω → ℝ}
    {μ : ℝ} {v₀ : ℝ≥0} (hv₀ : 0 < v₀)
    (hX : ∀ i, HasLaw (X i) (gaussianReal μ v₀) P) (hind : iIndepFun X P)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    P.real {ω | ((n : ℝ) - 1) * sampleVariance (fun i => X i ω) / v₀ ≤
      distributionQuantile (chiSquared (n - 1)) α} = α := by
  have : NullSingletonClass (chiSquared (n - 1)) := chiSquared_nullSingletonClass (by omega)
  rw [normal_variance_lower_tail_power hn hv₀ (by exact_mod_cast hv₀) hX hind,
    div_self (by exact_mod_cast hv₀.ne'), one_mul, cdf_eq_real,
    distributionQuantile_exact _ _ hα]

/-- At a nonnegative cutoff, exact lower-tail power is nonincreasing in the
true variance. Thus power rises as the variance alternative decreases. -/
theorem normal_variance_lower_power_antitone (d : ℕ) {v₀ c : ℝ}
    (hv₀ : 0 ≤ v₀) (hc : 0 ≤ c) :
    AntitoneOn (fun v : ℝ => cdf (chiSquared d) (v₀ / v * c)) (Ioi 0) := by
  intro v₁ hv₁ v₂ hv₂ hv
  apply monotone_cdf
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hv₀ hv₁ hv) hc

/-- The calibrated test has the same monotonicity, since every interior
chi-square quantile with positive degrees of freedom is positive. -/
theorem normal_variance_quantile_power_antitone {n : ℕ} (hn : 1 < n)
    {v₀ : ℝ} (hv₀ : 0 < v₀) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    AntitoneOn (fun v : ℝ => cdf (chiSquared (n - 1))
      (v₀ / v * distributionQuantile (chiSquared (n - 1)) α)) (Ioi 0) :=
  normal_variance_lower_power_antitone (n - 1) hv₀.le
    (distributionQuantile_pos _ (chiSquared_ae_pos (by omega)) hα).le

/-- The same power formula stated for the actual measurable test on the
full sample space. -/
theorem gaussianVarianceLowerTest_power {n : ℕ} (hn : 1 < n)
    (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P] {μ : ℝ} {v : ℝ≥0}
    (hv : 0 < v) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hX : ∀ i, HasLaw (fun x : Fin n → ℝ => x i) (gaussianReal μ v) P)
    (hind : iIndepFun (fun i (x : Fin n → ℝ) => x i) P) (c : ℝ) :
    (gaussianVarianceLowerTest n v₀ c).power P =
      cdf (chiSquared (n - 1)) (v₀ / v * c) := by
  rw [gaussianVarianceLowerTest, StatisticalTest.power_ofRejectionSet]
  exact normal_variance_lower_tail_power hn hv hv₀ hX hind c

end LectureNotes
