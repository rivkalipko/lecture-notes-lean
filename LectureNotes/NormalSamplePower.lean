import LectureNotes.PowerAnalysis

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- The alternative law of the actual Z statistic from an IID normal sample.
Centering at the null mean shifts its mean without changing unit variance. -/
theorem normal_iid_z_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    {μ μ₀ : ℝ} {v : ℝ≥0} (hv : 0 < v)
    (hX : ∀ i, HasLaw (X i) (gaussianReal μ v) P) (hind : iIndepFun X P) :
    HasLaw (fun ω => Real.sqrt n * (sampleMean (fun i => X i ω) - μ₀) / Real.sqrt v)
      (gaussianReal (Real.sqrt n * (μ - μ₀) / Real.sqrt v) 1) P := by
  have hvn : (0 : ℝ≥0) < v / n := div_pos hv (Nat.cast_pos.mpr hn)
  have h := gaussianReal_add_const (normal_standardize hvn (normal_sampleMean hn hX hind))
    ((μ - μ₀) / Real.sqrt (v / n : ℝ≥0))
  have he : (fun ω => (sampleMean (fun i => X i ω) - μ) / Real.sqrt (v / n : ℝ≥0) +
      (μ - μ₀) / Real.sqrt (v / n : ℝ≥0)) =
      (fun ω => (sampleMean (fun i => X i ω) - μ₀) / Real.sqrt (v / n : ℝ≥0)) := by
    funext ω
    ring
  rw [he] at h
  have hs (a : ℝ) : a / Real.sqrt (v / n : ℝ≥0) = Real.sqrt n * a / Real.sqrt v := by
    rw [NNReal.coe_div, NNReal.coe_natCast, Real.sqrt_div v.coe_nonneg, div_div_eq_mul_div]
    ring
  simpa only [zero_add, hs] using h

/-- For a standardized normal statistic, the lecture's sample-size formula
is a sufficient bound for the exact two-sided power, not an exact inversion. -/
theorem normal_power_from_sample_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → ℝ} (n : ℕ)
    {σ τ α q : ℝ} (hσ : 0 < σ) (hτ : τ ≠ 0)
    (hα : α ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (1 / 2 : ℝ) 1)
    (hm : Measurable T) (hT : HasLaw T (gaussianReal (Real.sqrt n * τ / σ) 1) P)
    (hsize : (distributionQuantile (gaussianReal 0 1) (1 - α / 2) +
      distributionQuantile (gaussianReal 0 1) q) ^ 2 * σ ^ 2 / τ ^ 2 ≤ (n : ℝ)) :
    q ≤ P.real {ω | distributionQuantile (gaussianReal 0 1) (1 - α / 2) < |T ω|} := by
  have hc : 0 < distributionQuantile (gaussianReal 0 1) (1 - α / 2) :=
    standardNormal_quantile_pos ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hq0 := standardNormal_quantile_pos hq
  apply normal_two_sided_power_sufficient hm hT hc.le
    (show q ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hq.1], hq.2⟩)
  rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hσ]
  exact (normal_sample_size_rule n hσ hτ (add_nonneg hc.le hq0.le)).mpr hsize

/-- The sample-size guarantee for the actual normal IID sampling model. -/
theorem normal_iid_sample_size_power {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) {μ μ₀ : ℝ} {v : ℝ≥0} (hv : 0 < v)
    (hX : ∀ i, HasLaw (X i) (gaussianReal μ v) P) (hind : iIndepFun X P)
    (heffect : μ ≠ μ₀) {α q : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (1 / 2 : ℝ) 1)
    (hsize : (distributionQuantile (gaussianReal 0 1) (1 - α / 2) +
      distributionQuantile (gaussianReal 0 1) q) ^ 2 * (v : ℝ) / (μ - μ₀) ^ 2 ≤ (n : ℝ)) :
    q ≤ P.real {ω | distributionQuantile (gaussianReal 0 1) (1 - α / 2) <
      |Real.sqrt n * (sampleMean (fun i => X i ω) - μ₀) / Real.sqrt v|} := by
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hv)
  apply normal_power_from_sample_size n hs (sub_ne_zero.mpr heffect) hα hq
    (by unfold sampleMean; fun_prop) (normal_iid_z_law hn hv hX hind)
  simpa only [Real.sq_sqrt v.coe_nonneg] using hsize

end LectureNotes
