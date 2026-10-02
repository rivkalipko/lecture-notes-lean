import LectureNotes.ConfidenceSets

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- L11's maximum absolute standardized coordinate error. The finite product
space carries the sup norm, so this is the maximum over coordinates. -/
def standardizedMax {ι : Type*} [Fintype ι]
    (estimate parameter scale : ι → ℝ) (rate : ℝ) : ℝ :=
  ‖fun i => (estimate i - parameter i) / scale i * rate‖

/-- Exact scalar inversion, with the positive estimated scale made explicit. -/
theorem abs_standardized_error_le_iff (estimate parameter scale rate c : ℝ)
    (hs : 0 < scale) (hr : 0 < rate) :
    |(estimate - parameter) / scale * rate| ≤ c ↔
      parameter ∈ Icc (estimate - c * scale / rate) (estimate + c * scale / rate) := by
  have he : (estimate - parameter) / scale * rate = (estimate - parameter) / (scale / rate) := by
    field_simp
  rw [he, abs_le, location_pivot_inversion _ _ _ _ _ (div_pos hs hr)]
  simp only [Set.mem_Icc, neg_mul, sub_neg_eq_add, mul_div_assoc]

/-- The acceptance region of the maximum statistic is exactly the Cartesian
product of the reported two-sided intervals. -/
theorem standardizedMax_rectangle {ι : Type*} [Fintype ι]
    (estimate parameter scale : ι → ℝ) {rate c : ℝ}
    (hs : ∀ i, 0 < scale i) (hr : 0 < rate) (hc : 0 ≤ c) :
    standardizedMax estimate parameter scale rate ≤ c ↔
      ∀ i, parameter i ∈ Icc (estimate i - c * scale i / rate)
        (estimate i + c * scale i / rate) := by
  rw [standardizedMax, pi_norm_le_iff_of_nonneg hc]
  simp only [Real.norm_eq_abs, abs_standardized_error_le_iff _ _ _ _ _ (hs _) hr]

/-- The two-coordinate formula printed in L11, retaining its absolute values. -/
theorem bivariate_standardized_rectangle (a b a₀ b₀ sa sb n c : ℝ)
    (ha : 0 < sa) (hb : 0 < sb) (hn : 0 < n) :
    max (|(a - a₀) / sa * Real.sqrt n|) (|(b - b₀) / sb * Real.sqrt n|) ≤ c ↔
      a₀ ∈ Icc (a - c * sa / Real.sqrt n) (a + c * sa / Real.sqrt n) ∧
      b₀ ∈ Icc (b - c * sb / Real.sqrt n) (b + c * sb / Real.sqrt n) := by
  rw [max_le_iff, abs_standardized_error_le_iff _ _ _ _ _ ha (Real.sqrt_pos.mpr hn),
    abs_standardized_error_le_iff _ _ _ _ _ hb (Real.sqrt_pos.mpr hn)]

/-- Random bootstrap critical values preserve this exact event identity;
calibration of the critical value is a separate probabilistic assertion. -/
theorem standardizedMax_coverage_identity {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (estimate scale : Ω → ι → ℝ) (parameter : ι → ℝ)
    (rate c : Ω → ℝ) (hs : ∀ ω i, 0 < scale ω i)
    (hr : ∀ ω, 0 < rate ω) (hc : ∀ ω, 0 ≤ c ω) :
    P.real {ω | standardizedMax (estimate ω) parameter (scale ω) (rate ω) ≤ c ω} =
      P.real {ω | ∀ i, parameter i ∈ Icc
        (estimate ω i - c ω * scale ω i / rate ω)
        (estimate ω i + c ω * scale ω i / rate ω)} := by
  congr 1
  ext ω
  exact standardizedMax_rectangle _ _ _ (hs ω) (hr ω) (hc ω)

/-- Once the maximum-statistic acceptance probabilities are calibrated,
the simultaneous rectangular region has exactly the same coverage limit. -/
theorem standardizedMax_rectangle_coverage {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (estimate scale : ℕ → Ω → ι → ℝ) (parameter : ι → ℝ)
    (rate c : ℕ → Ω → ℝ) (hs : ∀ n ω i, 0 < scale n ω i)
    (hr : ∀ n ω, 0 < rate n ω) (hc : ∀ n ω, 0 ≤ c n ω) {q : ℝ}
    (h : Tendsto (fun n => P.real {ω |
      standardizedMax (estimate n ω) parameter (scale n ω) (rate n ω) ≤ c n ω}) atTop (𝓝 q)) :
    Tendsto (fun n => P.real {ω | ∀ i, parameter i ∈ Icc
      (estimate n ω i - c n ω * scale n ω i / rate n ω)
      (estimate n ω i + c n ω * scale n ω i / rate n ω)}) atTop (𝓝 q) := by
  simpa only [standardizedMax_coverage_identity P _ _ parameter _ _ (hs _) (hr _) (hc _)] using h

end LectureNotes
