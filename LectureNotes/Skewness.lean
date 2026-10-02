import LectureNotes.VarianceAsymptotics

noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Finset

/-- Population skewness. A finite third absolute moment and positive variance
are the usual conditions for interpreting this standardized third moment. -/
def populationSkewness {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) : ℝ :=
  (∫ ω, (X ω - P[X]) ^ 3 ∂P) / (Real.sqrt Var[X; P]) ^ 3

/-- L5 Example 3 uses the n−1 sample variance in the denominator and the
n-normalized third centered sample moment in the numerator. -/
def sampleSkewness {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sampleMean (fun i => (x i - sampleMean x) ^ 3) / (Real.sqrt (sampleVariance x)) ^ 3

theorem sampleMean_centered_cube {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    sampleMean (fun i => (x i - sampleMean x) ^ 3) =
      sampleMean (fun i => (x i) ^ 3) -
        3 * sampleMean x * sampleMean (fun i => (x i) ^ 2) + 2 * (sampleMean x) ^ 3 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have he (i : Fin n) : (x i - sampleMean x) ^ 3 =
      (x i) ^ 3 - (3 * sampleMean x) * (x i) ^ 2 +
        (3 * (sampleMean x) ^ 2) * x i - (sampleMean x) ^ 3 := by ring
  conv_lhs => rw [sampleMean]
  simp only [he, sum_add_distrib, sum_sub_distrib, ← mul_sum,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold sampleMean
  simp only [Fintype.card_fin]
  field_simp
  ring

/-- The displayed skewness estimator is a nonlinear function of the first
three empirical raw moments; the n/(n−1) factor retains the source's s³. -/
theorem sampleSkewness_eq_raw_moments {n : ℕ} (hn : 1 < n) (x : Fin n → ℝ) :
    sampleSkewness x =
      (sampleMean (fun i => (x i) ^ 3) -
        3 * sampleMean x * sampleMean (fun i => (x i) ^ 2) + 2 * (sampleMean x) ^ 3) /
      (Real.sqrt ((n : ℝ) / (n - 1) *
        (sampleMean (fun i => (x i) ^ 2) - (sampleMean x) ^ 2))) ^ 3 := by
  rw [sampleSkewness, sampleMean_centered_cube (by omega),
    sampleVariance_eq_scaled_empiricalVariance hn, empiricalVariance_eq_secondMoment_sub_sq]

theorem sampleSkewness_measurable {n : ℕ} :
    Measurable (sampleSkewness : (Fin n → ℝ) → ℝ) := by
  unfold sampleSkewness sampleVariance sampleMean
  fun_prop

end LectureNotes
