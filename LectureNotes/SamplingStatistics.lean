import LectureNotes.MonteCarlo

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- L2's number of heads, expressed as a sum of zero-one observations. -/
def headCount {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i

/-- L2's first-success polynomial. On zero-one data it gives the one-based
position of the first success, with zero when no success occurs. -/
def firstSuccessStatistic {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ((i : ℝ) + 1) * x i * ∏ j ∈ Finset.Iio i, (1 - x j)

/-- Difference between the number of successes before and after a chosen
split of the ordered data. -/
def splitCountDifference {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, if i.val < k then x i else 0) - (∑ i, if k ≤ i.val then x i else 0)

theorem headCount_measurable {n : ℕ} : Measurable (headCount : (Fin n → ℝ) → ℝ) := by
  unfold headCount
  fun_prop

theorem firstSuccessStatistic_measurable {n : ℕ} :
    Measurable (firstSuccessStatistic : (Fin n → ℝ) → ℝ) := by
  unfold firstSuccessStatistic
  fun_prop

theorem splitCountDifference_measurable {n : ℕ} (k : ℕ) :
    Measurable (splitCountDifference k : (Fin n → ℝ) → ℝ) := by
  unfold splitCountDifference
  apply Measurable.sub <;> apply Finset.measurable_sum <;> intro i _ <;>
    split_ifs <;> fun_prop

theorem firstSuccessStatistic_no_success {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, x i = 0) : firstSuccessStatistic x = 0 := by
  simp [firstSuccessStatistic, hx]

/-- The displayed polynomial actually selects the earliest success; later
observations have no effect once an earlier observation equals one. -/
theorem firstSuccessStatistic_first {n : ℕ} (x : Fin n → ℝ) (i : Fin n)
    (hi : x i = 1) (hbefore : ∀ j, j < i → x j = 0) :
    firstSuccessStatistic x = (i : ℝ) + 1 := by
  classical
  unfold firstSuccessStatistic
  rw [Finset.sum_eq_single i]
  · rw [hi]
    have hp : (∏ j ∈ Finset.Iio i, (1 - x j)) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      rw [hbefore j (Finset.mem_Iio.mp hj)]
      norm_num
    rw [hp]
    ring
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · rw [hbefore j hlt]
      ring
    · have hp : (∏ a ∈ Finset.Iio j, (1 - x a)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_Iio.mpr hgt)
        rw [hi]
        ring
      rw [hp, mul_zero]
  · simp

/-- The lower generalized-inverse sample median used by the empirical-CDF
convention, including the lower of the two middle observations for even n. -/
def sampleMedian {n : ℕ} [NeZero n] (x : Fin n → ℝ) : ℝ :=
  distributionQuantile (empiricalLaw x) (1 / 2)

theorem sampleMedian_measurable {n : ℕ} [NeZero n] :
    Measurable (sampleMedian : (Fin n → ℝ) → ℝ) :=
  measurable_empirical_quantile (by norm_num)

theorem sampleMedian_order_statistic {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    ∃ k : Fin n, k.val + 1 = Nat.ceil ((n : ℝ) / 2) ∧
      sampleMedian x = (sortedSample x).val k := by
  simpa [sampleMedian, div_eq_mul_inv] using empirical_quantile_ceiling x
    (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)

/-- Drop exactly k observations from each end of the sorted sample. Meaningful
trimming requires 2*k<n; the formula is total even outside that range. Taking
k=floor(n/10) is one explicit integer convention for L2's 10%-trimmed example. -/
def trimmedSampleMean {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ((n - 2 * k : ℕ) : ℝ)⁻¹ *
    ∑ i : Fin n, if k ≤ i.val ∧ i.val + k < n then (sortedSample x).val i else 0

theorem trimmedSampleMean_measurable {n : ℕ} (k : ℕ) :
    Measurable (trimmedSampleMean k : (Fin n → ℝ) → ℝ) := by
  unfold trimmedSampleMean
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  split_ifs
  · exact (measurable_pi_apply i).comp (measurable_subtype_coe.comp sortedSample_measurable)
  · exact measurable_const

/-- The concrete ten-flip dataset printed in L2. -/
def lectureCoinData : Fin 10 → ℝ := ![0, 1, 1, 1, 0, 0, 1, 1, 0, 1]

theorem lectureCoinData_statistics : headCount lectureCoinData = 6 ∧
    firstSuccessStatistic lectureCoinData = 2 ∧ splitCountDifference 6 lectureCoinData = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [headCount, lectureCoinData, Fin.sum_univ_succ]
  · convert! firstSuccessStatistic_first lectureCoinData (1 : Fin 10) (by norm_num [lectureCoinData]) ?_ using 1
    · norm_num
    · intro j hj
      have hj0 : j = 0 := by apply Fin.ext; change j.val = 0; change j.val < 1 at hj; omega
      rw [hj0]
      norm_num [lectureCoinData]
  · norm_num [splitCountDifference, lectureCoinData, Fin.sum_univ_succ]

end LectureNotes
