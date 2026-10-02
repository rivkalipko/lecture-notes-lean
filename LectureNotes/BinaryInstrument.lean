import LectureNotes.InstrumentalVariables

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

/-- Indices in one of the two observed instrument groups. -/
def instrumentGroup {n : ℕ} (z : Fin n → Bool) (b : Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => z i = b)

/-- The within-group sample average. Statements comparing both averages
require both groups to contain observations. -/
def instrumentGroupMean {n : ℕ} (z : Fin n → Bool) (b : Bool) (y : Fin n → ℝ) : ℝ :=
  (∑ i ∈ instrumentGroup z b, y i) / (instrumentGroup z b).card

theorem instrumentGroup_partition {n : ℕ} (z : Fin n → Bool) :
    (instrumentGroup z true).card + (instrumentGroup z false).card = n := by
  have he : (instrumentGroup z false) = Finset.univ.filter (fun i => ¬ z i = true) := by
    ext i
    simp only [instrumentGroup, Finset.mem_filter, Finset.mem_univ, true_and]
    cases z i <;> simp
  rw [he]
  exact (Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun i => z i = true)).trans
    (Fintype.card_fin n)

theorem instrumentGroup_sum {n : ℕ} (z : Fin n → Bool) (y : Fin n → ℝ) :
    (∑ i ∈ instrumentGroup z true, y i) + (∑ i ∈ instrumentGroup z false, y i) = ∑ i, y i := by
  have he : (instrumentGroup z false) = Finset.univ.filter (fun i => ¬ z i = true) := by
    ext i
    simp only [instrumentGroup, Finset.mem_filter, Finset.mem_univ, true_and]
    cases z i <;> simp
  rw [he]
  exact Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => z i = true) y

/-- Binary-instrument covariance equals the difference of the two group
means times the product of their empirical proportions. -/
theorem sampleCovariance_binary {n : ℕ} (z : Fin n → Bool) (y : Fin n → ℝ)
    (h1 : 0 < (instrumentGroup z true).card) (h0 : 0 < (instrumentGroup z false).card) :
    sampleCovariance (fun i => if z i = true then 1 else 0) y =
      ((instrumentGroup z true).card / (n : ℝ)) *
        ((instrumentGroup z false).card / (n : ℝ)) *
        (instrumentGroupMean z true y - instrumentGroupMean z false y) := by
  have hc := instrumentGroup_partition z
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc1 : ((instrumentGroup z true).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h1.ne'
  have hc0 : ((instrumentGroup z false).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0.ne'
  have hsum := instrumentGroup_sum z y
  have hsumz : (∑ i, (if z i = true then (1 : ℝ) else 0)) = (instrumentGroup z true).card := by
    simp [instrumentGroup, ← Finset.sum_filter]
  have hsumzy : (∑ i, (if z i = true then (1 : ℝ) else 0) * y i) =
      ∑ i ∈ instrumentGroup z true, y i := by
    simp only [ite_mul, one_mul, zero_mul, instrumentGroup, Finset.sum_filter]
  have hcR : ((instrumentGroup z true).card : ℝ) + (instrumentGroup z false).card = n := by
    exact_mod_cast hc
  unfold sampleCovariance sampleMean instrumentGroupMean
  simp only [Fintype.card_fin]
  rw [hsumz, hsumzy, ← hsum]
  field_simp
  rw [← hcR]
  ring

/-- L6 Example 3: the binary IV estimator is exactly the ratio of the
outcome and treatment differences in means. Both groups are nonempty. -/
theorem instrumental_variables_binary_ratio {n : ℕ}
    (z : Fin n → Bool) (y d : Fin n → ℝ)
    (h1 : 0 < (instrumentGroup z true).card) (h0 : 0 < (instrumentGroup z false).card) :
    sampleCovariance (fun i => if z i = true then 1 else 0) y /
        sampleCovariance (fun i => if z i = true then 1 else 0) d =
      (instrumentGroupMean z true y - instrumentGroupMean z false y) /
        (instrumentGroupMean z true d - instrumentGroupMean z false d) := by
  rw [sampleCovariance_binary z y h1 h0, sampleCovariance_binary z d h1 h0]
  have hc := instrumentGroup_partition z
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc1 : ((instrumentGroup z true).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h1.ne'
  have hc0 : ((instrumentGroup z false).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0.ne'
  exact mul_div_mul_left _ _ (mul_ne_zero (div_ne_zero hc1 hn) (div_ne_zero hc0 hn))

/-- The first stage is nonzero precisely when the treatment group means differ. -/
theorem instrumental_variables_binary_relevance {n : ℕ}
    (z : Fin n → Bool) (d : Fin n → ℝ)
    (h1 : 0 < (instrumentGroup z true).card) (h0 : 0 < (instrumentGroup z false).card) :
    sampleCovariance (fun i => if z i = true then 1 else 0) d ≠ 0 ↔
      instrumentGroupMean z true d ≠ instrumentGroupMean z false d := by
  rw [sampleCovariance_binary z d h1 h0]
  have hc := instrumentGroup_partition z
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc1 : ((instrumentGroup z true).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h1.ne'
  have hc0 : ((instrumentGroup z false).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0.ne'
  simp only [ne_eq, mul_eq_zero, div_eq_zero_iff, hc1, hc0, hn, false_or, sub_eq_zero]

end LectureNotes
