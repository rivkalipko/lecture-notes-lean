import LectureNotes.Foundations

namespace LectureNotes

open Finset

/-! Deterministic identities behind the sample-mean and sample-variance proofs. -/

noncomputable def sampleMean {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, x i

theorem sum_centered_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) (m : ℝ)
    (hm : ∑ i, x i = (Fintype.card ι : ℝ) * m) :
    ∑ i, (x i - m) ^ 2 = ∑ i, x i ^ 2 - (Fintype.card ι : ℝ) * m ^ 2 := by
  classical
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hmul : (∑ i, 2 * x i * m) = 2 * m * (∑ i, x i) := by
    calc
      (∑ i, 2 * x i * m) = ∑ i, (2 * m) * x i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 2 * m * (∑ i, x i) := by rw [Finset.mul_sum]
  rw [hmul, hm]
  simp only [Finset.card_univ]
  ring

theorem sum_centered_sq_sampleMean {ι : Type*} [Fintype ι]
    [Nonempty ι] (x : ι → ℝ) :
    ∑ i, (x i - sampleMean x) ^ 2 =
      ∑ i, x i ^ 2 - (Fintype.card ι : ℝ) * (sampleMean x) ^ 2 := by
  classical
  apply sum_centered_sq x (sampleMean x)
  simp [sampleMean, Finset.mul_sum]

theorem sampleMean_eq_iff {ι : Type*} [Fintype ι] (x : ι → ℝ) (m : ℝ)
    (hcard : (Fintype.card ι : ℝ) ≠ 0) :
    sampleMean x = m ↔ ∑ i, x i = (Fintype.card ι : ℝ) * m := by
  unfold sampleMean
  constructor
  · intro h
    calc
      ∑ i, x i = (Fintype.card ι : ℝ) *
          ((Fintype.card ι : ℝ)⁻¹ * ∑ i, x i) := by field_simp [hcard]
      _ = (Fintype.card ι : ℝ) * m := by rw [h]
  · intro h
    rw [h]
    field_simp [hcard]

/-! The algebraic form of the unbiased-sample-variance calculation. -/

theorem sample_variance_identity {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (m : ℝ) (hm : ∑ i, x i = (Fintype.card ι : ℝ) * m)
    (hcard : (Fintype.card ι : ℝ) ≠ 0) :
    (∑ i, (x i - m) ^ 2) / (Fintype.card ι : ℝ) =
      (∑ i, x i ^ 2) / (Fintype.card ι : ℝ) - m ^ 2 := by
  rw [sum_centered_sq x m hm]
  field_simp

end LectureNotes
