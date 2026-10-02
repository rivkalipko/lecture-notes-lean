import LectureNotes.BinomialTwoSufficiency
import Mathlib.Algebra.Polynomial.Coeff

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Polynomial
open scoped ENNReal

/-- A Binomial(k,p) observation takes values from zero through k. -/
def binomialSampleTotal {k n : ℕ} (x : Fin n → Fin (k + 1)) : ℕ := ∑ i, (x i : ℕ)

def binomialSampleWeight {k n : ℕ} (x : Fin n → Fin (k + 1)) : ℝ :=
  ∏ i, (k.choose (x i) : ℝ)

theorem binomialSampleTotal_le {k n : ℕ} (x : Fin n → Fin (k + 1)) :
    binomialSampleTotal x ≤ k * n := by
  calc
    _ ≤ ∑ _ : Fin n, k := Finset.sum_le_sum (fun i _ => by have h := (x i).isLt; omega)
    _ = _ := by simp [mul_comm]

theorem binomialSampleWeight_pos {k n : ℕ} (x : Fin n → Fin (k + 1)) :
    0 < binomialSampleWeight x :=
  Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (Nat.choose_pos (by have h := (x i).isLt; omega)))

theorem binomial_polynomial_expansion (k : ℕ) :
    (∑ j : Fin (k + 1), C (k.choose j : ℝ) * (X : ℝ[X]) ^ (j : ℕ)) = (1 + X) ^ k := by
  rw [Fin.sum_univ_eq_sum_range (fun j => C (k.choose j : ℝ) * (X : ℝ[X]) ^ j) (k + 1)]
  ext t
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_one_add_X_pow]
  by_cases ht : t < k + 1
  · rw [Finset.sum_eq_single t]
    · simp
    · intro b hb hbt
      simp [hbt, hbt.symm]
    · simp [ht]
  · rw [Finset.sum_eq_zero]
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    · intro b hb
      have hbt : b ≠ t := by have hb' := Finset.mem_range.mp hb; omega
      simp [hbt, hbt.symm]

/-- The generating polynomial of the entire weighted sample. -/
theorem binomial_sample_generating_polynomial (k n : ℕ) :
    (∑ x : Fin n → Fin (k + 1), C (binomialSampleWeight x) * X ^ binomialSampleTotal x) =
      (1 + X : ℝ[X]) ^ (k * n) := by
  have h := Fintype.prod_sum (fun (_ : Fin n) (j : Fin (k + 1)) =>
    C (k.choose j : ℝ) * (X : ℝ[X]) ^ (j : ℕ))
  simp only [binomial_polynomial_expansion, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum] at h
  exact h.symm

/-- Vandermonde's counting identity for a full sample, with impossible totals
represented by a zero binomial coefficient. -/
theorem binomial_sample_fiber_weight (k n t : ℕ) :
    (∑ x : Fin n → Fin (k + 1), if binomialSampleTotal x = t then binomialSampleWeight x else 0) =
      ((k * n).choose t : ℝ) := by
  have h := congrArg (fun q : ℝ[X] => q.coeff t) (binomial_sample_generating_polynomial k n)
  simpa only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    coeff_one_add_X_pow, eq_comm] using h

/-- Selecting one coordinate to equal one replaces that coordinate's
binomial generating polynomial by kX. -/
theorem binomial_one_success_generating_polynomial {k n : ℕ} (i₀ : Fin n) :
    (∑ x : Fin n → Fin (k + 1), if (x i₀ : ℕ) = 1 then
      C (binomialSampleWeight x) * X ^ binomialSampleTotal x else 0) =
      C (k : ℝ) * X * (1 + X : ℝ[X]) ^ (k * (n - 1)) := by
  classical
  let b (j : Fin (k + 1)) : ℝ[X] := C (k.choose j : ℝ) * X ^ (j : ℕ)
  have hsingle : (∑ j : Fin (k + 1), (if (j : ℕ) = 1 then (1 : ℝ[X]) else 0) * b j) = C (k : ℝ) * X := by
    by_cases hk : 0 < k
    · let j₁ : Fin (k + 1) := ⟨1, by omega⟩
      rw [Finset.sum_eq_single j₁]
      · simp [j₁, b]
      · intro j hj hne
        have hj1 : (j : ℕ) ≠ 1 := by intro h; apply hne; exact Fin.ext h
        simp [hj1]
      · simp
    · have hk0 : k = 0 := by omega
      subst k
      simp [b]
  have hi (i : Fin n) :
      (∑ j : Fin (k + 1), (if i = i₀ then (if (j : ℕ) = 1 then (1 : ℝ[X]) else 0) else 1) * b j) =
      if i = i₀ then C (k : ℝ) * X else (1 + X) ^ k := by
    by_cases h : i = i₀
    · simpa only [if_pos h] using hsingle
    · simp only [if_neg h, one_mul, b]
      exact binomial_polynomial_expansion k
  have h := Fintype.prod_sum (fun (i : Fin n) (j : Fin (k + 1)) =>
    (if i = i₀ then (if (j : ℕ) = 1 then (1 : ℝ[X]) else 0) else 1) * b j)
  simp only [hi, Finset.prod_mul_distrib, Fintype.prod_ite_eq'] at h
  have hx (x : Fin n → Fin (k + 1)) :
      (∏ i, b (x i)) = C (binomialSampleWeight x) * X ^ binomialSampleTotal x := by
    simp only [b, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
    rfl
  simp only [hx, ite_mul, one_mul, zero_mul] at h
  rw [← h, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
  simp only [if_pos rfl]
  have he : (∏ i ∈ Finset.univ.erase i₀, if i = i₀ then C (k : ℝ) * X else (1 + X : ℝ[X]) ^ k) =
      ((1 + X : ℝ[X]) ^ k) ^ (n - 1) := by
    have heq : (∏ i ∈ Finset.univ.erase i₀, if i = i₀ then C (k : ℝ) * X else (1 + X : ℝ[X]) ^ k) =
        ∏ _ ∈ Finset.univ.erase i₀, (1 + X : ℝ[X]) ^ k := by
      apply Finset.prod_congr rfl
      intro i hi'
      exact if_neg (Finset.mem_erase.mp hi').1
    rw [heq, Finset.prod_const]
    simp
  rw [he, ← pow_mul]
  simp

/-- The weighted number of samples with a fixed total and one success in a
specified coordinate. The separate zero-total branch prevents natural-number
subtraction from incorrectly treating t=0 as t=1. -/
theorem binomial_one_success_fiber_weight {k n : ℕ} (i₀ : Fin n) (t : ℕ) :
    (∑ x : Fin n → Fin (k + 1), if binomialSampleTotal x = t ∧ (x i₀ : ℕ) = 1 then
      binomialSampleWeight x else 0) =
      if t = 0 then 0 else (k : ℝ) * ((k * (n - 1)).choose (t - 1) : ℝ) := by
  have h := congrArg (fun q : ℝ[X] => q.coeff t) (binomial_one_success_generating_polynomial (k := k) i₀)
  have hs : (∑ x : Fin n → Fin (k + 1), if binomialSampleTotal x = t ∧ (x i₀ : ℕ) = 1 then
      binomialSampleWeight x else 0) =
      (∑ x : Fin n → Fin (k + 1), (if (x i₀ : ℕ) = 1 then
        C (binomialSampleWeight x) * X ^ binomialSampleTotal x else (0 : ℝ[X])).coeff t) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : (x i₀ : ℕ) = 1 <;> by_cases ht : binomialSampleTotal x = t <;>
      simp [hx, ht, coeff_C_mul, coeff_X_pow] <;> aesop
  rw [hs, ← finsetSum_coeff, h]
  cases t with
  | zero => simp
  | succ t => simp [mul_assoc, coeff_C_mul, coeff_X_mul, coeff_one_add_X_pow]

end LectureNotes
