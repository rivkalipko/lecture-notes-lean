import LectureNotes.LikelihoodRatio

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open Set

def wilsonCenter (n mean z : ℝ) : ℝ := (n * mean + z ^ 2 / 2) / (n + z ^ 2)
def wilsonRadius (n mean z : ℝ) : ℝ :=
  Real.sqrt (z ^ 2 * (n * mean * (1 - mean) + z ^ 2 / 4)) / (n + z ^ 2)
def wilsonInterval (n mean z : ℝ) : Set ℝ :=
  Icc (wilsonCenter n mean z - wilsonRadius n mean z)
    (wilsonCenter n mean z + wilsonRadius n mean z)

theorem wilson_discriminant_nonneg {n m z : ℝ} (hn : 0 ≤ n) (hm : m ∈ Icc (0 : ℝ) 1) :
    0 ≤ z ^ 2 * (n * m * (1 - m) + z ^ 2 / 4) := by
  exact mul_nonneg (sq_nonneg z)
    (add_nonneg (mul_nonneg (mul_nonneg hn hm.1) (sub_nonneg.mpr hm.2)) (by positivity))

/-- Both endpoints of the Bernoulli score confidence interval, obtained by
inverting the quadratic inequality. z is the nonnegative critical magnitude
in applications; the algebra depends only on its square. -/
theorem wilson_interval_inversion (n m z p : ℝ) (hn : 0 < n) (hm : m ∈ Icc (0 : ℝ) 1) :
    n * (m - p) ^ 2 ≤ z ^ 2 * p * (1 - p) ↔ p ∈ wilsonInterval n m z := by
  let A := n + z ^ 2
  let b := n * m + z ^ 2 / 2
  let d := z ^ 2 * (n * m * (1 - m) + z ^ 2 / 4)
  have hA : 0 < A := add_pos_of_pos_of_nonneg hn (sq_nonneg _)
  have hd : 0 ≤ d := wilson_discriminant_nonneg hn.le hm
  have hsq : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd
  have hs0 := Real.sqrt_nonneg d
  have halg : (A * p - b) ^ 2 - d = A * (n * (m - p) ^ 2 - z ^ 2 * p * (1 - p)) := by
    dsimp [A, b, d]
    ring
  have hquad : n * (m - p) ^ 2 ≤ z ^ 2 * p * (1 - p) ↔ (A * p - b) ^ 2 ≤ d := by
    calc
      _ ↔ A * (n * (m - p) ^ 2 - z ^ 2 * p * (1 - p)) ≤ 0 := by
        simp [mul_nonpos_iff, hA.le, not_le_of_gt hA, sub_nonpos]
      _ ↔ _ := by rw [← halg, sub_nonpos]
  have hroot : (A * p - b) ^ 2 ≤ d ↔ -Real.sqrt d ≤ A * p - b ∧ A * p - b ≤ Real.sqrt d := by
    constructor
    · intro h
      constructor <;> nlinarith [sq_nonneg (A * p - b + Real.sqrt d), sq_nonneg (A * p - b - Real.sqrt d)]
    · rintro ⟨hl, hr⟩
      have hp0 : 0 ≤ (Real.sqrt d - (A * p - b)) * ((A * p - b) + Real.sqrt d) :=
        mul_nonneg (sub_nonneg.mpr hr) (by linarith)
      nlinarith
  rw [hquad, hroot]
  change _ ↔ b / A - Real.sqrt d / A ≤ p ∧ p ≤ b / A + Real.sqrt d / A
  rw [← sub_div, ← add_div, div_le_iff₀ hA, le_div_iff₀ hA]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Link the endpoints to the actual Bernoulli score statistic. The open
parameter interval makes its information denominator positive. -/
theorem bernoulli_score_wilson (n m z p : ℝ) (hn : 0 < n)
    (hm : m ∈ Icc (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) 1) :
    (n * m - n * p) ^ 2 / (n * p * (1 - p)) ≤ z ^ 2 ↔ p ∈ wilsonInterval n m z := by
  rw [div_le_iff₀ (mul_pos (mul_pos hn hp.1) (sub_pos.mpr hp.2))]
  rw [← wilson_interval_inversion n m z p hn hm]
  have he : (n * m - n * p) ^ 2 = n * (n * (m - p) ^ 2) := by ring
  have hf : z ^ 2 * (n * p * (1 - p)) = n * (z ^ 2 * p * (1 - p)) := by ring
  rw [he, hf, mul_le_mul_iff_right₀ hn]

end LectureNotes
