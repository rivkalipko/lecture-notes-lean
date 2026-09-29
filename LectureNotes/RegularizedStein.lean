import LectureNotes.GaussianStein

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

def normalSquareNorm {p : ℕ} (y : Fin p → ℝ) : ℝ := ∑ i, y i ^ 2

def regularizedSteinCorrection {p : ℕ} (a ε : ℝ) (y : Fin p → ℝ) (i : Fin p) : ℝ :=
  -a * y i / (normalSquareNorm y + ε)

def regularizedSteinDerivative {p : ℕ} (a ε : ℝ) (y : Fin p → ℝ) (i : Fin p) : ℝ :=
  -a * (normalSquareNorm y + ε - 2 * y i ^ 2) / (normalSquareNorm y + ε) ^ 2

theorem normalSquareNorm_nonneg {p : ℕ} (y : Fin p → ℝ) : 0 ≤ normalSquareNorm y :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem coordinate_sq_le_normalSquareNorm {p : ℕ} (y : Fin p → ℝ) (i : Fin p) :
    y i ^ 2 ≤ normalSquareNorm y :=
  Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)

theorem normalSquareNorm_insertNth {n : ℕ} (i : Fin (n + 1)) (x : ℝ) (z : Fin n → ℝ) :
    normalSquareNorm (i.insertNth x z) = x ^ 2 + normalSquareNorm z := by
  unfold normalSquareNorm
  rw [i.sum_univ_succAbove]
  simp

theorem regularizedSteinCorrection_measurable {p : ℕ} (a ε : ℝ) :
    Measurable (regularizedSteinCorrection (p := p) a ε) := by
  unfold regularizedSteinCorrection normalSquareNorm
  fun_prop

theorem regularizedSteinDerivative_measurable {p : ℕ} (a ε : ℝ) :
    Measurable (regularizedSteinDerivative (p := p) a ε) := by
  unfold regularizedSteinDerivative normalSquareNorm
  fun_prop

theorem regularizedSteinCorrection_hasDerivAt {n : ℕ} (a ε : ℝ) (hε : 0 < ε)
    (i : Fin (n + 1)) (z : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (fun t => regularizedSteinCorrection a ε (i.insertNth t z) i)
      (regularizedSteinDerivative a ε (i.insertNth x z) i) x := by
  have hden : x ^ 2 + normalSquareNorm z + ε ≠ 0 := by
    have := normalSquareNorm_nonneg z
    positivity
  simp only [regularizedSteinCorrection, regularizedSteinDerivative,
    normalSquareNorm_insertNth, Fin.insertNth_apply_same]
  have h := ((hasDerivAt_id x).const_mul (-a)).div
    ((((hasDerivAt_id x).pow 2).add_const (normalSquareNorm z)).add_const ε) hden
  convert! h using 1
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

theorem regularizedSteinCorrection_bound {p : ℕ} (a ε : ℝ) (hε : 0 < ε)
    (y : Fin p → ℝ) (i : Fin p) :
    |regularizedSteinCorrection a ε y i| ≤ |a| * (1 + 1 / ε) := by
  have hS := normalSquareNorm_nonneg y
  have ht := coordinate_sq_le_normalSquareNorm y i
  have hden : 0 < normalSquareNorm y + ε := by positivity
  have hsmall : |y i| ≤ normalSquareNorm y + 1 := by
    nlinarith [sq_nonneg (|y i| - 1), sq_abs (y i)]
  have hrat : |y i| / (normalSquareNorm y + ε) ≤ 1 + 1 / ε := by
    rw [div_le_iff₀ hden]
    have hinv : ε * (1 / ε) = 1 := by field_simp
    have hnonneg : 0 ≤ normalSquareNorm y * (1 / ε) := by positivity
    nlinarith
  unfold regularizedSteinCorrection
  rw [abs_div, abs_mul, abs_neg, abs_of_pos hden, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hrat (abs_nonneg a)

theorem regularizedSteinDerivative_bound {p : ℕ} (a ε : ℝ) (hε : 0 < ε)
    (y : Fin p → ℝ) (i : Fin p) :
    |regularizedSteinDerivative a ε y i| ≤ 3 * |a| / ε := by
  have hS := normalSquareNorm_nonneg y
  have ht := coordinate_sq_le_normalSquareNorm y i
  have hden : 0 < normalSquareNorm y + ε := by positivity
  have hnum : |normalSquareNorm y + ε - 2 * y i ^ 2| ≤ 3 * (normalSquareNorm y + ε) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (y i)]
  unfold regularizedSteinDerivative
  rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (normalSquareNorm y + ε))]
  calc
    |a| * |normalSquareNorm y + ε - 2 * y i ^ 2| / (normalSquareNorm y + ε) ^ 2 ≤
        |a| * (3 * (normalSquareNorm y + ε)) / (normalSquareNorm y + ε) ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (abs_nonneg _)) (sq_nonneg _)
    _ = 3 * |a| / (normalSquareNorm y + ε) := by field_simp
    _ ≤ 3 * |a| / ε := div_le_div_of_nonneg_left (by positivity) hε (by linarith)

/-- The finite-dimensional algebra in Stein's unbiased risk formula. -/
theorem regularizedStein_risk_integrand {p : ℕ} (a ε v : ℝ) (y : Fin p → ℝ) :
    (∑ i, (regularizedSteinCorrection a ε y i ^ 2 +
      2 * v * regularizedSteinDerivative a ε y i)) =
    (a ^ 2 - 2 * a * v * ((p : ℝ) - 2)) * normalSquareNorm y / (normalSquareNorm y + ε) ^ 2 -
      2 * a * p * v * ε / (normalSquareNorm y + ε) ^ 2 := by
  have he i : regularizedSteinCorrection a ε y i ^ 2 +
      2 * v * regularizedSteinDerivative a ε y i =
      ((a ^ 2 + 4 * a * v) * y i ^ 2 - 2 * a * v * (normalSquareNorm y + ε)) /
        (normalSquareNorm y + ε) ^ 2 := by
    unfold regularizedSteinCorrection regularizedSteinDerivative
    simp only [div_pow, mul_pow, neg_sq]
    ring
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold normalSquareNorm
  ring

end LectureNotes
