import LectureNotes.JamesStein

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

theorem jamesStein_loss_zero {p : ℕ} (v : ℝ) (y : Fin p → ℝ)
    (hy : normalSquareNorm y ≠ 0) :
    (∑ i, jamesStein v y i ^ 2) = normalSquareNorm y - 2 * ((p : ℝ) - 2) * v +
      (((p : ℝ) - 2) * v) ^ 2 * (1 / normalSquareNorm y) := by
  unfold jamesStein
  simp only [mul_pow, ← Finset.mul_sum]
  change (1 - ((p : ℝ) - 2) * v / normalSquareNorm y) ^ 2 * normalSquareNorm y = _
  field_simp
  <;> ring

/-- The inverse-radius expectation in the centered normal model. The proof
uses the established Stein risk identity; it does not assume a χ² moment. -/
theorem centered_normal_inverse_square {p : ℕ} (hp : 3 ≤ p) (v : ℝ≥0) (hv : 0 < v) :
    (∫ y : Fin p → ℝ, 1 / normalSquareNorm y ∂Measure.pi (fun _ => gaussianReal 0 v)) =
      1 / (((p : ℝ) - 2) * v) := by
  cases p with
  | zero => omega
  | succ n =>
    let P := Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 v)
    let a : ℝ := (((n + 1 : ℕ) : ℝ) - 2) * v
    have ha : 0 < a := by
      have hdim : (2 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast hp
      exact mul_pos (sub_pos.mpr hdim) (by exact_mod_cast hv)
    have hi := normal_inverse_square_integrable (fun _ => 0) v hv hp
    have hY i : HasLaw (fun y : Fin (n + 1) → ℝ => y i) (gaussianReal 0 v) P :=
      ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
    have hS : Integrable (normalSquareNorm (p := n + 1)) P := by
      apply integrable_finsetSum
      intro i _
      exact (((hY i).identDistrib HasLaw.id).memLp_iff.mpr (memLp_id_gaussianReal 2)).integrable_sq
    have hm : (∫ y, normalSquareNorm y ∂P) = (n + 1 : ℕ) * (v : ℝ) := by
      simpa only [sub_zero, normalSquareNorm] using normal_means_identity_risk hY
    have he : (∫ y, ∑ i, jamesStein v y i ^ 2 ∂P) =
        (∫ y, normalSquareNorm y - 2 * a + a ^ 2 * (1 / normalSquareNorm y) ∂P) := by
      apply integral_congr_ae
      filter_upwards [normalSquareNorm_pos_ae (fun _ => 0) v hv.ne'] with y hy
      simpa only [a, mul_assoc] using jamesStein_loss_zero v y hy.ne'
    have hsint : Integrable (fun y => normalSquareNorm y - 2 * a) P := by
      simpa only [Pi.sub_apply] using! hS.sub (integrable_const (2 * a))
    rw [integral_add hsint (hi.const_mul (a ^ 2)),
      integral_sub hS (integrable_const (2 * a)), integral_const, integral_const_mul, hm] at he
    simp only [probReal_univ, one_smul] at he
    have hr := jamesStein_risk (fun _ : Fin (n + 1) => 0) v hv hp
    simp only [sub_zero] at hr
    have hmul : a * (a * (∫ y, 1 / normalSquareNorm y ∂P)) = a * 1 := by
      dsimp [P, a] at he ⊢
      nlinarith
    have hcancel := mul_left_cancel₀ ha.ne' hmul
    apply (eq_div_iff ha.ne').mpr
    simpa only [mul_comm] using hcancel

/-- L13's empirical-Bayes calculation: under marginal variance w, the
James–Stein correction estimates the Bayesian noise fraction σ²/w. -/
theorem empirical_bayes_shrinkage_unbiased {p : ℕ} (hp : 3 ≤ p)
    (noise priorVariance : ℝ≥0) (hnoise : 0 < noise) :
    (∫ y : Fin p → ℝ, ((p : ℝ) - 2) * noise / normalSquareNorm y
      ∂Measure.pi (fun _ => gaussianReal 0 (noise + priorVariance))) =
      (noise : ℝ) / (noise + priorVariance) := by
  have hw : 0 < noise + priorVariance := add_pos_of_pos_of_nonneg hnoise priorVariance.coe_nonneg
  have he (y : Fin p → ℝ) : ((p : ℝ) - 2) * noise / normalSquareNorm y =
      (((p : ℝ) - 2) * noise) * (1 / normalSquareNorm y) := by ring
  simp_rw [he, integral_const_mul, centered_normal_inverse_square hp (noise + priorVariance) hw]
  have hp' : ((p : ℝ) - 2) ≠ 0 := by
    have h : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  simp only [NNReal.coe_add]
  field_simp

end LectureNotes
