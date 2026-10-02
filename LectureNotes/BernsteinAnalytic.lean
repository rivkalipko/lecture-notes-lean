import LectureNotes.Concentration

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped Topology ENNReal NNReal

/-- The factorial estimate responsible for Bernstein's range constant 1/3. -/
theorem bernstein_factorial_bound (k : ℕ) :
    (2 : ℝ) * 3 ^ k ≤ (k + 2).factorial := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, pow_succ]
    have hk : (3 : ℝ) ≤ (k + 2 : ℕ) + 1 := by
      exact_mod_cast (show 3 ≤ k + 2 + 1 by omega)
    nlinarith [mul_le_mul_of_nonneg_right hk (by positivity : (0 : ℝ) ≤ (k + 2).factorial)]

/-- A variance-sensitive quadratic exponential majorant, proved by bounding
the actual exponential series with a geometric series. -/
theorem bernstein_exp_bound {y M : ℝ} (hM : 0 ≤ M) (hM3 : M < 3) (hy : |y| ≤ M) :
    exp y ≤ 1 + y + y ^ 2 / (2 * (1 - M / 3)) := by
  have hexp : HasSum (fun k : ℕ => y ^ k / k.factorial) (exp y) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp y
  have htail : HasSum (fun k : ℕ => y ^ (k + 2) / (k + 2).factorial) (exp y - (1 + y)) := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, zero_add, pow_one, Nat.factorial_one] using (hasSum_nat_add_iff' 2).mpr hexp
  have hgeo := (hasSum_geometric_of_lt_one (div_nonneg hM (by norm_num))
    (show M / 3 < 1 by linarith)).mul_left (y ^ 2 / 2)
  have hb (k : ℕ) : y ^ (k + 2) / (k + 2).factorial ≤ (y ^ 2 / 2) * (M / 3) ^ k := by
    have hf : (0 : ℝ) < (k + 2).factorial := by positivity
    calc
      _ ≤ |y| ^ (k + 2) / (k + 2).factorial := by
        exact div_le_div_of_nonneg_right (by simpa only [abs_pow] using le_abs_self (y ^ (k + 2))) hf.le
      _ = y ^ 2 * |y| ^ k / (k + 2).factorial := by rw [pow_add, sq_abs]; ring
      _ ≤ y ^ 2 * M ^ k / (k + 2).factorial := by gcongr
      _ ≤ y ^ 2 * M ^ k / (2 * 3 ^ k) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (bernstein_factorial_bound k)
      _ = _ := by rw [div_pow]; ring
  have hh := hasSum_le hb htail hgeo
  have he : y ^ 2 / 2 * (1 - M / 3)⁻¹ = y ^ 2 / (2 * (1 - M / 3)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at hh
  linarith

/-- The MGF bound uses the actual variance of a centered bounded observation. -/
theorem bernstein_mgf_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : MemLp X 2 P) {M t : ℝ} (hM : 0 ≤ M)
    (hb : ∀ᵐ ω ∂P, |X ω| ≤ M) (hm : P[X] = 0) (ht : 0 ≤ t) (htM : t * M < 3) :
    mgf X P t ≤ exp (t ^ 2 * Var[X; P] / (2 * (1 - t * M / 3))) := by
  have hi := hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hexp := integrable_exp_mul_of_le t M ht hX.aemeasurable
    (hb.mono (fun ω hω => (le_abs_self _).trans hω))
  let c := t ^ 2 / (2 * (1 - t * M / 3))
  have hb' : ∀ᵐ ω ∂P, exp (t * X ω) ≤ 1 + t * X ω + c * X ω ^ 2 := by
    filter_upwards [hb] with ω hω
    have hh := bernstein_exp_bound (mul_nonneg ht hM) htM
      (show |t * X ω| ≤ t * M by rw [abs_mul, abs_of_nonneg ht]; gcongr)
    convert! hh using 1
    dsimp [c]
    ring
  have hpI : Integrable (fun ω => 1 + t * X ω + c * X ω ^ 2) P :=
    ((integrable_const 1).add (hi.const_mul t)).add (hX.integrable_sq.const_mul c)
  have hh := integral_mono_ae hexp hpI hb'
  have hlin : Integrable (fun ω => 1 + t * X ω) P := (integrable_const 1).add (hi.const_mul t)
  rw [integral_add (f := fun ω => 1 + t * X ω) (g := fun ω => c * X ω ^ 2) hlin (hX.integrable_sq.const_mul c),
    integral_add (f := fun _ => (1 : ℝ)) (g := fun ω => t * X ω) (integrable_const 1) (hi.const_mul t), integral_const_mul, integral_const_mul,
    integral_const, hm] at hh
  rw [variance_of_integral_eq_zero hX.aemeasurable hm]
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero] at hh
  have he : c * (∫ ω, X ω ^ 2 ∂P) = t ^ 2 * (∫ ω, X ω ^ 2 ∂P) / (2 * (1 - t * M / 3)) := by
    dsimp [c]
    ring
  rw [he] at hh
  exact hh.trans (by linarith [add_one_le_exp (t ^ 2 * (∫ ω, X ω ^ 2 ∂P) / (2 * (1 - t * M / 3)))])

end LectureNotes
