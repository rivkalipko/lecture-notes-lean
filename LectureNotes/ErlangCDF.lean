import LectureNotes.GammaConjugacy
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

def erlangTailPolynomial (k : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), x ^ i / (i.factorial : ℝ)

theorem erlang_cdf_primitive_derivative (k : ℕ) (x : ℝ) :
    HasDerivAt (fun t => 1 - Real.exp (-t) * erlangTailPolynomial k t)
      (Real.exp (-x) * x ^ k / (k.factorial : ℝ)) x := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
    simpa only [Pi.neg_apply, id_eq, mul_neg, mul_one] using! (hasDerivAt_id x).neg.exp
  induction k with
  | zero =>
    simpa [erlangTailPolynomial] using! (hasDerivAt_const x 1).sub hexp
  | succ k ih =>
    have he : (fun t => 1 - Real.exp (-t) * erlangTailPolynomial (k + 1) t) =
        (fun t => (1 - Real.exp (-t) * erlangTailPolynomial k t) -
          Real.exp (-t) * (t ^ (k + 1) / ((k + 1).factorial : ℝ))) := by
      funext t
      simp only [erlangTailPolynomial, Finset.sum_range_succ]
      ring
    rw [he]
    have hnew := hexp.mul (((hasDerivAt_id x).pow (k + 1)).div_const ((k + 1).factorial : ℝ))
    convert! ih.sub hnew using 1
    simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem erlangTailPolynomial_zero (k : ℕ) : erlangTailPolynomial k 0 = 1 := by
  unfold erlangTailPolynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    simp [zero_pow hb]
  · simp

/-- Exact Erlang CDF, derived from the actual Gamma density by the fundamental
theorem of calculus. Mathlib uses shape and rate. -/
theorem gamma_nat_cdf (k : ℕ) {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    cdf (gammaMeasure ((k : ℝ) + 1) r) x =
      1 - Real.exp (-(r * x)) * erlangTailPolynomial k (r * x) := by
  rw [cdf_gammaMeasure_eq_integral (by positivity) hr]
  let G (t : ℝ) := r ^ (k + 1) / (k.factorial : ℝ) * t ^ k * Real.exp (-(r * t))
  have hpdf : gammaPDFReal ((k : ℝ) + 1) r = (Ici (0 : ℝ)).indicator G := by
    funext t
    unfold gammaPDFReal
    rw [Real.Gamma_nat_eq_factorial]
    have hp : r ^ ((k : ℝ) + 1) = r ^ (k + 1) := by
      rw [← Nat.cast_add_one, Real.rpow_natCast]
    rw [hp, show (k : ℝ) + 1 - 1 = k by ring, Real.rpow_natCast]
    by_cases ht : 0 ≤ t <;> simp [ht, G]
  rw [hpdf, setIntegral_indicator measurableSet_Ici]
  have hi : Iic x ∩ Ici (0 : ℝ) = Icc 0 x := by ext t; simp [and_comm]
  rw [hi, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hd (t : ℝ) : HasDerivAt
      (fun u => 1 - Real.exp (-(r * u)) * erlangTailPolynomial k (r * u)) (G t) t := by
    have hh := (erlang_cdf_primitive_derivative k (r * t)).comp t
      ((hasDerivAt_id t).const_mul r)
    convert! hh using 1
    dsimp only [G, id_eq]
    rw [mul_pow, pow_succ]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hG.intervalIntegrable 0 x)]
  simp [erlangTailPolynomial_zero]

/-- A certified interval for the Gamma(50, rate 1/2) lower-tail probability at
90. The final link to the actual chi-square law is stated separately. -/
theorem gamma_fifty_half_cdf_ninety_bounds :
    (246 : ℝ) / 1000 < cdf (gammaMeasure 50 (1 / 2)) 90 ∧
      cdf (gammaMeasure 50 (1 / 2)) 90 < (247 : ℝ) / 1000 := by
  let S := erlangTailPolynomial 49 45
  have hS : S =
      (26113678275484720007276619720165301129845067731822508726969168447 : ℝ) /
        992446776068150297004182678682165314408415232 := by
    norm_num [S, erlangTailPolynomial, Finset.sum_range_succ]
  have hSpos : 0 < S := by rw [hS]; positivity
  have hc : cdf (gammaMeasure 50 (1 / 2)) 90 = 1 - S / Real.exp 45 := by
    have hh := gamma_nat_cdf 49 (r := 1 / 2) (x := 90) (by norm_num) (by norm_num)
    norm_num only [Nat.cast_ofNat, show (49 : ℝ) + 1 = 50 by norm_num,
      show (1 / 2 : ℝ) * 90 = 45 by norm_num] at hh
    rw [Real.exp_neg] at hh
    simpa only [S, div_eq_mul_inv, mul_comm] using hh
  have he : Real.exp 45 = (Real.exp 1) ^ 45 := by
    simpa using Real.exp_nat_mul (1 : ℝ) 45
  have hlo : (2.7182818283 : ℝ) ^ 45 ≤ Real.exp 45 := by
    rw [he]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le _
  have hhi : Real.exp 45 ≤ (2.7182818286 : ℝ) ^ 45 := by
    rw [he]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le _
  have hlower : (246 : ℝ) / 1000 < 1 - S / (2.7182818283 : ℝ) ^ 45 := by
    rw [hS]
    norm_num
  have hupper : 1 - S / (2.7182818286 : ℝ) ^ 45 < (247 : ℝ) / 1000 := by
    rw [hS]
    norm_num
  have hratioLo := div_le_div_of_nonneg_left hSpos.le (by positivity : 0 < (2.7182818283 : ℝ) ^ 45) hlo
  have hratioHi := div_le_div_of_nonneg_left hSpos.le (Real.exp_pos 45) hhi
  rw [hc]
  constructor <;> linarith

end LectureNotes
