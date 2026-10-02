import LectureNotes.OrderStatistics

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Polynomial

/-- The positive denominator polynomial of a Cauchy sample, evaluated on ℝ. -/
def cauchySampleDenominator {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) : ℝ :=
  ∏ i, ((θ - x i) ^ 2 + 1)

/-- Complex factorization records each observation as the real part of a pair
of roots one unit above and below the real axis. Multiplicities are retained. -/
def cauchySamplePolynomial {n : ℕ} (x : Fin n → ℝ) : ℂ[X] :=
  ∏ i, (X - C ((x i : ℂ) + Complex.I)) * (X - C ((x i : ℂ) - Complex.I))

theorem cauchySampleDenominator_pos {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) :
    0 < cauchySampleDenominator x θ :=
  Finset.prod_pos (fun _ _ => by positivity)

theorem cauchySamplePolynomial_monic {n : ℕ} (x : Fin n → ℝ) :
    (cauchySamplePolynomial x).Monic := by
  simp only [cauchySamplePolynomial, Monic, leadingCoeff_prod, leadingCoeff_mul,
    leadingCoeff_X_sub_C, one_mul, Finset.prod_const_one]

theorem cauchySamplePolynomial_eval_real {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) :
    (cauchySamplePolynomial x).eval (θ : ℂ) = (cauchySampleDenominator x θ : ℂ) := by
  simp only [cauchySamplePolynomial, cauchySampleDenominator, eval_prod,
    eval_mul, eval_sub, eval_X, eval_C, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  push_cast
  calc
    ((θ : ℂ) - ((x i : ℂ) + Complex.I)) * ((θ : ℂ) - ((x i : ℂ) - Complex.I)) =
        ((θ : ℂ) - (x i : ℂ)) ^ 2 - Complex.I ^ 2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

theorem cauchySamplePolynomial_matching_value {n : ℕ} {x y : Fin n → ℝ}
    (h : cauchySamplePolynomial x = cauchySamplePolynomial y) (i : Fin n) :
    ∃ j, x i = y j := by
  have hz : (cauchySamplePolynomial x).eval ((x i : ℂ) + Complex.I) = 0 := by
    simp only [cauchySamplePolynomial, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  rw [h] at hz
  simp only [cauchySamplePolynomial, eval_prod] at hz
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hz
  simp only [eval_mul, eval_sub, eval_X, eval_C] at hj
  refine ⟨j, ?_⟩
  rcases mul_eq_zero.mp hj with hj | hj
  · have hr := congrArg Complex.re (sub_eq_zero.mp hj)
    simpa using hr
  · have hr := congrArg Complex.re (sub_eq_zero.mp hj)
    simpa using hr

/-- Equality of the Cauchy denominator polynomials determines every order
statistic, including repeated sample values. -/
theorem cauchySamplePolynomial_injective_on_sorted {n : ℕ} {x y : Fin n → ℝ}
    (hx : Monotone x) (hy : Monotone y)
    (h : cauchySamplePolynomial x = cauchySamplePolynomial y) : x = y := by
  induction n with
  | zero => exact funext (fun i => Fin.elim0 i)
  | succ n ih =>
    obtain ⟨j, hj⟩ := cauchySamplePolynomial_matching_value h 0
    obtain ⟨i, hi⟩ := cauchySamplePolynomial_matching_value h.symm 0
    have h0 : x 0 = y 0 := le_antisymm
      ((hx (Fin.zero_le i)).trans_eq hi.symm)
      ((hy (Fin.zero_le j)).trans_eq hj.symm)
    have htail : cauchySamplePolynomial (fun i : Fin n => x i.succ) =
        cauchySamplePolynomial (fun i : Fin n => y i.succ) := by
      simp only [cauchySamplePolynomial, Fin.prod_univ_succ] at h
      rw [h0] at h
      exact mul_left_cancel₀
        (((monic_X_sub_C ((y 0 : ℂ) + Complex.I)).mul
          (monic_X_sub_C ((y 0 : ℂ) - Complex.I))).ne_zero) h
    have he := ih (fun _ _ hij => hx (Fin.succ_le_succ_iff.mpr hij))
      (fun _ _ hij => hy (Fin.succ_le_succ_iff.mpr hij)) htail
    funext i
    exact Fin.cases h0 (fun i => congrFun he i) i

/-- Natural-number location contrasts suffice to identify the ordered Cauchy
sample; equality at infinitely many points forces polynomial equality. -/
theorem cauchy_ratios_injective_on_sorted {n : ℕ} {x y : Fin n → ℝ}
    (hx : Monotone x) (hy : Monotone y)
    (h : ∀ k : ℕ, cauchySampleDenominator x 0 / cauchySampleDenominator x k =
      cauchySampleDenominator y 0 / cauchySampleDenominator y k) : x = y := by
  let a : ℂ := cauchySampleDenominator x 0
  let b : ℂ := cauchySampleDenominator y 0
  have hp : C a * cauchySamplePolynomial y = C b * cauchySamplePolynomial x := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Nat.cast_injective : Function.Injective (fun k : ℕ => (k : ℂ)))).mono
    rintro z ⟨k, rfl⟩
    change (C a * cauchySamplePolynomial y).eval (k : ℂ) =
      (C b * cauchySamplePolynomial x).eval (k : ℂ)
    simp only [eval_mul, eval_C]
    have hc := (div_eq_div_iff (cauchySampleDenominator_pos x k).ne'
      (cauchySampleDenominator_pos y k).ne').mp (h k)
    have hcast : (k : ℂ) = ((k : ℝ) : ℂ) := by norm_cast
    rw [hcast, cauchySamplePolynomial_eval_real, cauchySamplePolynomial_eval_real]
    dsimp only [a, b]
    exact_mod_cast hc
  have hab : a = b := by
    have he := congrArg Polynomial.leadingCoeff hp
    simpa only [leadingCoeff_mul, leadingCoeff_C,
      (cauchySamplePolynomial_monic x).leadingCoeff,
      (cauchySamplePolynomial_monic y).leadingCoeff, mul_one] using he
  rw [← hab] at hp
  have ha : C a ≠ (0 : ℂ[X]) := by
    apply C_ne_zero.mpr
    dsimp only [a]
    exact_mod_cast (cauchySampleDenominator_pos x 0).ne'
  exact cauchySamplePolynomial_injective_on_sorted hx hy (mul_left_cancel₀ ha hp).symm

end LectureNotes
