import LectureNotes.GaussianQuadraticForms

/-! L1 chi-square moments and the fourth normal moment used in L5 Example 5. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem standard_normal_second_moment : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
  simpa using h.symm

/-- Differentiate the Gaussian moment-generating function four times at zero. -/
theorem standard_normal_fourth_moment : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  have hE (t : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (x ^ 2 / 2))
      (t * Real.exp (t ^ 2 / 2)) t := by
    convert! (((hasDerivAt_id t).pow 2).div_const 2).exp using 1
    simp only [id_eq, Pi.pow_apply]
    ring
  have h1 : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
      fun t => t * Real.exp (t ^ 2 / 2) := funext (fun t => (hE t).deriv)
  have h2 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
    funext t
    convert! ((hasDerivAt_id t).mul (hE t)).deriv using 1
    simp only [id_eq]
    ring
  have h3 : deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
    funext t
    convert! (((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2)).mul (hE t)).deriv
      using 1
    simp only [id_eq, Pi.add_apply, Pi.pow_apply]
    ring
  have h4 : deriv (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) 0 = 3 := by
    convert! ((((hasDerivAt_id (0 : ℝ)).const_mul 3).add
      ((hasDerivAt_id (0 : ℝ)).pow 3)).mul (hE 0)).deriv using 1
    norm_num
  have hm := iteratedDeriv_mgf_zero
    (X := id) (μ := gaussianReal 0 1) (by simp) 4
  change iteratedDeriv 4 (mgf id (gaussianReal 0 1)) 0 =
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) at hm
  rw [← hm, mgf_id_gaussianReal]
  simp only [zero_mul, NNReal.coe_one, one_mul, zero_add]
  rw [iteratedDeriv_succ (n := 3), iteratedDeriv_succ (n := 2),
    iteratedDeriv_succ (n := 1), iteratedDeriv_one, h1, h2, h3, h4]

theorem normal_square_memLp (μ : ℝ) (v : ℝ≥0) :
    MemLp (fun x : ℝ => x ^ 2) 2 (gaussianReal μ v) := by
  have h : MemLp id (4 : ENNReal) (gaussianReal μ v) := memLp_id_gaussianReal 4
  have : ENNReal.HolderTriple 4 4 2 := by
    rw [ENNReal.holderTriple_iff]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]
  have hprod : MemLp (fun x : ℝ => id x * id x) 2 (gaussianReal μ v) := h.mul' h
  simpa [sq] using hprod

theorem standard_normal_square_variance :
    Var[fun x : ℝ => x ^ 2; gaussianReal 0 1] = 2 := by
  rw [variance_eq_sub (normal_square_memLp 0 1), standard_normal_second_moment]
  simp only [Pi.pow_apply]
  have h : (fun x : ℝ => (x ^ 2) ^ 2) = fun x => x ^ 4 := by funext x; ring
  rw [h, standard_normal_fourth_moment]
  norm_num

theorem chiSquared_mean (n : ℕ) : ∫ x, x ∂chiSquared n = n := by
  rw [chiSquared, integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  rw [integral_finsetSum]
  · have h (i : Fin n) :
        (∫ z : Fin n → ℝ, z i ^ 2 ∂Measure.pi (fun _ => gaussianReal 0 1)) = 1 := by
      rw [integral_comp_eval (μ := fun _ : Fin n => gaussianReal 0 1) (i := i)
        (f := fun x : ℝ => x ^ 2) (by fun_prop), standard_normal_second_moment]
    simp [h]
  · intro i _
    exact ((normal_square_memLp 0 1).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)).integrable (by norm_num)

theorem chiSquared_memLp (n : ℕ) : MemLp id 2 (chiSquared n) := by
  rw [chiSquared]
  apply (memLp_map_measure_iff (by fun_prop) (Measurable.aemeasurable (by fun_prop))).mpr
  have h (i : Fin n) := (normal_square_memLp 0 1).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)
  simpa only [Function.comp_def, id_eq] using memLp_finsetSum _ (fun i _ => h i)

theorem chiSquared_variance (n : ℕ) : Var[id; chiSquared n] = 2 * n := by
  rw [chiSquared, variance_map (by fun_prop) (Measurable.aemeasurable (by fun_prop))]
  change Var[fun z : Fin n → ℝ => ∑ i, z i ^ 2; Measure.pi fun _ => gaussianReal 0 1] = _
  have h := variance_sum_pi (μ := fun _ : Fin n => gaussianReal 0 1)
    (X := fun _ x => x ^ 2) (fun _ => normal_square_memLp 0 1)
  convert! h using 1
  · congr 1
    ext z
    simp
  · simp [standard_normal_square_variance, mul_comm]

theorem chiSquared_second_moment (n : ℕ) :
    ∫ x : ℝ, x ^ 2 ∂chiSquared n = (n : ℝ) * (n + 2) := by
  have h := variance_eq_sub (chiSquared_memLp n)
  simp only [chiSquared_variance, Pi.pow_apply, id_eq, chiSquared_mean] at h
  nlinarith

end LectureNotes
