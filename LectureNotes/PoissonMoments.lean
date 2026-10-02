import LectureNotes.Foundations

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

theorem poisson_exponential_series (r : ℝ≥0) (t : ℝ) :
    HasSum (fun n : ℕ => (Real.exp (-r) * (r : ℝ) ^ n / n.factorial) * Real.exp (t * n))
      (Real.exp ((r : ℝ) * (Real.exp t - 1))) := by
  convert! (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * Real.exp t)).mul_left (Real.exp (-r)) using 1
  · funext n
    rw [mul_pow, ← Real.exp_nat_mul, mul_comm t (n : ℝ)]
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring

/-- The Poisson law has all exponential moments, established from its actual mass series. -/
theorem poisson_exponential_integrable (r : ℝ≥0) (t : ℝ) :
    Integrable (fun n : ℕ => Real.exp (t * n)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    (poisson_exponential_series r t).summable

theorem poisson_mgf (r : ℝ≥0) (t : ℝ) :
    mgf (fun n : ℕ => (n : ℝ)) (poissonMeasure r) t =
      Real.exp ((r : ℝ) * (Real.exp t - 1)) := by
  rw [mgf, integral_poissonMeasure]
  simpa only [smul_eq_mul] using (poisson_exponential_series r t).tsum_eq

theorem poisson_integrableExpSet (r : ℝ≥0) :
    integrableExpSet (fun n : ℕ => (n : ℝ)) (poissonMeasure r) = univ := by
  apply Set.eq_univ_of_forall
  exact poisson_exponential_integrable r

theorem poisson_mgf_hasDerivAt (r t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (r * (Real.exp u - 1)))
      (r * Real.exp t * Real.exp (r * (Real.exp t - 1))) t := by
  convert! ((((Real.hasDerivAt_exp t).sub_const 1).const_mul r).exp) using 1 <;> ring

theorem poisson_memLp_two (r : ℝ≥0) : MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) := by
  have ht : (0 : ℝ) ∈ interior (integrableExpSet (fun n : ℕ => (n : ℝ)) (poissonMeasure r)) := by
    rw [poisson_integrableExpSet]; simp
  exact memLp_of_mem_interior_integrableExpSet ht 2

/-- L1: the expectation of the actual Poisson law is its rate. -/
theorem poisson_mean (r : ℝ≥0) : (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  have ht : (0 : ℝ) ∈ interior (integrableExpSet (fun n : ℕ => (n : ℝ)) (poissonMeasure r)) := by
    rw [poisson_integrableExpSet]; simp
  rw [← deriv_mgf_zero ht, show mgf (fun n : ℕ => (n : ℝ)) (poissonMeasure r) =
      (fun t => Real.exp ((r : ℝ) * (Real.exp t - 1))) from funext (poisson_mgf r)]
  simpa using (poisson_mgf_hasDerivAt r 0).deriv

theorem poisson_second_moment (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r) = (r : ℝ) + (r : ℝ) ^ 2 := by
  have ht : (0 : ℝ) ∈ interior (integrableExpSet (fun n : ℕ => (n : ℝ)) (poissonMeasure r)) := by
    rw [poisson_integrableExpSet]; simp
  have hm := iteratedDeriv_mgf_zero ht 2
  rw [show mgf (fun n : ℕ => (n : ℝ)) (poissonMeasure r) =
      (fun t => Real.exp ((r : ℝ) * (Real.exp t - 1))) from funext (poisson_mgf r)] at hm
  have hd : deriv (fun t : ℝ => Real.exp ((r : ℝ) * (Real.exp t - 1))) =
      fun t => (r : ℝ) * Real.exp t * Real.exp ((r : ℝ) * (Real.exp t - 1)) :=
    funext (fun t => (poisson_mgf_hasDerivAt r t).deriv)
  rw [iteratedDeriv_succ (n := 1), iteratedDeriv_one, hd] at hm
  have hh := (((Real.hasDerivAt_exp 0).const_mul (r : ℝ)).mul
    (poisson_mgf_hasDerivAt r 0)).deriv
  simp only [Real.exp_zero, mul_one, sub_self, mul_zero] at hh
  simp only [Pi.pow_apply] at hm
  rw [← hm]
  convert! hh using 1 <;> ring

/-- L1: the Poisson variance equals the same rate. -/
theorem poisson_variance (r : ℝ≥0) : Var[fun n : ℕ => (n : ℝ); poissonMeasure r] = r := by
  rw [variance_eq_sub (poisson_memLp_two r)]
  simp only [Pi.pow_apply, poisson_second_moment, poisson_mean]
  ring

end LectureNotes
