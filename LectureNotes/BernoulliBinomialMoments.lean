import LectureNotes.BinomialSample

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

/-- The real-valued Bernoulli law, including the endpoints p=0 and p=1. -/
def bernoulliRealLaw (p : Icc (0 : ℝ) 1) : Measure ℝ := bernoulliMeasure 1 0 p

instance bernoulliRealLaw_probability (p : Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (bernoulliRealLaw p) := inferInstanceAs (IsProbabilityMeasure (bernoulliMeasure 1 0 p))

theorem bernoulliRealLaw_moment (p : Icc (0 : ℝ) 1) {k : ℕ} (hk : 0 < k) :
    (∫ x : ℝ, x ^ k ∂bernoulliRealLaw p) = p := by
  rw [bernoulliRealLaw, integral_bernoulliMeasure]
  simp [hk.ne']

theorem bernoulliRealLaw_memLp_two (p : Icc (0 : ℝ) 1) : MemLp id 2 (bernoulliRealLaw p) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  exact integrable_bernoulliMeasure 1 0 p _

theorem bernoulliRealLaw_mean (p : Icc (0 : ℝ) 1) : (∫ x : ℝ, x ∂bernoulliRealLaw p) = p := by
  simpa using bernoulliRealLaw_moment p (k := 1) (by norm_num)

theorem bernoulliRealLaw_variance (p : Icc (0 : ℝ) 1) :
    Var[id; bernoulliRealLaw p] = (p : ℝ) * (1 - p) := by
  rw [variance_eq_sub (bernoulliRealLaw_memLp_two p)]
  simp only [Pi.pow_apply, id_eq, bernoulliRealLaw_moment p (by norm_num : 0 < 2), bernoulliRealLaw_mean]
  ring

/-- The MGF of the actual finite binomial probability law. -/
theorem binomialCountLaw_mgf (k : ℕ) (p : Icc (0 : ℝ) 1) (t : ℝ) :
    mgf (fun j : Fin (k + 1) => (j : ℝ)) (binomialCountLaw k p) t =
      ((p : ℝ) * Real.exp t + (1 - p)) ^ k := by
  rw [mgf, integral_fintype Integrable.of_finite]
  simp only [measureReal_def, binomialCountLaw_singleton, smul_eq_mul]
  simp_rw [ENNReal.toReal_ofReal (binomialCountMass_nonneg k p _)]
  simp only [binomialCountMass]
  have he (j : ℕ) : (k.choose j : ℝ) * (p : ℝ) ^ j * (1 - (p : ℝ)) ^ (k - j) *
      Real.exp (t * j) = ((p : ℝ) * Real.exp t) ^ j * (1 - (p : ℝ)) ^ (k - j) * (k.choose j : ℝ) := by
    rw [mul_pow, mul_comm t (j : ℝ), Real.exp_nat_mul]
    ring
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (fun j => ((p : ℝ) * Real.exp t) ^ j *
    (1 - (p : ℝ)) ^ (k - j) * (k.choose j : ℝ)) (k + 1)]
  exact (add_pow _ _ _).symm

theorem binomialCountLaw_integrableExpSet (k : ℕ) (p : Icc (0 : ℝ) 1) :
    integrableExpSet (fun j : Fin (k + 1) => (j : ℝ)) (binomialCountLaw k p) = univ := by
  apply Set.eq_univ_of_forall
  intro t
  exact Integrable.of_finite

theorem binomial_mgf_hasDerivAt (k : ℕ) (p : ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (p * Real.exp u + (1 - p)) ^ k)
      ((k : ℝ) * (p * Real.exp t + (1 - p)) ^ (k - 1) * (p * Real.exp t)) t := by
  convert! ((((Real.hasDerivAt_exp t).const_mul p).add_const (1 - p)).pow k) using 1 <;> ring

theorem binomialCountLaw_mean (k : ℕ) (p : Icc (0 : ℝ) 1) :
    (∫ j : Fin (k + 1), (j : ℝ) ∂binomialCountLaw k p) = (k : ℝ) * p := by
  have ht : (0 : ℝ) ∈ interior (integrableExpSet (fun j : Fin (k + 1) => (j : ℝ))
      (binomialCountLaw k p)) := by rw [binomialCountLaw_integrableExpSet]; simp
  rw [← deriv_mgf_zero ht, show mgf (fun j : Fin (k + 1) => (j : ℝ)) (binomialCountLaw k p) =
      (fun t => ((p : ℝ) * Real.exp t + (1 - p)) ^ k) from funext (binomialCountLaw_mgf k p)]
  have hb : (p : ℝ) + (1 - p) = 1 := by ring
  simpa only [Real.exp_zero, mul_one, hb, one_pow] using (binomial_mgf_hasDerivAt k p 0).deriv

theorem binomialCountLaw_second_moment (k : ℕ) (p : Icc (0 : ℝ) 1) :
    (∫ j : Fin (k + 1), (j : ℝ) ^ 2 ∂binomialCountLaw k p) =
      (k : ℝ) * p + (k : ℝ) * (k - 1 : ℕ) * (p : ℝ) ^ 2 := by
  have ht : (0 : ℝ) ∈ interior (integrableExpSet (fun j : Fin (k + 1) => (j : ℝ))
      (binomialCountLaw k p)) := by rw [binomialCountLaw_integrableExpSet]; simp
  have hm := iteratedDeriv_mgf_zero ht 2
  rw [show mgf (fun j : Fin (k + 1) => (j : ℝ)) (binomialCountLaw k p) =
      (fun t => ((p : ℝ) * Real.exp t + (1 - p)) ^ k) from funext (binomialCountLaw_mgf k p)] at hm
  have hd : deriv (fun t : ℝ => ((p : ℝ) * Real.exp t + (1 - p)) ^ k) =
      fun t => (k : ℝ) * ((p : ℝ) * Real.exp t + (1 - p)) ^ (k - 1) * ((p : ℝ) * Real.exp t) :=
    funext (fun t => (binomial_mgf_hasDerivAt k p t).deriv)
  rw [iteratedDeriv_succ (n := 1), iteratedDeriv_one, hd] at hm
  have hb : (p : ℝ) + (1 - p) = 1 := by ring
  have hh := (((binomial_mgf_hasDerivAt (k - 1) p 0).const_mul (k : ℝ)).mul
    ((Real.hasDerivAt_exp 0).const_mul (p : ℝ))).deriv
  simp only [Real.exp_zero, mul_one, hb, one_pow] at hh
  simp only [Pi.pow_apply] at hm
  rw [← hm]
  convert! hh using 1 <;> ring

theorem binomialCountLaw_variance (k : ℕ) (p : Icc (0 : ℝ) 1) :
    Var[fun j : Fin (k + 1) => (j : ℝ); binomialCountLaw k p] =
      (k : ℝ) * p * (1 - p) := by
  rw [variance_eq_sub (show MemLp (fun j : Fin (k + 1) => (j : ℝ)) 2 (binomialCountLaw k p) from
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr Integrable.of_finite)]
  simp only [Pi.pow_apply, binomialCountLaw_second_moment, binomialCountLaw_mean]
  cases k with
  | zero => simp
  | succ n => simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one]; ring

end LectureNotes
