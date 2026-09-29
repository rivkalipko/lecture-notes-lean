import LectureNotes.EstimationTheory

set_option autoImplicit false

/-! L7 logistic example: normalized Bernoulli probabilities, the actual
log-likelihood derivative, and the negative curvature calculation. -/
noncomputable section
namespace LectureNotes
open Set

def logistic (t : ℝ) : ℝ := Real.exp t / (1 + Real.exp t)

theorem logistic_mem_Ioo (t : ℝ) : logistic t ∈ Ioo (0 : ℝ) 1 := by
  have he := Real.exp_pos t
  constructor
  · exact div_pos he (by positivity)
  · exact (div_lt_one (by positivity : 0 < 1 + Real.exp t)).mpr (by linarith)

def logisticMass (y : Bool) (t : ℝ) : ℝ := if y then logistic t else 1 - logistic t

theorem logisticMass_positive (y : Bool) (t : ℝ) : 0 < logisticMass y t := by
  cases y <;> simp only [logisticMass, Bool.false_eq_true, ↓reduceIte]
  · linarith [(logistic_mem_Ioo t).2]
  · exact (logistic_mem_Ioo t).1

theorem logisticMass_normalized (t : ℝ) : ∑ y : Bool, logisticMass y t = 1 := by
  simp [logisticMass, Fintype.sum_bool]

def logisticLogLikelihood (y : Bool) (t : ℝ) : ℝ :=
  (if y then t else 0) - Real.log (1 + Real.exp t)

theorem logistic_log_likelihood (y : Bool) (t : ℝ) :
    Real.log (logisticMass y t) = logisticLogLikelihood y t := by
  have he := Real.exp_pos t
  have hd : 1 + Real.exp t ≠ 0 := by positivity
  cases y
  · have hc : 1 - logistic t = 1 / (1 + Real.exp t) := by
      unfold logistic; field_simp; ring
    simp [logisticMass, logisticLogLikelihood, hc, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hd]
  · simp [logisticMass, logisticLogLikelihood, logistic, Real.log_div he.ne' hd]

theorem hasDerivAt_logistic (t : ℝ) :
    HasDerivAt logistic (logistic t * (1 - logistic t)) t := by
  have hd : 1 + Real.exp t ≠ 0 := by positivity
  convert! (Real.hasDerivAt_exp t).div ((Real.hasDerivAt_exp t).const_add 1) hd using 1
  unfold logistic
  field_simp
  <;> ring

theorem hasDerivAt_logisticLogLikelihood (y : Bool) (t : ℝ) :
    HasDerivAt (logisticLogLikelihood y) ((if y then 1 else 0) - logistic t) t := by
  have hd : 1 + Real.exp t ≠ 0 := by positivity
  have hlog := ((Real.hasDerivAt_exp t).const_add 1).log hd
  cases y
  · simpa [logisticLogLikelihood, logistic] using! (hasDerivAt_const t (0 : ℝ)).sub hlog
  · simpa [logisticLogLikelihood, logistic] using! (hasDerivAt_id t).sub hlog

theorem logistic_second_derivative (y : Bool) (t : ℝ) :
    deriv (deriv (logisticLogLikelihood y)) t = -(logistic t * (1 - logistic t)) := by
  have he : deriv (logisticLogLikelihood y) = fun s => (if y then 1 else 0) - logistic s :=
    funext (fun s => (hasDerivAt_logisticLogLikelihood y s).deriv)
  rw [he]
  exact ((hasDerivAt_logistic t).const_sub _).deriv

/-- Every Hessian quadratic form is nonpositive. This does not assert
strict concavity, uniqueness, or existence of a finite logistic MLE. -/
theorem logistic_hessian_nonpositive {n p : ℕ} (η : Fin n → ℝ)
    (x : Fin n → Fin p → ℝ) (v : Fin p → ℝ) :
    (∑ i, -(logistic (η i) * (1 - logistic (η i))) * (∑ j, x i j * v j) ^ 2) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (mul_nonneg (logistic_mem_Ioo _).1.le
      (sub_nonneg.mpr (logistic_mem_Ioo _).2.le))) (sq_nonneg _)

end LectureNotes
