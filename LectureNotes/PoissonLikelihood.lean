import LectureNotes.PoissonMoments
import LectureNotes.LikelihoodRatio

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The actual IID Poisson experiment, including rate zero. -/
def poissonSampleExperiment (n : ℕ) (r : ℝ≥0) : Measure (Fin n → ℕ) :=
  Measure.pi (fun _ => poissonMeasure r)

instance poissonSampleExperiment_probability (n : ℕ) (r : ℝ≥0) :
    IsProbabilityMeasure (poissonSampleExperiment n r) := by
  unfold poissonSampleExperiment
  infer_instance

/-- The likelihood is the product of actual one-observation probability masses. -/
def poissonSampleLikelihood {n : ℕ} (x : Fin n → ℕ) (r : ℝ≥0) : ℝ :=
  ∏ i, (poissonMeasure r).real {x i}

/-- The nonnegative sample mean is the MLE on the closed parameter space. -/
def poissonSampleMLE {n : ℕ} (x : Fin n → ℕ) : ℝ≥0 :=
  (∑ i, (x i : ℝ≥0)) / n

/-- The usual real log-likelihood expression; its equality with the actual
logarithm below is stated at positive rates. -/
def poissonSampleLogLikelihood {n : ℕ} (x : Fin n → ℕ) (r : ℝ) : ℝ :=
  (∑ i, (x i : ℝ)) * Real.log r - n * r - Real.log (∏ i, (x i).factorial : ℝ)

theorem poissonSampleLikelihood_mass {n : ℕ} (x : Fin n → ℕ) (r : ℝ≥0) :
    (poissonSampleExperiment n r).real {x} = poissonSampleLikelihood x r := by
  simp [poissonSampleExperiment, poissonSampleLikelihood, measureReal_def, ENNReal.toReal_prod]

theorem poissonSampleLikelihood_formula {n : ℕ} (x : Fin n → ℕ) (r : ℝ≥0) :
    poissonSampleLikelihood x r = (r : ℝ) ^ (∑ i, x i) * Real.exp (-n * r) /
      (∏ i, (x i).factorial : ℝ) := by
  unfold poissonSampleLikelihood
  simp_rw [poissonMeasure_real_singleton]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← Real.exp_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (n : ℝ) * -(r : ℝ) = -n * r by ring]
  ring

theorem poissonSampleLikelihood_nonneg {n : ℕ} (x : Fin n → ℕ) (r : ℝ≥0) :
    0 ≤ poissonSampleLikelihood x r :=
  Finset.prod_nonneg (fun _ _ => measureReal_nonneg)

theorem poissonSampleLikelihood_pos {n : ℕ} (x : Fin n → ℕ) {r : ℝ≥0} (hr : 0 < r) :
    0 < poissonSampleLikelihood x r :=
  Finset.prod_pos (fun i _ => poissonMeasure_real_singleton_pos (x i) hr)

theorem poissonSampleMLE_coe {n : ℕ} (x : Fin n → ℕ) :
    (poissonSampleMLE x : ℝ) = sampleMean (fun i => (x i : ℝ)) := by
  simp only [poissonSampleMLE, NNReal.coe_div, NNReal.coe_sum, NNReal.coe_natCast,
    sampleMean, Fintype.card_fin]
  ring

theorem poissonSampleLikelihood_log {n : ℕ} (x : Fin n → ℕ)
    {r : ℝ≥0} (hr : 0 < r) :
    Real.log (poissonSampleLikelihood x r) = poissonSampleLogLikelihood x r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hf : (0 : ℝ) < ∏ i, ((x i).factorial : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast Nat.factorial_pos (x i))
  rw [poissonSampleLikelihood_formula, Real.log_div (mul_pos (pow_pos hrR _) (Real.exp_pos _)).ne' hf.ne',
    Real.log_mul (pow_pos hrR _).ne' (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
  simp only [poissonSampleLogLikelihood, Nat.cast_sum]
  ring

theorem poissonSampleLogLikelihood_derivative {n : ℕ} (x : Fin n → ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (poissonSampleLogLikelihood x) ((∑ i, (x i : ℝ)) / r - n) r := by
  convert! (((Real.hasDerivAt_log hr.ne').const_mul (∑ i, (x i : ℝ))).sub
    ((hasDerivAt_id r).const_mul (n : ℝ))).sub_const (Real.log (∏ i, (x i).factorial : ℝ)) using 1 <;>
    simp [poissonSampleLogLikelihood, id_eq] <;> ring

theorem poissonSampleLogLikelihood_score_derivative {n : ℕ} (x : Fin n → ℕ)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => (∑ i, (x i : ℝ)) / t - n)
      (-(∑ i, (x i : ℝ)) / r ^ 2) r := by
  convert! (((hasDerivAt_const r (∑ i, (x i : ℝ))).div (hasDerivAt_id r) hr.ne').sub_const (n : ℝ)) using 1 <;> simp [id_eq] <;> ring

/-- The log kernel is globally maximized at the mean, from log u≤u−1. -/
theorem poisson_log_kernel_max {a m r n : ℝ} (hm : 0 < m) (hr : 0 < r)
    (hn : 0 ≤ n) (ha : a = n * m) : a * Real.log r - n * r ≤ a * Real.log m - n * m := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hr hm))
    (show 0 ≤ a by rw [ha]; positivity)
  have he : a * (r / m - 1) = n * r - n * m := by rw [ha]; field_simp
  rw [Real.log_div hr.ne' hm.ne', he] at h
  nlinarith

/-- On the closed nonnegative rate space the sample mean is an actual global
maximizer, including the all-zero sample whose maximum is at rate zero. -/
theorem poissonSampleMLE_isMLE {n : ℕ} (hn : 0 < n) (x : Fin n → ℕ) :
    IsMLE poissonSampleLikelihood x (poissonSampleMLE x) := by
  intro r
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hzero : ∑ i, x i = 0
  · have hx : ∀ i, x i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hzero) i (Finset.mem_univ i)
    have hm : poissonSampleMLE x = 0 := by simp [poissonSampleMLE, hx]
    rw [hm, poissonSampleLikelihood_formula, poissonSampleLikelihood_formula]
    simp only [hx, Finset.sum_const_zero, pow_zero, NNReal.coe_zero, mul_zero,
      neg_zero, Real.exp_zero, mul_one, Nat.factorial_zero, Nat.cast_one, Finset.prod_const_one, div_one, one_mul]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnR.le) r.coe_nonneg)
  · have hpos : 0 < poissonSampleMLE x := by
      unfold poissonSampleMLE
      apply div_pos _ (by exact_mod_cast hn)
      exact_mod_cast Nat.pos_of_ne_zero hzero
    by_cases hr : r = 0
    · have hzL : poissonSampleLikelihood x 0 = 0 := by
        rw [poissonSampleLikelihood_formula]
        simp [hzero]
      rw [hr, hzL]
      exact poissonSampleLikelihood_nonneg x (poissonSampleMLE x)
    · have hrpos : 0 < r := lt_of_le_of_ne (show (0 : ℝ≥0) ≤ r from zero_le) (Ne.symm hr)
      apply (Real.log_le_log_iff (poissonSampleLikelihood_pos x hrpos)
        (poissonSampleLikelihood_pos x hpos)).mp
      rw [poissonSampleLikelihood_log x hrpos, poissonSampleLikelihood_log x hpos]
      unfold poissonSampleLogLikelihood
      apply sub_le_sub_right
      apply poisson_log_kernel_max (by exact_mod_cast hpos) (by exact_mod_cast hrpos) hnR.le
      rw [poissonSampleMLE_coe]
      simp only [sampleMean, Fintype.card_fin]
      field_simp

/-- With all-zero observations a strictly positive rate cannot maximize the
likelihood: halving it strictly improves the likelihood. -/
theorem poisson_all_zero_positive_improvement {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℕ) (hx : ∀ i, x i = 0) {r : ℝ≥0} (hr : 0 < r) :
    poissonSampleLikelihood x r < poissonSampleLikelihood x (r / 2) := by
  simp only [poissonSampleLikelihood_formula, hx, Finset.sum_const_zero, pow_zero,
    one_mul, Nat.factorial_zero, Nat.cast_one, Finset.prod_const_one, div_one,
    NNReal.coe_div, NNReal.coe_ofNat, Real.exp_lt_exp]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  nlinarith [mul_pos hnR hrR]

/-- Actual likelihood-ratio suprema reduce to the likelihood evaluated at
the null rate and at the proved maximum. -/
theorem poisson_likelihoodRatio_eq {n : ℕ} (hn : 0 < n) (x : Fin n → ℕ) (r₀ : ℝ≥0) :
    likelihoodRatio poissonSampleLikelihood {r₀} x =
      poissonSampleLikelihood x r₀ / poissonSampleLikelihood x (poissonSampleMLE x) := by
  exact likelihoodRatio_eq_of_maximizers _ _ _ (mem_singleton r₀)
    (fun _ h => by rw [mem_singleton_iff.mp h]) (poissonSampleMLE_isMLE hn x)

/-- The source LR formula is the actual likelihood-ratio statistic. The
formula remains valid at an all-zero sample by its continuous boundary value. -/
theorem poisson_minus_two_log_likelihoodRatio {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℕ) {r₀ : ℝ≥0} (hr₀ : 0 < r₀) :
    -2 * Real.log (likelihoodRatio poissonSampleLikelihood {r₀} x) =
      poissonLR n (poissonSampleMLE x) r₀ := by
  by_cases hzero : ∑ i, x i = 0
  · have hx : ∀ i, x i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hzero) i (Finset.mem_univ i)
    have hm : poissonSampleMLE x = 0 := by simp [poissonSampleMLE, hx]
    rw [poisson_likelihoodRatio_eq hn, hm]
    simp [poissonSampleLikelihood_formula, hx, poissonLR]
    ring
  · have hm : 0 < poissonSampleMLE x := by
      unfold poissonSampleMLE
      apply div_pos _ (by exact_mod_cast hn)
      exact_mod_cast Nat.pos_of_ne_zero hzero
    have hmR : (0 : ℝ) < poissonSampleMLE x := by exact_mod_cast hm
    have hrR : (0 : ℝ) < r₀ := by exact_mod_cast hr₀
    have hsum : (∑ i, (x i : ℝ)) = n * (poissonSampleMLE x : ℝ) := by
      rw [poissonSampleMLE_coe]
      simp only [sampleMean, Fintype.card_fin]
      field_simp
    rw [poisson_likelihoodRatio_eq hn,
      minus_two_log_ratio _ _ (poissonSampleLikelihood_pos x hr₀) (poissonSampleLikelihood_pos x hm),
      poissonSampleLikelihood_log x hm, poissonSampleLikelihood_log x hr₀]
    unfold poissonSampleLogLikelihood poissonLR
    rw [hsum, Real.log_div hmR.ne' hrR.ne']
    ring

/-- The displayed score equation is valid at the interior maximum, but the
all-zero boundary maximum is deliberately excluded. -/
theorem poisson_score_zero_at_mle {n : ℕ} (hn : 0 < n) (x : Fin n → ℕ)
    (hx : 0 < ∑ i, x i) :
    (∑ i, (x i : ℝ)) / (poissonSampleMLE x : ℝ) - n = 0 := by
  have hsum : (0 : ℝ) < ∑ i, (x i : ℝ) := by exact_mod_cast hx
  rw [poissonSampleMLE_coe]
  simp only [sampleMean, Fintype.card_fin]
  field_simp
  ring

end LectureNotes
