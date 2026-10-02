import LectureNotes.MethodOfMoments

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- L3 Example 4: the square of an IID sample mean has Gaussian first-order
limit with variance 4μ²v. Zero mean or variance is permitted. -/
theorem iid_squared_sampleMean_limit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hi : iIndepFun X P) (hid : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ConvergesInDistribution P (gaussianReal 0 Var[X 0; P].toNNReal)
      (fun n ω => Real.sqrt n * ((sampleMean (fun i : Fin n => X i ω)) ^ 2 - P[X 0] ^ 2))
      (fun z => z * (2 * P[X 0])) ∧
    HasLaw (fun z : ℝ => z * (2 * P[X 0]))
      (gaussianReal 0 (⟨4 * P[X 0] ^ 2, by positivity⟩ * Var[X 0; P].toNNReal))
      (gaussianReal 0 Var[X 0; P].toNNReal) := by
  have hd (m : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * m) m := by
    simpa only [id_eq, Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one] using! (hasDerivAt_id m).pow 2
  have hh := moment_inverse_asymptotic_normality hXm hX hi hid
    (by fun_prop : Continuous (fun x : ℝ => x ^ 2)) (hd P[X 0]).differentiableAt rfl
    (show HasLaw id (gaussianReal 0 Var[X 0; P].toNNReal)
      (gaussianReal 0 Var[X 0; P].toNNReal) from HasLaw.id)
  rw [(hd P[X 0]).deriv] at hh
  have he (n : ℕ) (ω : Ω) : momentInverseEstimator id (fun x : ℝ => x ^ 2) X n ω =
      (sampleMean (fun i : Fin n => X i ω)) ^ 2 := by
    simp only [momentInverseEstimator, id_eq, sampleMean, Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range (fun i => X i ω) n]
    ring
  have hv : (⟨(2 * P[X 0]) ^ 2, sq_nonneg _⟩ : ℝ≥0) = ⟨4 * P[X 0] ^ 2, by positivity⟩ := by
    ext
    ring
  simpa only [he, id_eq, hv] using! hh

/-- At a zero population mean the first-order target is the constant zero;
a nondegenerate Gaussian approximation at this scale would be incorrect. -/
theorem iid_squared_sampleMean_zero_mean_limit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hi : iIndepFun X P) (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hm : P[X 0] = 0) :
    ConvergesInDistribution P (gaussianReal 0 Var[X 0; P].toNNReal)
      (fun n ω => Real.sqrt n * (sampleMean (fun i : Fin n => X i ω)) ^ 2) (fun _ => 0) := by
  simpa only [hm, zero_pow (by norm_num : 2 ≠ 0), sub_zero, mul_zero] using
    (iid_squared_sampleMean_limit hXm hX hi hid).1

end LectureNotes
