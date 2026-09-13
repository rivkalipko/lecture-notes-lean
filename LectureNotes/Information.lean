import LectureNotes.EstimationTheory

/-! L1 covariance bound and L6 Cramér–Rao's variance bound.
The score-moment derivative hypothesis is explicit, as in L6 Theorem 2. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- L1 Cauchy–Schwarz for covariance, including the zero-variance case. -/
theorem covariance_sq_le_variances {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    cov[X, Y; P] ^ 2 ≤ Var[X; P] * Var[Y; P] := by
  by_cases hzero : Var[Y; P] = 0
  · have heq := zero_variance_is_constant P hY hzero
    have hc : cov[X, Y; P] = 0 := by
      unfold covariance
      apply integral_eq_zero_of_ae
      filter_upwards [heq] with ω hω
      simp [hω]
    simp [hc, hzero]
  · have hy : 0 < Var[Y; P] := lt_of_le_of_ne (variance_nonneg Y P) (Ne.symm hzero)
    have hq := variance_nonneg
      (fun ω => Var[Y; P] * X ω - cov[X, Y; P] * Y ω) P
    rw [variance_fun_sub (hX.const_mul _) (hY.const_mul _),
      variance_const_mul, variance_const_mul,
      covariance_const_mul_left, covariance_const_mul_right] at hq
    have he : Var[Y; P] *
        (Var[X; P] * Var[Y; P] - cov[X, Y; P] ^ 2) =
        Var[Y; P] ^ 2 * Var[X; P] -
          2 * (Var[Y; P] * (cov[X, Y; P] * cov[X, Y; P])) +
          cov[X, Y; P] ^ 2 * Var[Y; P] := by ring
    rw [← he] at hq
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hq hy)

/-- L6 Theorem 2 after differentiating the model's expectation. The hypothesis
on the derivative is the score identity justified by model regularity. -/
theorem cramer_rao_bound {W S : Ω → ℝ} (hW : MemLp W 2 P) (hS : MemLp S 2 P)
    (hscore : P[S] = 0) (hI : 0 < FisherInformation P S)
    {mean : ℝ → ℝ} {θ : ℝ}
    (hd : HasDerivAt mean (∫ ω, W ω * S ω ∂P) θ) :
    (deriv mean θ) ^ 2 / FisherInformation P S ≤ Var[W; P] := by
  have h := covariance_sq_le_variances P hW hS
  rw [covariance_eq_sub hW hS, hscore, mul_zero, sub_zero] at h
  have hv : Var[S; P] = FisherInformation P S := by
    exact variance_of_integral_eq_zero hS.aemeasurable hscore
  rw [hv] at h
  rw [hd.deriv]
  exact (div_le_iff₀ hI).2 h

/-- Algebraic corollary when the score-product moment is the derivative of
the identity. `RegularDensity.cramer_rao_unbiased` derives this situation from
unbiasedness throughout an open parameter domain. -/
theorem cramer_rao_unbiased_from_score_identity {W S : Ω → ℝ}
    (hW : MemLp W 2 P) (hS : MemLp S 2 P)
    (hscore : P[S] = 0) (hI : 0 < FisherInformation P S) {θ : ℝ}
    (hd : HasDerivAt (fun t : ℝ => t) (∫ ω, W ω * S ω ∂P) θ) :
    1 / FisherInformation P S ≤ Var[W; P] := by
  simpa using cramer_rao_bound P hW hS hscore hI hd

/-- Information adds for independent, mean-zero scores; the mean-zero
condition is essential and fails in the notes' uniform-endpoint example. -/
theorem fisherInformation_sum {n : ℕ} {S : Fin n → Ω → ℝ}
    (hS : ∀ i, MemLp (S i) 2 P) (hzero : ∀ i, P[S i] = 0)
    (hind : Pairwise (fun i j => IndepFun (S i) (S j) P)) :
    FisherInformation P (fun ω => ∑ i, S i ω) = ∑ i, FisherInformation P (S i) := by
  have hsum := memLp_finsetSum Finset.univ (fun i _ => hS i)
  have he : P[fun ω => ∑ i, S i ω] = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hS i).integrable (by norm_num))]
    simp [hzero]
  have hv : Var[fun ω => ∑ i, S i ω; P] = ∑ i, Var[S i; P] := by
    convert! IndepFun.variance_sum (s := Finset.univ) (fun i _ => hS i)
      (fun i _ j _ hij => hind hij) using 1
    congr 1
    funext ω
    simp
  rw [variance_of_integral_eq_zero hsum.aemeasurable he] at hv
  simpa only [variance_of_integral_eq_zero (hS _).aemeasurable (hzero _),
    FisherInformation] using hv
end LectureNotes
