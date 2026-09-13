import LectureNotes.Sampling

/-! L2 sample moments and the Horvitz–Thompson estimator. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Finset
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def sampleVariance {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, (x i - sampleMean x) ^ 2) / (n - 1 : ℝ)

theorem sampleMean_expectation {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Integrable (X i) P) {μ : ℝ} (hμ : ∀ i, P[X i] = μ) :
    P[fun ω => sampleMean (fun i => X i ω)] = μ := by
  simp only [sampleMean, Fintype.card_fin]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hX i)]
  simp [hμ, hn.ne']

theorem sampleMean_memLp {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) :
    MemLp (fun ω => sampleMean (fun i => X i ω)) 2 P := by
  unfold sampleMean
  exact (memLp_finsetSum _ (fun i _ => hX i)).const_mul _

theorem sampleMean_variance {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) (hind : Pairwise (fun i j => IndepFun (X i) (X j) P))
    {σ2 : ℝ} (hv : ∀ i, Var[X i; P] = σ2) :
    Var[fun ω => sampleMean (fun i => X i ω); P] = σ2 / n := by
  have hs : Var[fun ω => ∑ i, X i ω; P] = ∑ i, Var[X i; P] := by
    convert! IndepFun.variance_sum (s := univ) (fun i _ => hX i)
      (fun i _ j _ hij => hind hij) using 1
    congr 1
    funext ω
    simp
  simp only [sampleMean, Fintype.card_fin]
  rw [variance_const_mul, hs]
  simp only [hv, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- L2 Lemma 1: unbiasedness of sample variance. Pairwise independence suffices. -/
theorem sampleVariance_unbiased {n : ℕ} (hn : 1 < n) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P)
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) P))
    {μ σ2 : ℝ} (hμ : ∀ i, P[X i] = μ) (hv : ∀ i, Var[X i; P] = σ2) :
    P[fun ω => sampleVariance (fun i => X i ω)] = σ2 := by
  have hn0 : 0 < n := by omega
  letI : NeZero n := ⟨hn0.ne'⟩
  have hM := sampleMean_memLp hX
  have hmean := sampleMean_expectation hn0
    (fun i => (hX i).integrable (by norm_num)) hμ
  have hvar := sampleMean_variance hn0 hX hind hv
  have hsecond (i) : (∫ ω, X i ω ^ 2 ∂P) = σ2 + μ ^ 2 := by
    have h := variance_eq_second_moment_sub_mean_sq P (hX i)
    rw [hv i, hμ i] at h
    linarith
  have hMsecond : (∫ ω, sampleMean (fun i => X i ω) ^ 2 ∂P) =
      σ2 / n + μ ^ 2 := by
    have h := variance_eq_second_moment_sub_mean_sq P hM
    rw [hmean, hvar] at h
    linarith
  have hid (ω) := sum_centered_sq_sampleMean (fun i => X i ω)
  simp only [Fintype.card_fin] at hid
  simp only [sampleVariance, hid]
  rw [integral_div, integral_sub
    (integrable_finsetSum _ (fun i _ => (hX i).integrable_sq))
    (hM.integrable_sq.const_mul n), integral_finsetSum _ (fun i _ => (hX i).integrable_sq),
    integral_const_mul, hMsecond]
  simp only [hsecond, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hnm : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  field_simp
  ring

/-- First moment of a sampling weight. For a selection indicator this is its
inclusion probability, as proved in `FinitePopulation`. -/
def inclusionProbability {N : ℕ} (R : Fin N → Ω → ℝ) (P : Measure Ω) (i : Fin N) : ℝ :=
  P[R i]
/-- Product moment; this is a joint inclusion probability for indicators. -/
def pairInclusionProbability {N : ℕ} (R : Fin N → Ω → ℝ) (P : Measure Ω)
    (i j : Fin N) : ℝ := ∫ ω, R i ω * R j ω ∂P
def horvitzThompson {N : ℕ} (x : Fin N → ℝ) (R : Fin N → Ω → ℝ)
    (P : Measure Ω) (ω : Ω) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, R i ω * (x i / inclusionProbability R P i)

theorem horvitzThompson_unbiased {N : ℕ} (_hN : 0 < N) (x : Fin N → ℝ)
    {R : Fin N → Ω → ℝ} (hR : ∀ i, Integrable (R i) P)
    (hπ : ∀ i, inclusionProbability R P i ≠ 0) :
    P[horvitzThompson x R P] = sampleMean x := by
  unfold horvitzThompson sampleMean
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hR i).mul_const _)]
  simp only [Fintype.card_fin, integral_mul_const]
  congr 1
  apply sum_congr rfl
  intro i _
  change inclusionProbability R P i * (x i / inclusionProbability R P i) = x i
  field_simp [hπ i]

theorem horvitzThompson_variance {N : ℕ} (_hN : 0 < N) (x : Fin N → ℝ)
    {R : Fin N → Ω → ℝ} (hR : ∀ i, MemLp (R i) 2 P)
    (_hπ : ∀ i, inclusionProbability R P i ≠ 0) :
    Var[horvitzThompson x R P; P] =
      (N : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j,
        (pairInclusionProbability R P i j -
          inclusionProbability R P i * inclusionProbability R P j) *
          (x i * x j / (inclusionProbability R P i * inclusionProbability R P j)) := by
  unfold horvitzThompson
  rw [variance_const_mul, variance_fun_sum (fun i => (hR i).mul_const _)]
  congr 1
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [covariance_mul_const_left, covariance_mul_const_right, covariance_eq_sub (hR i) (hR j)]
  unfold inclusionProbability pairInclusionProbability
  simp only [Pi.mul_apply]
  ring
end LectureNotes
