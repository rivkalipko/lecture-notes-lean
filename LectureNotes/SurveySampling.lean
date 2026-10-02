import LectureNotes.FinitePopulation
import LectureNotes.BernoulliBinomialMoments

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

/-- Inverse joint-inclusion weighting estimates the design variance using
only products of observed units. Joint probabilities must be positive when used. -/
def horvitzThompsonVarianceEstimator {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (x : Fin N → ℝ) (R : Fin N → Ω → ℝ) (P : Measure Ω) (ω : Ω) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, R i ω * R j ω *
    ((pairInclusionProbability R P i j - inclusionProbability R P i * inclusionProbability R P j) *
      (x i * x j / (pairInclusionProbability R P i j *
        inclusionProbability R P i * inclusionProbability R P j)))

/-- Unbiased variance estimation needs nonzero joint inclusion probabilities,
in addition to the marginal inclusion condition for estimating the mean. -/
theorem horvitzThompsonVarianceEstimator_unbiased {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ)
    {R : Fin N → Ω → ℝ} (hR : ∀ i, MemLp (R i) 2 P)
    (hπ : ∀ i, inclusionProbability R P i ≠ 0)
    (hπ₂ : ∀ i j, pairInclusionProbability R P i j ≠ 0) :
    P[horvitzThompsonVarianceEstimator x R P] = Var[horvitzThompson x R P; P] := by
  rw [horvitzThompson_variance hN x hR hπ]
  have hp i j : Integrable (fun ω => R i ω * R j ω) P := by
    simpa only [Pi.mul_apply] using! (hR i).integrable_mul (hR j)
  unfold horvitzThompsonVarianceEstimator
  rw [integral_const_mul, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => (hp i j).mul_const _))]
  simp_rw [integral_finsetSum _ (fun j _ => (hp _ j).mul_const _), integral_mul_const]
  congr 1
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  change pairInclusionProbability R P i j * _ = _
  field_simp [hπ₂ i j, hπ i, hπ j]

/-- The preceding estimator for an actual finite-population sampling design. -/
theorem horvitzThompsonVarianceEstimator_design_unbiased {N : ℕ} (hN : 0 < N)
    (x : Fin N → ℝ) (P : Measure (Finset (Fin N))) [IsProbabilityMeasure P]
    (hπ : ∀ i : Fin N, 0 < P.real {s | i ∈ s})
    (hπ₂ : ∀ i j : Fin N, 0 < P.real {s | i ∈ s ∧ j ∈ s}) :
    P[horvitzThompsonVarianceEstimator x selectionIndicator P] =
      Var[horvitzThompson x selectionIndicator P; P] := by
  apply horvitzThompsonVarianceEstimator_unbiased hN x (fun i => selectionIndicator_memLp i P)
  · intro i
    simpa only [inclusionProbability, selectionIndicator_expectation] using (hπ i).ne'
  · intro i j
    simpa only [pairInclusionProbability, selectionIndicator_product_expectation] using (hπ₂ i j).ne'

/-- Poisson survey sampling: inclusion indicators are independent Bernoulli
variables; the sample size is random. -/
def poissonSamplingLaw {N : ℕ} (π : Fin N → Set.Icc (0 : ℝ) 1) : Measure (Fin N → ℝ) :=
  Measure.pi (fun i => bernoulliRealLaw (π i))

instance poissonSamplingLaw_probability {N : ℕ} (π : Fin N → Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (poissonSamplingLaw π) := by unfold poissonSamplingLaw; infer_instance

theorem poissonSampling_coordinate_law {N : ℕ} (π : Fin N → Set.Icc (0 : ℝ) 1) (i : Fin N) :
    HasLaw (fun r : Fin N → ℝ => r i) (bernoulliRealLaw (π i)) (poissonSamplingLaw π) :=
  (measurePreserving_eval (fun i => bernoulliRealLaw (π i)) i).hasLaw

/-- L2 Example 6: only the diagonal design-variance terms survive under
independent Bernoulli inclusion. Inclusion probability one is allowed. -/
theorem independent_bernoulli_horvitzThompson_variance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ} (x : Fin N → ℝ)
    (π : Fin N → Set.Icc (0 : ℝ) 1) (hπ : ∀ i, 0 < (π i : ℝ))
    {R : Fin N → Ω → ℝ} (hR : ∀ i, HasLaw (R i) (bernoulliRealLaw (π i)) P)
    (hind : Pairwise (fun i j => IndepFun (R i) (R j) P)) :
    Var[horvitzThompson x R P; P] =
      (N : ℝ)⁻¹ ^ 2 * ∑ i, ((1 - (π i : ℝ)) / (π i : ℝ)) * x i ^ 2 := by
  have h₂ i : MemLp (R i) 2 P :=
    ((hR i).identDistrib HasLaw.id).memLp_iff.mpr (bernoulliRealLaw_memLp_two (π i))
  have hm i : inclusionProbability R P i = (π i : ℝ) := by
    rw [inclusionProbability, (hR i).integral_eq, bernoulliRealLaw_mean]
  have hv i : Var[R i; P] = (π i : ℝ) * (1 - (π i : ℝ)) := by
    rw [(hR i).variance_eq, bernoulliRealLaw_variance]
  have hs : Var[fun ω => ∑ i, R i ω * (x i / inclusionProbability R P i); P] =
      ∑ i, Var[fun ω => R i ω * (x i / inclusionProbability R P i); P] := by
    convert! IndepFun.variance_sum (s := univ)
      (fun i _ => (h₂ i).mul_const (x i / inclusionProbability R P i))
      (fun i _ j _ hij => (hind hij).comp
        (by fun_prop : Measurable (fun z : ℝ => z * (x i / inclusionProbability R P i)))
        (by fun_prop : Measurable (fun z : ℝ => z * (x j / inclusionProbability R P j)))) using 1
    congr 1
    funext ω
    simp
  unfold horvitzThompson
  rw [variance_const_mul, hs]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [variance_mul_const, hv, hm]
  field_simp [(hπ i).ne']

theorem poissonSampling_horvitzThompson_variance {N : ℕ} (x : Fin N → ℝ)
    (π : Fin N → Set.Icc (0 : ℝ) 1) (hπ : ∀ i, 0 < (π i : ℝ)) :
    Var[horvitzThompson x (fun i r => r i) (poissonSamplingLaw π); poissonSamplingLaw π] =
      (N : ℝ)⁻¹ ^ 2 * ∑ i, ((1 - (π i : ℝ)) / (π i : ℝ)) * x i ^ 2 := by
  apply independent_bernoulli_horvitzThompson_variance x π hπ (poissonSampling_coordinate_law π)
  intro i j hij
  exact (iIndepFun_pi (fun _ => measurable_id.aemeasurable)).indepFun hij

/-- The nonnegative unbiased design-variance estimator for independent
Bernoulli sampling. Only units actually sampled contribute. -/
def poissonHTVarianceEstimator {Ω : Type*} {N : ℕ} (x π : Fin N → ℝ)
    (R : Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i, R i ω * ((1 - π i) / (π i) ^ 2) * x i ^ 2

theorem poissonHTVarianceEstimator_unbiased {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ} (x : Fin N → ℝ)
    (π : Fin N → Set.Icc (0 : ℝ) 1) (hπ : ∀ i, 0 < (π i : ℝ))
    {R : Fin N → Ω → ℝ} (hR : ∀ i, HasLaw (R i) (bernoulliRealLaw (π i)) P)
    (hind : Pairwise (fun i j => IndepFun (R i) (R j) P)) :
    P[poissonHTVarianceEstimator x (fun i => (π i : ℝ)) R] = Var[horvitzThompson x R P; P] := by
  rw [independent_bernoulli_horvitzThompson_variance x π hπ hR hind]
  have h₂ i : MemLp (R i) 2 P :=
    ((hR i).identDistrib HasLaw.id).memLp_iff.mpr (bernoulliRealLaw_memLp_two (π i))
  unfold poissonHTVarianceEstimator
  rw [integral_const_mul, integral_finsetSum _ (fun i _ =>
    (((h₂ i).integrable (by norm_num)).mul_const _).mul_const _)]
  simp only [integral_mul_const]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [(hR i).integral_eq, bernoulliRealLaw_mean]
  field_simp [(hπ i).ne']

/-- Under simple random sampling the inverse-inclusion estimator is exactly
the ordinary sample mean, so its general variance formula gives the FPC. -/
theorem horvitzThompson_simpleRandom_eq {N n : ℕ} (hn : 0 < n) (hN : n ≤ N)
    (x : Fin N → ℝ) (s : Finset (Fin N)) :
    horvitzThompson x selectionIndicator (simpleRandomSampling hN) s =
      designMean n x selectionIndicator s := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [horvitzThompson, inclusionProbability, selectionIndicator_expectation,
    simpleRandomSampling_inclusion hn hN, designMean]
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro i _
  field_simp

theorem horvitzThompson_simpleRandom_variance {N n : ℕ} (hn : 0 < n) (hN : n ≤ N)
    (hN2 : 1 < N) (x : Fin N → ℝ) :
    Var[horvitzThompson x selectionIndicator (simpleRandomSampling hN); simpleRandomSampling hN] =
      (1 - (n : ℝ) / N) * sampleVariance x / n := by
  have he := funext (horvitzThompson_simpleRandom_eq hn hN x)
  rw [he]
  exact simpleRandomSampling_variance hn hN hN2 x

end LectureNotes
