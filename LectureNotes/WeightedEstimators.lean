import LectureNotes.Estimation
import LectureNotes.SamplingMoments

noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Finset

/-- The weighted mean from L5 Example 6. The weights are deterministic. -/
def weightedEstimator {n : ℕ} (w : Fin n → ℝ) {Ω : Type*}
    (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ := ∑ i, w i * X i ω

theorem weightedEstimator_memLp {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Fin n → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 P)
    (w : Fin n → ℝ) : MemLp (weightedEstimator w X) 2 P := by
  have h := memLp_finsetSum' univ (fun i _ => (hX i).const_mul (w i))
  have he : (∑ i, fun ω => w i * X i ω) = weightedEstimator w X := by
    ext ω
    simp [weightedEstimator]
  rwa [he] at h

theorem weightedEstimator_mean {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) {μ : ℝ} (hm : ∀ i, P[X i] = μ)
    (w : Fin n → ℝ) : P[weightedEstimator w X] = μ * ∑ i, w i := by
  unfold weightedEstimator
  rw [integral_finsetSum univ (fun i _ => ((hX i).integrable (by norm_num)).const_mul _)]
  simp_rw [integral_const_mul, hm]
  rw [← sum_mul, mul_comm]

theorem weightedEstimator_variance {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) (hi : Pairwise (fun i j => IndepFun (X i) (X j) P))
    {v : ℝ} (hv : ∀ i, Var[X i; P] = v) (w : Fin n → ℝ) :
    Var[weightedEstimator w X; P] = v * ∑ i, (w i) ^ 2 := by
  have hind : Set.Pairwise (↑(univ : Finset (Fin n)))
      (fun i j => IndepFun (fun ω => w i * X i ω) (fun ω => w j * X j ω) P) := by
    intro i _ j _ hij
    exact (hi hij).comp (measurable_const.mul measurable_id)
      (measurable_const.mul measurable_id)
  have h := IndepFun.variance_sum (s := univ)
    (fun i _ => (hX i).const_mul (w i)) hind
  have he : (∑ i, fun ω => w i * X i ω) = weightedEstimator w X := by
    ext ω
    simp [weightedEstimator]
  rw [he] at h
  simp_rw [variance_const_mul, hv] at h
  rw [← sum_mul, mul_comm] at h
  exact h

theorem weightedEstimator_mse {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) (hi : Pairwise (fun i j => IndepFun (X i) (X j) P))
    {μ v : ℝ} (hm : ∀ i, P[X i] = μ) (hv : ∀ i, Var[X i; P] = v)
    (w : Fin n → ℝ) : mse P (weightedEstimator w X) μ =
      μ ^ 2 * ((∑ i, w i) - 1) ^ 2 + v * ∑ i, (w i) ^ 2 := by
  rw [mse_eq_variance_add_bias_sq P (weightedEstimator_memLp hX w) μ,
    weightedEstimator_variance hX hi hv, bias, weightedEstimator_mean hX hm]
  ring

/-- At the particular mean zero every weighted estimator is unbiased. The
unit-sum condition is necessary at a nonzero mean, or across all means. -/
theorem weightedEstimator_unbiased_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) {μ : ℝ} (hm : ∀ i, P[X i] = μ)
    (w : Fin n → ℝ) : Unbiased P (weightedEstimator w X) μ ↔
      μ = 0 ∨ ∑ i, w i = 1 := by
  rw [Unbiased, and_iff_right ((weightedEstimator_memLp hX w).integrable (by norm_num)),
    weightedEstimator_mean hX hm]
  constructor
  · intro h
    have he : μ * ((∑ i, w i) - 1) = 0 := by nlinarith
    simpa only [sub_eq_zero] using mul_eq_zero.mp he
  · rintro (h | h) <;> simp [h]

/-- Algebraic variance decomposition for unit-sum weights. -/
theorem unit_sum_weights_sq {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ)
    (hw : ∑ i, w i = 1) :
    (∑ i, (w i) ^ 2) = 1 / n + ∑ i, (w i - 1 / n) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hc : ∑ i, w i = (Fintype.card (Fin n) : ℝ) * (1 / n) := by
    simp [hw, hn0]
  have h := sum_centered_sq w (1 / n) hc
  simp only [Fintype.card_fin] at h
  have he : (n : ℝ) * (1 / (n : ℝ)) ^ 2 = 1 / (n : ℝ) := by field_simp
  rw [he] at h
  linarith

/-- Unique minimum variance among unit-sum weights, when the common variance
is strictly positive. -/
theorem unit_sum_weights_variance_minimum {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℝ) (hw : ∑ i, w i = 1) {v : ℝ} (hv : 0 < v) :
    v / n ≤ v * ∑ i, (w i) ^ 2 ∧
      (v * ∑ i, (w i) ^ 2 = v / n ↔ ∀ i, w i = 1 / n) := by
  rw [unit_sum_weights_sq hn w hw]
  rw [mul_add, mul_one_div]
  have hs : 0 ≤ ∑ i, (w i - 1 / n) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  constructor
  · nlinarith
  · constructor
    · intro he i
      have hz : ∑ j, (w j - 1 / n) ^ 2 = 0 := by nlinarith
      have hi := (sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (w j - 1 / n))).mp hz i (mem_univ i)
      nlinarith [sq_nonneg (w i - 1 / n)]
    · intro he
      simp [he]

/-- The oracle minimizing unrestricted weighted-mean MSE depends on the
unknown mean and variance. The displayed identity proves global optimality. -/
theorem weighted_mse_oracle_identity {n : ℕ} (w : Fin n → ℝ) (μ v : ℝ)
    (hv : 0 < v) :
    μ ^ 2 * ((∑ i, w i) - 1) ^ 2 + v * ∑ i, (w i) ^ 2 =
      μ ^ 2 * v / (v + n * μ ^ 2) +
        v * ∑ i, (w i - μ ^ 2 / (v + n * μ ^ 2)) ^ 2 +
        μ ^ 2 * (∑ i, (w i - μ ^ 2 / (v + n * μ ^ 2))) ^ 2 := by
  have hd : v + n * μ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hs : ∑ i, (w i - μ ^ 2 / (v + n * μ ^ 2)) ^ 2 =
      (∑ i, (w i) ^ 2) - 2 * (μ ^ 2 / (v + n * μ ^ 2)) * (∑ i, w i) +
        n * (μ ^ 2 / (v + n * μ ^ 2)) ^ 2 := by
    have he (i : Fin n) : (w i - μ ^ 2 / (v + n * μ ^ 2)) ^ 2 =
        (w i) ^ 2 - (2 * (μ ^ 2 / (v + n * μ ^ 2))) * w i +
          (μ ^ 2 / (v + n * μ ^ 2)) ^ 2 := by ring
    simp only [he, sum_add_distrib, sum_sub_distrib, ← mul_sum,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hs, sum_sub_distrib]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  <;> ring

/-- The oracle is the unique global MSE minimizer for the actual weighted
estimator whenever the observations have a common positive variance. -/
theorem weightedEstimator_oracle_minimum {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) (hi : Pairwise (fun i j => IndepFun (X i) (X j) P))
    {μ v : ℝ} (hm : ∀ i, P[X i] = μ) (hv : ∀ i, Var[X i; P] = v)
    (hvpos : 0 < v) (w : Fin n → ℝ) :
    μ ^ 2 * v / (v + n * μ ^ 2) ≤ mse P (weightedEstimator w X) μ ∧
      (mse P (weightedEstimator w X) μ = μ ^ 2 * v / (v + n * μ ^ 2) ↔
        ∀ i, w i = μ ^ 2 / (v + n * μ ^ 2)) := by
  rw [weightedEstimator_mse hX hi hm hv,
    weighted_mse_oracle_identity w μ v hvpos]
  have hs : 0 ≤ ∑ i, (w i - μ ^ 2 / (v + n * μ ^ 2)) ^ 2 :=
    sum_nonneg (fun _ _ => sq_nonneg _)
  have hl : 0 ≤ μ ^ 2 * (∑ i, (w i - μ ^ 2 / (v + n * μ ^ 2))) ^ 2 := by positivity
  constructor
  · nlinarith
  · constructor
    · intro h i
      have hz : ∑ j, (w j - μ ^ 2 / (v + n * μ ^ 2)) ^ 2 = 0 := by nlinarith
      have hz' := (sum_eq_zero_iff_of_nonneg (fun j _ =>
        sq_nonneg (w j - μ ^ 2 / (v + n * μ ^ 2)))).mp hz i (mem_univ i)
      nlinarith
    · intro h
      simp [h]

theorem weightedEstimator_oracle_bias {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) {μ v : ℝ} (hm : ∀ i, P[X i] = μ)
    (hv : 0 < v) :
    bias P (weightedEstimator (fun _ => μ ^ 2 / (v + n * μ ^ 2)) X) μ =
      -μ * v / (v + n * μ ^ 2) := by
  rw [bias, weightedEstimator_mean hX hm]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd : v + n * μ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- With zero mean the oracle is the constant zero estimator (c=1).
Otherwise the shrinkage coefficient is strictly between zero and one. -/
theorem weighted_oracle_shrinkage_coefficient {n : ℕ} (hn : 0 < n)
    (μ : ℝ) {v : ℝ} (hv : 0 < v) :
    μ ^ 2 / (v + n * μ ^ 2) = (1 - v / (v + n * μ ^ 2)) / n ∧
      0 < v / (v + n * μ ^ 2) ∧ v / (v + n * μ ^ 2) ≤ 1 ∧
        (v / (v + n * μ ^ 2) < 1 ↔ μ ≠ 0) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < v + n * μ ^ 2 := by positivity
  refine ⟨?_, div_pos hv hd, ?_, ?_⟩
  · field_simp
    ring
  · rw [div_le_one hd]
    have h := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg μ)
    linarith
  · rw [div_lt_one hd]
    constructor
    · intro h hz
      simp [hz] at h
    · intro h
      have hp : 0 < (n : ℝ) * μ ^ 2 := mul_pos hn' (sq_pos_of_ne_zero h)
      linarith

/-- The oracle risk is strictly below the sample-mean risk, even at μ=0. -/
theorem weighted_oracle_strict_risk_improvement {n : ℕ} (hn : 0 < n)
    (μ : ℝ) {v : ℝ} (hv : 0 < v) :
    μ ^ 2 * v / (v + n * μ ^ 2) < v / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_lt_div_iff₀ (by positivity) hn']
  nlinarith [sq_pos_of_pos hv]

/-- The strict comparison is between the actual oracle weighted estimator
and the actual sample average, under the same sampling law. -/
theorem weightedEstimator_oracle_strictly_better_than_sampleMean
    {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) (hi : Pairwise (fun i j => IndepFun (X i) (X j) P))
    {μ v : ℝ} (hm : ∀ i, P[X i] = μ) (hv : ∀ i, Var[X i; P] = v)
    (hvpos : 0 < v) :
    mse P (weightedEstimator (fun _ => μ ^ 2 / (v + n * μ ^ 2)) X) μ <
      mse P (fun ω => sampleMean (fun i => X i ω)) μ := by
  rw [(weightedEstimator_oracle_minimum hX hi hm hv hvpos _).2.mpr (fun _ => rfl)]
  have hm' := sampleMean_expectation hn (fun i => (hX i).integrable (by norm_num)) hm
  rw [mse_eq_variance_add_bias_sq P (sampleMean_memLp hX) μ,
    sampleMean_variance hn hX hi hv, bias, hm', sub_self, zero_pow (by decide : 2 ≠ 0), add_zero]
  exact weighted_oracle_strict_risk_improvement hn μ hvpos

end LectureNotes
