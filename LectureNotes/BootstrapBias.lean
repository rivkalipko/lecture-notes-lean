import LectureNotes.BootstrapVarianceMoments

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

/-- Exact conditional bootstrap bias for a smooth transform of the sample mean. -/
def bootstrapBias {n : ℕ} [NeZero n] (g : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  (∫ b, g (sampleMean b) ∂bootstrapLaw x) - g (sampleMean x)

/-- Subtracting the exact conditional bootstrap bias. -/
def bootstrapBiasCorrected {n : ℕ} [NeZero n] (g : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  g (sampleMean x) - bootstrapBias g x

/-- Bias estimated from B complete resamples. The accompanying sampling law
is a product of B copies of the conditional bootstrap law. -/
def simulatedBootstrapBias {n B : ℕ} (g : ℝ → ℝ) (x : Fin n → ℝ)
    (b : Fin B → (Fin n → ℝ)) : ℝ :=
  sampleMean (fun j => g (sampleMean (b j))) - g (sampleMean x)

/-- A quadratic expectation is determined by the mean and variance. -/
theorem quadratic_expectation {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    (a b c : ℝ) :
    (∫ ω, (a * Y ω ^ 2 + b * Y ω + c) ∂P) =
      a * (Var[Y; P] + (∫ ω, Y ω ∂P) ^ 2) + b * (∫ ω, Y ω ∂P) + c := by
  have hi := hY.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hab : Integrable (fun ω => a * Y ω ^ 2 + b * Y ω) P := by
    simpa only [Pi.add_apply] using! (hY.integrable_sq.const_mul a).add (hi.const_mul b)
  rw [integral_add hab (integrable_const c), integral_add (hY.integrable_sq.const_mul a) (hi.const_mul b),
    integral_const_mul, integral_const_mul, integral_const]
  have hv := variance_eq_second_moment_sub_mean_sq P hY
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [hv]
  ring

/-- For a quadratic transform the exact bootstrap bias has the empirical
n-denominator variance. This identity also covers a one-observation sample. -/
theorem bootstrapBias_quadratic {n : ℕ} [NeZero n] (x : Fin n → ℝ)
    (a b c : ℝ) :
    bootstrapBias (fun y => a * y ^ 2 + b * y + c) x = a * empiricalVariance x / n := by
  letI := bootstrapLaw_isProbabilityMeasure x
  unfold bootstrapBias
  rw [quadratic_expectation (bootstrap_sampleMean_memLp x),
    bootstrap_sampleMean_variance, bootstrap_sampleMean_expectation]
  ring

theorem bootstrapBiasCorrected_quadratic {n : ℕ} [NeZero n] (x : Fin n → ℝ)
    (a b c : ℝ) :
    bootstrapBiasCorrected (fun y => a * y ^ 2 + b * y + c) x =
      a * sampleMean x ^ 2 + b * sampleMean x + c - a * empiricalVariance x / n := by
  simp only [bootstrapBiasCorrected, bootstrapBias_quadratic]

/-- Integrability of the empirical central second moment. -/
theorem empiricalVariance_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) :
    Integrable (fun ω => empiricalVariance (fun i => X i ω)) P := by
  simp only [empiricalVariance_eq_secondMoment_sub_sq]
  exact ((integrable_finsetSum _ (fun i _ => (hX i).integrable_sq)).const_mul _).sub
    (sampleMean_memLp hX).integrable_sq

/-- Expected empirical variance under equal means and variances; pairwise
independence suffices. The formula includes n=1. -/
theorem empiricalVariance_expectation {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 P)
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) P))
    {μ v : ℝ} (hm : ∀ i, P[X i] = μ) (hv : ∀ i, Var[X i; P] = v) :
    (∫ ω, empiricalVariance (fun i => X i ω) ∂P) = (1 - 1 / n) * v := by
  have hM := sampleMean_memLp hX
  have hmean := sampleMean_expectation hn (fun i => (hX i).integrable (by norm_num)) hm
  have hvar := sampleMean_variance hn hX hind hv
  have hsq (i) : (∫ ω, X i ω ^ 2 ∂P) = v + μ ^ 2 := by
    have h := variance_eq_second_moment_sub_mean_sq P (hX i)
    rw [hm i, hv i] at h
    linarith
  have hM2 : (∫ ω, sampleMean (fun i => X i ω) ^ 2 ∂P) = v / n + μ ^ 2 := by
    have h := variance_eq_second_moment_sub_mean_sq P hM
    rw [hmean, hvar] at h
    linarith
  simp only [empiricalVariance_eq_secondMoment_sub_sq]
  have hraw : Integrable (fun ω => sampleMean (fun i => X i ω ^ 2)) P := by
    unfold sampleMean
    exact (integrable_finsetSum _ (fun i _ => (hX i).integrable_sq)).const_mul _
  rw [integral_sub hraw hM.integrable_sq, sampleMean_expectation hn (fun i => (hX i).integrable_sq) hsq, hM2]
  ring

/-- The quadratic plug-in bias is a times the variance of the sample mean. -/
theorem quadratic_sampleMean_bias {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 P)
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) P))
    {μ v : ℝ} (hm : ∀ i, P[X i] = μ) (hv : ∀ i, Var[X i; P] = v)
    (a b c : ℝ) :
    (∫ ω, (a * sampleMean (fun i => X i ω) ^ 2 +
      b * sampleMean (fun i => X i ω) + c) ∂P) - (a * μ ^ 2 + b * μ + c) = a * v / n := by
  rw [quadratic_expectation (sampleMean_memLp hX),
    sampleMean_expectation hn (fun i => (hX i).integrable (by norm_num)) hm,
    sampleMean_variance hn hX hind hv]
  ring

/-- Ordinary exact bootstrap correction removes the quadratic order 1/n
bias but leaves the explicit order 1/n² bias. -/
theorem bootstrapBiasCorrected_quadratic_bias {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} [NeZero n]
    {X : Fin n → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 P)
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) P))
    {μ v : ℝ} (hm : ∀ i, P[X i] = μ) (hv : ∀ i, Var[X i; P] = v)
    (a b c : ℝ) :
    (∫ ω, bootstrapBiasCorrected (fun y => a * y ^ 2 + b * y + c)
      (fun i => X i ω) ∂P) - (a * μ ^ 2 + b * μ + c) = a * v / (n : ℝ) ^ 2 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hM := sampleMean_memLp hX
  have hi := hM.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simp only [bootstrapBiasCorrected_quadratic]
  have hpI : Integrable (fun ω => a * sampleMean (fun i => X i ω) ^ 2 +
      b * sampleMean (fun i => X i ω) + c) P := by
    simpa only [Pi.add_apply] using!
      (((hM.integrable_sq.const_mul a).add (hi.const_mul b)).add (integrable_const c))
  rw [integral_sub hpI (((empiricalVariance_integrable hX).const_mul a).div_const n),
    integral_div, integral_const_mul, empiricalVariance_expectation hn hX hind hm hv]
  have h := quadratic_sampleMean_bias hn hX hind hm hv a b c
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp at h ⊢
  nlinarith

/-- Inflating the quadratic bootstrap bias by n/(n-1) gives an exactly
unbiased quadratic estimator whenever n>1. -/
theorem quadratic_sampleVariance_correction_unbiased {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 1 < n)
    {X : Fin n → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 P)
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) P))
    {μ v : ℝ} (hm : ∀ i, P[X i] = μ) (hv : ∀ i, Var[X i; P] = v)
    (a b c : ℝ) :
    (∫ ω, (a * sampleMean (fun i => X i ω) ^ 2 + b * sampleMean (fun i => X i ω) + c -
      a * sampleVariance (fun i => X i ω) / n) ∂P) = a * μ ^ 2 + b * μ + c := by
  have hn0 : 0 < n := by omega
  have hM := sampleMean_memLp hX
  have hi := hM.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hV : Integrable (fun ω => sampleVariance (fun i => X i ω)) P := by
    unfold sampleVariance
    exact (integrable_finsetSum _ (fun i _ =>
      ((hX i).sub hM).integrable_sq)).div_const _
  have hpI : Integrable (fun ω => a * sampleMean (fun i => X i ω) ^ 2 +
      b * sampleMean (fun i => X i ω) + c) P := by
    simpa only [Pi.add_apply] using!
      (((hM.integrable_sq.const_mul a).add (hi.const_mul b)).add (integrable_const c))
  rw [integral_sub hpI ((hV.const_mul a).div_const n), integral_div, integral_const_mul,
    sampleVariance_unbiased hn hX hind hm hv]
  have h := quadratic_sampleMean_bias hn0 hX hind hm hv a b c
  linarith

end LectureNotes
