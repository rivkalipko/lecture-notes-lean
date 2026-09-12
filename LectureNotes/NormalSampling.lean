import LectureNotes.SamplingMoments

/-! L2 normal sampling: the sample-mean law with explicit mean and variance. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem normal_sampleMean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    {μ : ℝ} {v : ℝ≥0} (hX : ∀ i, HasLaw (X i) (gaussianReal μ v) P)
    (hind : iIndepFun X P) :
    HasLaw (fun ω => sampleMean (fun i => X i ω)) (gaussianReal μ (v / n)) P := by
  have hlp (i) := (hX i).hasGaussianLaw.memLp_two
  have hm : P[fun ω => sampleMean (fun i => X i ω)] = μ :=
    sampleMean_expectation hn (fun i => (hX i).hasGaussianLaw.integrable)
      (fun i => by simpa using (hX i).integral_eq)
  have hv : Var[fun ω => sampleMean (fun i => X i ω); P] = (v : ℝ) / n :=
    sampleMean_variance hn hlp (fun _ _ hij => hind.indepFun hij)
      (fun i => by simpa using (hX i).variance_eq)
  have hg : HasGaussianLaw (fun ω => sampleMean (fun i => X i ω)) P := by
    have hsum := hind.hasGaussianLaw_fun_sum (fun i => (hX i).hasGaussianLaw)
    simpa only [sampleMean, Fintype.card_fin, smul_eq_mul] using hsum.fun_smul (n : ℝ)⁻¹
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal, hm, hv]
  congr 1
  ext
  simp
  positivity

/-- L2 Theorem 1(3): the sample mean and the entire residual vector are
independent. Taking a measurable squared norm gives independence of variance. -/
theorem normal_sampleMean_independent_residuals {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hX : ∀ i, HasLaw (X i) (gaussianReal μ v) P) (hind : iIndepFun X P) :
    IndepFun (fun ω => sampleMean (fun i => X i ω))
      (fun ω i => X i ω - sampleMean (fun j => X j ω)) P := by
  classical
  let M : (Fin n → ℝ) →L[ℝ] ℝ :=
    (n : ℝ)⁻¹ • ∑ i, ContinuousLinearMap.proj i
  have hM (x : Fin n → ℝ) : M x = sampleMean x := by
    simp [M, sampleMean]
  let R : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i - M)
  let V : (Fin n → ℝ) →L[ℝ] (Unit → ℝ) :=
    ContinuousLinearMap.pi (fun _ => M)
  have hg := (hind.hasGaussianLaw (fun i => (hX i).hasGaussianLaw)).map (V.prod R)
  have hlp (i) := (hX i).hasGaussianLaw.memLp_two
  have hmlp := sampleMean_memLp hlp
  have hv := sampleMean_variance (σ2 := (v : ℝ)) hn hlp (fun _ _ hij => hind.indepFun hij)
    (fun i => (hX i).variance_eq.trans (by simp))
  have hc (j : Fin n) :
      cov[fun ω => sampleMean (fun i => X i ω), X j; P] = (v : ℝ) / n := by
    simp only [sampleMean, Fintype.card_fin]
    rw [covariance_const_mul_left, covariance_fun_sum_left hlp (hlp j)]
    rw [Finset.sum_eq_single j]
    · rw [covariance_self (hlp j).aemeasurable, (hX j).variance_eq]
      simp [div_eq_mul_inv, mul_comm]
    · intro i _ hij
      exact (hind.indepFun hij).covariance_eq_zero (hlp i) (hlp j)
    · simp
  have hi : IndepFun (fun ω (_ : Unit) => sampleMean (fun i => X i ω))
      (fun ω i => X i ω - sampleMean (fun j => X j ω)) P := by
    apply HasGaussianLaw.indepFun_of_covariance_eval
    · simpa [V, R, hM, Function.comp_def] using hg
    · intro _ j
      rw [covariance_fun_sub_right hmlp (hlp j) hmlp,
        covariance_self hmlp.aemeasurable, hc, hv, sub_self]
  simpa only [Function.comp_def, id_eq] using
    hi.comp (measurable_pi_apply ()) measurable_id

theorem normal_sampleMean_independent_sampleVariance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hX : ∀ i, HasLaw (X i) (gaussianReal μ v) P) (hind : iIndepFun X P) :
    IndepFun (fun ω => sampleMean (fun i => X i ω))
      (fun ω => sampleVariance (fun i => X i ω)) P := by
  have hi := normal_sampleMean_independent_residuals hn hX hind
  simpa only [Function.comp_def, id_eq, sampleVariance] using
    hi.comp measurable_id
      (show Measurable (fun y : Fin n → ℝ => (∑ i, y i ^ 2) / (n - 1 : ℝ)) by fun_prop)
end LectureNotes
