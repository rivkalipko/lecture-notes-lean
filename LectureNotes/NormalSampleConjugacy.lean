import LectureNotes.NormalConjugacy
import LectureNotes.BetaConjugacy
import LectureNotes.NormalUnknownVarianceMLE
import LectureNotes.DecisionTheory
import LectureNotes.BootstrapVarianceConsistency
import LectureNotes.MonteCarlo

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

/-- The full normalized normal sample likelihood separates into its value at
its mean and the parameter-dependent Gaussian kernel. -/
theorem normal_sample_likelihood_kernel {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) {v : ℝ≥0} (hv : 0 < v) (θ : ℝ) :
    (∏ i, gaussianPDFReal θ v (x i)) =
      (∏ i, gaussianPDFReal (sampleMean x) v (x i)) *
        Real.exp (-((n : ℝ) / v) * (θ - sampleMean x) ^ 2 / 2) := by
  have hp (t : ℝ) : 0 < ∏ i, gaussianPDFReal t v (x i) :=
    Finset.prod_pos (fun i _ => gaussianPDFReal_pos _ _ _ hv.ne')
  rw [← Real.exp_log (hp θ), ← Real.exp_log (hp (sampleMean x)), ← Real.exp_add]
  congr 1
  rw [normal_sample_log_density x θ hv,
    normal_sample_log_density x (sampleMean x) hv,
    sum_squared_error_decomposition hn x θ]
  ring

/-- L12's normal-normal posterior, using the actual normal prior measure and
the product of all normalized observation densities. Both variances are positive. -/
theorem normal_sample_conjugacy {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (μ₀ : ℝ) {v w : ℝ≥0} (hv : 0 < v) (hw : 0 < w) :
    bayesUpdate (gaussianReal μ₀ w) (fun θ => ∏ i, gaussianPDFReal θ v (x i)) =
      gaussianReal (normalPosteriorMean ((n : ℝ) / v) (1 / w) (sampleMean x) μ₀)
        ⟨normalPosteriorVariance ((n : ℝ) / v) (1 / w), by
          unfold normalPosteriorVariance; positivity⟩ := by
  rw [gaussianReal_of_var_ne_zero μ₀ hw.ne']
  change bayesUpdate (volume.withDensity (fun θ => ENNReal.ofReal (gaussianPDFReal μ₀ w θ)))
    (fun θ => ∏ i, gaussianPDFReal θ v (x i)) = _
  rw [bayesUpdate_withDensity volume _ _ (by fun_prop) (by
    unfold gaussianPDFReal; fun_prop) (gaussianPDFReal_nonneg μ₀ w)]
  have he (θ : ℝ) : gaussianPDFReal μ₀ w θ * (∏ i, gaussianPDFReal θ v (x i)) =
      ((Real.sqrt (2 * Real.pi * w))⁻¹ *
        (∏ i, gaussianPDFReal (sampleMean x) v (x i))) *
      Real.exp (-(((n : ℝ) / v) * (θ - sampleMean x) ^ 2 +
        (1 / w) * (θ - μ₀) ^ 2) / 2) := by
    rw [normal_sample_likelihood_kernel hn x hv θ, gaussianPDFReal_def]
    calc
      _ = ((Real.sqrt (2 * Real.pi * w))⁻¹ *
          (∏ i, gaussianPDFReal (sampleMean x) v (x i))) *
          (Real.exp (-(θ - μ₀) ^ 2 / (2 * w)) *
            Real.exp (-((n : ℝ) / v) * (θ - sampleMean x) ^ 2 / 2)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  simp_rw [he]
  rw [bayesUpdate_scale _ _ (by
    apply mul_ne_zero
    · apply inv_ne_zero; apply (Real.sqrt_pos.mpr _).ne'; positivity
    · exact (Finset.prod_pos (fun i _ => gaussianPDFReal_pos _ _ _ hv.ne')).ne')]
  exact normal_normal_conjugacy _ _ _ _ (by positivity) (by positivity)

/-- An empty sample leaves the actual Gaussian prior unchanged. -/
theorem normal_sample_conjugacy_empty (x : Fin 0 → ℝ) (μ₀ : ℝ) (w : ℝ≥0) :
    bayesUpdate (gaussianReal μ₀ w) (fun θ => ∏ i, gaussianPDFReal θ 1 (x i)) =
      gaussianReal μ₀ w := by
  simp [bayesUpdate, evidence]

/-- L13 Example 3, with unit observation variance and prior precision λ=1/w.
The displayed shrinkage mean and variance are the exact full-sample posterior. -/
theorem normal_unit_sample_conjugacy {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (μ₀ : ℝ) {w : ℝ≥0} (hw : 0 < w) :
    bayesUpdate (gaussianReal μ₀ w) (fun θ => ∏ i, gaussianPDFReal θ 1 (x i)) =
      gaussianReal ((1 / (w : ℝ)) / (1 / (w : ℝ) + n) * μ₀ +
        (n : ℝ) / (1 / (w : ℝ) + n) * sampleMean x)
        ⟨(w : ℝ) / (1 + n * w), by positivity⟩ := by
  rw [normal_sample_conjugacy hn x μ₀ (by norm_num) hw]
  congr 1
  · simp only [normalPosteriorMean, NNReal.coe_one, div_one]
    ring
  · apply NNReal.eq
    simp only [normalPosteriorVariance, NNReal.coe_one, div_one]
    have hwR : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
    field_simp
    <;> ring

/-- The precision-weighted expression is the expectation of the actual posterior. -/
theorem normal_sample_posterior_mean {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (μ₀ : ℝ) {v w : ℝ≥0} (hv : 0 < v) (hw : 0 < w) :
    (∫ θ, θ ∂bayesUpdate (gaussianReal μ₀ w)
      (fun θ => ∏ i, gaussianPDFReal θ v (x i))) =
      normalPosteriorMean ((n : ℝ) / v) (1 / w) (sampleMean x) μ₀ := by
  rw [normal_sample_conjugacy hn x μ₀ hv hw]
  exact integral_id_gaussianReal

/-- The inverse total precision is the variance of the actual posterior. -/
theorem normal_sample_posterior_variance {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (μ₀ : ℝ) {v w : ℝ≥0} (hv : 0 < v) (hw : 0 < w) :
    Var[id; bayesUpdate (gaussianReal μ₀ w)
      (fun θ => ∏ i, gaussianPDFReal θ v (x i))] =
      normalPosteriorVariance ((n : ℝ) / v) (1 / w) := by
  rw [normal_sample_conjugacy hn x μ₀ hv hw]
  exact variance_id_gaussianReal

/-- For every full observed sample, the displayed mean minimizes actual squared
posterior loss over all real actions. -/
theorem normal_sample_posterior_mean_minimizes {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (μ₀ : ℝ) {v w : ℝ≥0} (hv : 0 < v) (hw : 0 < w) (a : ℝ) :
    (∫ θ, (θ - normalPosteriorMean ((n : ℝ) / v) (1 / w) (sampleMean x) μ₀) ^ 2
      ∂bayesUpdate (gaussianReal μ₀ w) (fun θ => ∏ i, gaussianPDFReal θ v (x i))) ≤
      ∫ θ, (θ - a) ^ 2 ∂bayesUpdate (gaussianReal μ₀ w)
        (fun θ => ∏ i, gaussianPDFReal θ v (x i)) := by
  rw [normal_sample_conjugacy hn x μ₀ hv hw]
  simpa only [id_eq, integral_id_gaussianReal] using!
    posterior_mean_minimizes_squared_loss _ (memLp_id_gaussianReal 2) a

/-- Data dominate a fixed positive-variance normal prior: along any convergent
sample-mean sequence, the posterior mean has that limit and its variance vanishes. -/
theorem normal_sample_posterior_parameters_tendsto
    {m : ℕ → ℝ} {μ μ₀ : ℝ} {v w : ℝ≥0} (hv : 0 < v) (hw : 0 < w)
    (hm : Tendsto m atTop (𝓝 μ)) :
    Tendsto (fun n => normalPosteriorMean (((n + 1 : ℕ) : ℝ) / v)
      (1 / w) (m n) μ₀) atTop (𝓝 μ) ∧
    Tendsto (fun n => normalPosteriorVariance (((n + 1 : ℕ) : ℝ) / v)
      (1 / w)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hcoef : Tendsto (fun n : ℕ => ((v : ℝ) / w) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using tendsto_const_nhds.mul hinv
  have hden : Tendsto (fun n : ℕ => 1 + ((v : ℝ) / w) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 1) := by simpa using hcoef.const_add 1
  have hmean := (hm.add (hcoef.mul_const μ₀)).div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hvar := ((tendsto_const_nhds (x := (v : ℝ))).mul hinv).div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hwR : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
  constructor
  · simpa only [zero_mul, add_zero, div_one] using hmean.congr'
      (Eventually.of_forall fun n => by
        dsimp [normalPosteriorMean]
        have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
        <;> ring)
  · have hh : Tendsto (fun n : ℕ => ((v : ℝ) * (1 / ((n + 1 : ℕ) : ℝ))) /
        (1 + ((v : ℝ) / w) / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_div, Pi.div_apply] using! hvar
    apply hh.congr'
    filter_upwards [] with n
    dsimp [normalPosteriorVariance]
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring

/-- The actual finite-sample conjugate posterior concentrates at a limiting
sample mean; no posterior-normal approximation is needed. -/
theorem normal_sample_posterior_concentration
    (x : (n : ℕ) → Fin (n + 1) → ℝ) {μ μ₀ : ℝ} {v w : ℝ≥0}
    (hv : 0 < v) (hw : 0 < w)
    (hm : Tendsto (fun n => sampleMean (x n)) atTop (𝓝 μ)) :
    ∀ ε > 0, Tendsto (fun n =>
      (bayesUpdate (gaussianReal μ₀ w)
        (fun θ => ∏ i, gaussianPDFReal θ v (x n i))).real
        {θ | ε ≤ |θ - μ|}) atTop (𝓝 0) := by
  let m n := normalPosteriorMean (((n + 1 : ℕ) : ℝ) / v) (1 / w) (sampleMean (x n)) μ₀
  let s n : ℝ≥0 := ⟨normalPosteriorVariance (((n + 1 : ℕ) : ℝ) / v) (1 / w), by
    unfold normalPosteriorVariance; positivity⟩
  let Q n := gaussianReal (m n) (s n)
  have hLp n : MemLp (fun θ : ℝ => θ - m n) 2 (Q n) := by
    simpa only [Pi.sub_apply, id_eq] using! (memLp_id_gaussianReal 2).sub (memLp_const (m n))
  obtain ⟨hm', hv'⟩ := normal_sample_posterior_parameters_tendsto hv hw hm (μ₀ := μ₀)
  have hmse : Tendsto (fun n => ∫ θ, (θ - m n) ^ 2 ∂Q n) atTop (𝓝 0) := by
    have he n : (∫ θ, (θ - m n) ^ 2 ∂Q n) = (s n : ℝ) := by
      have hh := variance_eq_integral (by fun_prop : AEMeasurable (id : ℝ → ℝ) (Q n))
      simp only [Q, id_eq, integral_id_gaussianReal, variance_id_gaussianReal] at hh
      exact hh.symm
    simp_rw [he]
    exact hv'
  have hh := row_probability_center_limit hm' (row_secondMoment_implies_probability hLp hmse)
  intro ε hε
  convert hh ε hε using 1
  funext n
  rw [normal_sample_conjugacy (Nat.succ_pos n) (x n) μ₀ hv hw]

/-- L12's concentration claim in the actual IID normal sampling experiment.
Both the sample-mean limit and the posterior-moment limits are derived. -/
theorem iid_normal_sample_posterior_concentration {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    {μ μ₀ : ℝ} {v w : ℝ≥0} (hv : 0 < v) (hw : 0 < w)
    (hX : ∀ i, HasLaw (X i) (gaussianReal μ v) P) (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P, ∀ ε > 0, Tendsto (fun n =>
      (bayesUpdate (gaussianReal μ₀ w)
        (fun θ => ∏ i : Fin (n + 1), gaussianPDFReal θ v (X i ω))).real
        {θ | ε ≤ |θ - μ|}) atTop (𝓝 0) := by
  have hh := monteCarlo_mean_strong_consistency (hX 0).hasGaussianLaw.integrable hind
    (fun i => (hX i).identDistrib (hX 0))
  have hmean : (∫ ω, X 0 ω ∂P) = μ := by simpa using! (hX 0).integral_eq
  filter_upwards [hh] with ω hω
  apply normal_sample_posterior_concentration (fun n i => X i ω) hv hw
  rw [hmean] at hω
  exact hω.comp (tendsto_add_atTop_nat 1)

end LectureNotes
