import LectureNotes.GammaConjugacy
import LectureNotes.IIDScoreAsymptotics
import Mathlib.Probability.Distributions.Exponential

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

/-- L7 Example 1 uses the rate parameter, whose mean is its reciprocal. -/
def exponentialLogLikelihood (x r : ℝ) : ℝ := Real.log r - r * x

theorem exponential_log_density {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    Real.log (exponentialPDFReal r x) = exponentialLogLikelihood x r := by
  have he : exponentialPDFReal r x = r * Real.exp (-(r * x)) := by
    simp [exponentialPDFReal, gammaPDFReal, hx, Real.Gamma_one]
  rw [he, Real.log_mul hr.ne' (Real.exp_ne_zero _), Real.log_exp]
  rfl

theorem exponential_log_derivative {r : ℝ} (hr : 0 < r) (x : ℝ) :
    HasDerivAt (exponentialLogLikelihood x) (1 / r - x) r := by
  simpa [exponentialLogLikelihood, one_div] using!
    (Real.hasDerivAt_log hr.ne').sub ((hasDerivAt_id r).mul_const x)

theorem exponential_score_derivative {r : ℝ} (hr : 0 < r) (x : ℝ) :
    HasDerivAt (fun t : ℝ => 1 / t - x) (-(1 / r ^ 2)) r := by
  simpa [one_div] using! (hasDerivAt_inv hr.ne').sub_const x

/-- The reciprocal sample mean is a global maximum, not only a solution of
the first-order equation. The total observation sum must be positive. -/
theorem exponential_mle_maximizes {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hs : 0 < ∑ i, x i) {r : ℝ} (hr : 0 < r) :
    (∑ i, exponentialLogLikelihood (x i) r) ≤
      ∑ i, exponentialLogLikelihood (x i) ((n : ℝ) / ∑ i, x i) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let m := (n : ℝ) / ∑ i, x i
  have hm : 0 < m := div_pos hnR hs
  have hb := Real.log_le_sub_one_of_pos (div_pos hr hm)
  rw [Real.log_div hr.ne' hm.ne'] at hb
  have hh : m * (∑ i, x i) = n := div_mul_cancel₀ _ hs.ne'
  have hh' : (n : ℝ) * (r / m - 1) = r * (∑ i, x i) - n := by
    rw [← hh]
    field_simp
    <;> ring
  have hc := mul_le_mul_of_nonneg_left hb hnR.le
  rw [hh'] at hc
  simp only [exponentialLogLikelihood, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  change _ ≤ (n : ℝ) * Real.log m - m * ∑ i, x i
  rw [hh]
  nlinarith

theorem exponential_mean {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ, x ∂expMeasure r) = 1 / r := gamma_mean 1 r zero_lt_one hr

/-- The same maximum for the actual exponential density on its support. -/
theorem exponential_mle_maximizes_density {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hs : 0 < ∑ i, x i) {r : ℝ} (hr : 0 < r) :
    (∑ i, Real.log (exponentialPDFReal r (x i))) ≤
      ∑ i, Real.log (exponentialPDFReal ((n : ℝ) / ∑ i, x i) (x i)) := by
  have he (t : ℝ) (ht : 0 < t) : (∑ i, Real.log (exponentialPDFReal t (x i))) =
      ∑ i, exponentialLogLikelihood (x i) t :=
    Finset.sum_congr rfl (fun i _ => exponential_log_density ht (hx i))
  rw [he r hr, he _ (div_pos (by exact_mod_cast hn) hs)]
  exact exponential_mle_maximizes hn x hs hr

theorem exponential_memLp_two {r : ℝ} (hr : 0 < r) :
    MemLp (id : ℝ → ℝ) 2 (expMeasure r) :=
  (memLp_two_iff_integrable_sq (by fun_prop)).mpr (gamma_power_integrable 1 r zero_lt_one hr 2)

theorem exponential_variance {r : ℝ} (hr : 0 < r) :
    Var[id; expMeasure r] = 1 / r ^ 2 := gamma_variance 1 r zero_lt_one hr

/-- Fisher information computed from the variance of the actual score law. -/
theorem exponential_score_information {r : ℝ} (hr : 0 < r) :
    Var[fun x : ℝ => 1 / r - x; expMeasure r] = 1 / r ^ 2 := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rw [variance_const_sub (by fun_prop)]
  exact exponential_variance hr

theorem exponential_score_mean {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ, (1 / r - x) ∂expMeasure r) = 0 := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hi : Integrable (fun x : ℝ => x) (expMeasure r) :=
    (exponential_memLp_two hr).integrable (by norm_num)
  rw [integral_sub (integrable_const _) hi]
  simp [exponential_mean hr]

theorem exponential_ae_pos {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂expMeasure r, 0 < x := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hz : cdf (expMeasure r) 0 = 0 := by simp [cdf_expMeasure_eq hr]
  have hm := ofReal_cdf (μ := expMeasure r) 0
  rw [hz, ENNReal.ofReal_zero] at hm
  rw [ae_iff]
  simp only [not_lt]
  exact hm.symm

theorem exponential_information_second_moment {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ, (1 / r - x) ^ 2 ∂expMeasure r) = 1 / r ^ 2 := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hs : MemLp (fun x : ℝ => 1 / r - x) 2 (expMeasure r) :=
    (memLp_const (1 / r)).sub (exponential_memLp_two hr)
  have hv := variance_eq_sub hs
  simp only [exponential_score_mean hr, zero_pow (by decide : 2 ≠ 0), sub_zero, Pi.pow_apply] at hv
  exact hv.symm.trans (exponential_score_information hr)

theorem exponential_information_negative_hessian {r : ℝ} (hr : 0 < r) :
    -(∫ _ : ℝ, -(1 / r ^ 2) ∂expMeasure r) = 1 / r ^ 2 := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  simp

/-- The sequence form of the observed sample mean; its zero-sample value is
irrelevant to every asymptotic assertion. -/
def exponentialSampleMean {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, X i ω) / n

def exponentialRateMLE {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (exponentialSampleMean X n ω)⁻¹

theorem exponential_sampleMean_positive {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} {r : ℝ} (hr : 0 < r)
    (hX : ∀ i, HasLaw (X i) (expMeasure r) P) {n : ℕ} (hn : 0 < n) :
    ∀ᵐ ω ∂P, 0 < exponentialSampleMean X n ω := by
  have hp (i) : ∀ᵐ ω ∂P, 0 < X i ω :=
    ((hX i).ae_iff (by measurability)).mpr (exponential_ae_pos hr)
  filter_upwards [ae_all_iff.mpr hp] with ω hω
  apply div_pos _ (by exact_mod_cast hn)
  exact Finset.sum_pos (fun i _ => hω i) (by simpa using hn.ne')

theorem exponential_sampleMean_consistent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {r : ℝ}
    (hr : 0 < r) (hm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (expMeasure r) P) (hind : iIndepFun X P) :
    ConvergesInProbability P (exponentialSampleMean X) (fun _ => 1 / r) := by
  have hi : IdentDistrib (X 0) id P (expMeasure r) := (hX 0).identDistrib HasLaw.id
  have h₂ := hi.memLp_iff.mpr (exponential_memLp_two hr)
  have he : (∫ ω, X 0 ω ∂P) = 1 / r := (hX 0).integral_eq.trans (exponential_mean hr)
  have h := iid_statistic_average_limit X id hm measurable_id hind
    (fun i => (hX i).identDistrib (hX 0)) (h₂.integrable (by norm_num))
  simpa only [id_eq, he, exponentialSampleMean] using! h

theorem exponential_mle_consistent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {r : ℝ}
    (hr : 0 < r) (hm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (expMeasure r) P) (hind : iIndepFun X P) :
    ConvergesInProbability P (exponentialRateMLE X) (fun _ => r) := by
  have h := continuous_mapping_probability_const (continuousAt_inv₀ (one_div_ne_zero hr.ne'))
    (exponential_sampleMean_consistent hr hm hX hind)
  simpa only [exponentialRateMLE, one_div, inv_inv] using! h

/-- The plug-in asymptotic variance estimates `r²`; the variance of the
unscaled estimator is estimated by this quantity divided by sample size. -/
theorem exponential_plugin_variance_consistent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {r : ℝ}
    (hr : 0 < r) (hm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (expMeasure r) P) (hind : iIndepFun X P) :
    ConvergesInProbability P (fun n ω => exponentialRateMLE X n ω ^ 2) (fun _ => r ^ 2) :=
  continuous_mapping_probability_const (g := fun x : ℝ => x ^ 2) (by fun_prop)
    (exponential_mle_consistent hr hm hX hind)

/-- The CLT for the exponential sample mean is derived from its second moment. -/
theorem exponential_sampleMean_clt {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : ℕ → Ω → ℝ} {r : ℝ} (hr : 0 < r)
    (hX : ∀ i, HasLaw (X i) (expMeasure r) P) (hind : iIndepFun X P)
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 ⟨1 / r ^ 2, by positivity⟩) Q) :
    ConvergesInDistribution P Q
      (fun n ω => Real.sqrt n * (exponentialSampleMean X n ω - 1 / r)) Z := by
  have hi : IdentDistrib (X 0) id P (expMeasure r) := (hX 0).identDistrib HasLaw.id
  have h₂ := hi.memLp_iff.mpr (exponential_memLp_two hr)
  have he : (∫ ω, X 0 ω ∂P) = 1 / r := (hX 0).integral_eq.trans (exponential_mean hr)
  have hv : Var[X 0; P].toNNReal = ⟨1 / r ^ 2, by positivity⟩ := by
    rw [(hX 0).variance_eq, exponential_variance hr]
    apply NNReal.coe_injective
    change max (1 / r ^ 2) 0 = 1 / r ^ 2
    exact max_eq_left (by positivity)
  have h := central_limit_theorem (X := X) (by simpa only [hv] using hZ) h₂ hind
    (fun i => (hX i).identDistrib (hX 0))
  rw [he] at h
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl)) h
  intro n
  apply ae_of_all
  intro ω
  dsimp only
  by_cases hn : n = 0
  · simp [hn]
  · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [← sqrt_times_average]
    unfold exponentialSampleMean
    congr 1
    field_simp

/-- L7 Example 1: square-root sample-size scaling of the rate MLE has limiting
normal variance `r²`. Consistency and the CLT are proved from the IID
exponential model; they are not assumptions of this theorem. -/
theorem exponential_mle_asymptotic_normality {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : ℕ → Ω → ℝ} {r : ℝ} (hr : 0 < r) (hm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (expMeasure r) P) (hind : iIndepFun X P)
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 ⟨1 / r ^ 2, by positivity⟩) Q) :
    ConvergesInDistribution P Q
      (fun n ω => Real.sqrt n * (exponentialRateMLE X n ω - r))
      (fun ω => -r * Z ω / (1 / r)) ∧
    HasLaw (fun ω => -r * Z ω / (1 / r)) (gaussianReal 0 ⟨r ^ 2, sq_nonneg r⟩) Q := by
  have hM := exponential_sampleMean_consistent hr hm hX hind
  have hC := exponential_sampleMean_clt hr hX hind hZ
  have hMm (n) : Measurable (exponentialSampleMean X n) := by
    unfold exponentialSampleMean
    exact (Finset.measurable_sum _ (fun i _ => hm i)).div_const (n : ℝ)
  have hN := continuous_mapping_distribution (g := fun x => -r * x) (by fun_prop) hC
  have h := slutsky_div (one_div_ne_zero hr.ne') hN hM (fun n => (hMm n).aemeasurable)
  constructor
  · apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl)) h
    intro n
    by_cases hn : n = 0
    · subst n
      exact ae_of_all _ (fun _ => by simp)
    filter_upwards [exponential_sampleMean_positive hr hX (Nat.pos_of_ne_zero hn)] with ω hω
    unfold exponentialRateMLE
    field_simp [hω.ne', hr.ne']
    <;> ring
  · have hlaw := gaussianReal_div_const (gaussianReal_const_mul hZ (-r)) (1 / r)
    simp only [mul_zero, zero_div] at hlaw
    convert! hlaw using 1
    congr 1
    apply NNReal.coe_injective
    change r ^ 2 = (-r) ^ 2 * (1 / r ^ 2) / (1 / r) ^ 2
    field_simp
    <;> ring

end LectureNotes
