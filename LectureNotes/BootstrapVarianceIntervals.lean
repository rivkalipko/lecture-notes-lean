import LectureNotes.BootstrapVarianceAsymptotics
import LectureNotes.BootstrapIntervals

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

/-- Sampling normality for the denominator-(n-1) variance estimator, scaled by
the positive standard deviation of the squared centered observation. -/
theorem iid_sampleVariance_standardized_clt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (τ : ℝ) (hτ : 0 < τ)
    (hvar : Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P] = τ ^ 2) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => Real.sqrt ((n : ℝ) + 1) / τ *
        (sampleVariance (fun i : Fin (n + 1) => X i ω) - Var[X 0; P])) id := by
  have h₂ : MemLp (X 0) 2 P := hX.mono_exponent (by norm_num)
  have hfour : Integrable (fun ω => (X 0 ω - P[X 0]) ^ 4) P := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs] using
      (hX.sub (memLp_const (P[X 0]))).integrable_norm_pow' (p := 4)
  have hZ : HasLaw (fun z : ℝ => τ * z)
      (gaussianReal 0 Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P].toNNReal)
      (gaussianReal 0 1) := by
    simpa [hvar, Real.toNNReal_of_nonneg (sq_nonneg τ)] using
      gaussianReal_const_mul (show HasLaw id (gaussianReal 0 1) (gaussianReal 0 1) from HasLaw.id) τ
  have hh := sampleVariance_clt hXm h₂ hind hident hfour hZ
  have hs : ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => Real.sqrt (n + 1 : ℕ) *
        (sampleVariance (fun i : Fin (n + 1) => X i ω) - Var[X 0; P])) (fun z => τ * z) :=
    { forall_aemeasurable := fun n => hh.forall_aemeasurable (n + 1)
      tendsto := hh.tendsto.comp (tendsto_add_atTop_nat 1) }
  have hc := continuous_mapping_distribution (g := fun z => z / τ) (by fun_prop) hs
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun z => by simp [hτ.ne'])) hc
  intro n
  apply ae_of_all
  intro ω
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- L8's basic bootstrap variance interval has its nominal asymptotic coverage
under finite fourth moment and positive variance of squared deviations. Its
quantiles use the actual conditional product-resampling distribution. -/
theorem iid_basic_bootstrap_variance_interval_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P]) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => P.real {ω | Var[X 0; P] ∈ Icc
      (sampleVariance (fun i : Fin (n + 1) => X i ω) -
        distributionQuantile (bootstrapSampleVarianceDifferenceLaw (fun i : Fin (n + 1) => X i ω)) b)
      (sampleVariance (fun i : Fin (n + 1) => X i ω) -
        distributionQuantile (bootstrapSampleVarianceDifferenceLaw (fun i : Fin (n + 1) => X i ω)) a)})
      atTop (𝓝 (b - a)) := by
  let σ := Real.sqrt (Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P])
  have hσ : 0 < σ := Real.sqrt_pos.mpr hv
  have hσsq : Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P] = σ ^ 2 := (Real.sq_sqrt hv.le).symm
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  let E (n : ℕ) (ω : Ω) := sampleVariance (fun i : Fin (n + 1) => X i ω)
  let S (n : ℕ) (_ω : Ω) := σ / Real.sqrt ((n : ℝ) + 1)
  let B (n : ℕ) (ω : Ω) := bootstrapSampleVarianceErrorLaw (fun i : Fin (n + 1) => X i ω) σ
  have hT : ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => (E n ω - Var[X 0; P]) / S n ω) id := by
    convert! iid_sampleVariance_standardized_clt hXm hX hind hident σ hσ hσsq using 1
    funext n ω
    dsimp only [E, S]
    rw [div_div_eq_mul_div]
    ring
  have h := bootstrap_interval_coverage B (gaussianReal 0 1)
    (E := E) (S := S) (θ := Var[X 0; P])
    (fun n => ae_of_all _ (fun _ => div_pos hσ (Real.sqrt_pos.mpr (by positivity))))
    (fun n => by dsimp only [E, S]; unfold sampleVariance sampleMean; fun_prop)
    hT HasLaw.id (gaussian_cdf_strictMono 0 1 (by norm_num))
    (iid_bootstrap_sampleVariance_cdf hXm hX hind hident σ hσ hσsq) ha hb hab
    (fun n => measurable_data_bootstrapSampleVarianceErrorLaw_quantile
      (fun i : Fin (n + 1) => X i) (fun i => hXm i) σ ha)
    (fun n => measurable_data_bootstrapSampleVarianceErrorLaw_quantile
      (fun i : Fin (n + 1) => X i) (fun i => hXm i) σ hb)
  have hqa n ω : distributionQuantile (B n ω) a * S n ω =
      distributionQuantile (bootstrapSampleVarianceDifferenceLaw (fun i : Fin (n + 1) => X i ω)) a := by
    simpa only [B, S, Nat.cast_add, Nat.cast_one] using
      bootstrapSampleVarianceErrorLaw_quantile_rescale (fun i : Fin (n + 1) => X i ω) σ hσ ha
  have hqb n ω : distributionQuantile (B n ω) b * S n ω =
      distributionQuantile (bootstrapSampleVarianceDifferenceLaw (fun i : Fin (n + 1) => X i ω)) b := by
    simpa only [B, S, Nat.cast_add, Nat.cast_one] using
      bootstrapSampleVarianceErrorLaw_quantile_rescale (fun i : Fin (n + 1) => X i ω) σ hσ hb
  simpa only [hqa, hqb, E] using! h


/-- The two-sided basic bootstrap variance test has limiting rejection
probability α under its variance null. Quantiles of the unscaled resampling
error are equivalent to L8's square-root scaled critical values. -/
theorem iid_basic_bootstrap_variance_test_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P])
    (v₀ : ℝ) (hnull : Var[X 0; P] = v₀) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω |
      sampleVariance (fun i : Fin (n + 1) => X i ω) - v₀ ∉ Icc
        (distributionQuantile (bootstrapSampleVarianceDifferenceLaw
          (fun i : Fin (n + 1) => X i ω)) (α / 2))
        (distributionQuantile (bootstrapSampleVarianceDifferenceLaw
          (fun i : Fin (n + 1) => X i ω)) (1 - α / 2))}) atTop (𝓝 α) := by
  have ha : α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hb : 1 - α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hab : α / 2 ≤ 1 - α / 2 := by linarith [hα.2]
  let E (n : ℕ) (ω : Ω) := sampleVariance (fun i : Fin (n + 1) => X i ω)
  let A (n : ℕ) (ω : Ω) := distributionQuantile (bootstrapSampleVarianceDifferenceLaw
    (fun i : Fin (n + 1) => X i ω)) (α / 2)
  let B (n : ℕ) (ω : Ω) := distributionQuantile (bootstrapSampleVarianceDifferenceLaw
    (fun i : Fin (n + 1) => X i ω)) (1 - α / 2)
  have hAm n : Measurable (A n) := measurable_data_bootstrapSampleVarianceDifferenceLaw_quantile
    (fun i : Fin (n + 1) => X i) (fun i => hXm i) ha
  have hBm n : Measurable (B n) := measurable_data_bootstrapSampleVarianceDifferenceLaw_quantile
    (fun i : Fin (n + 1) => X i) (fun i => hXm i) hb
  have hEm n : Measurable (E n) := by dsimp only [E]; unfold sampleVariance sampleMean; fun_prop
  have hm n : MeasurableSet {ω | v₀ ∈ Icc (E n ω - B n ω) (E n ω - A n ω)} :=
    (measurableSet_le ((hEm n).sub (hBm n)) measurable_const).inter
      (measurableSet_le measurable_const ((hEm n).sub (hAm n)))
  have hc := iid_basic_bootstrap_variance_interval_coverage hXm hX hind hident hv ha hb hab
  rw [hnull] at hc
  have he n : {ω | E n ω - v₀ ∉ Icc (A n ω) (B n ω)} =
      {ω | v₀ ∈ Icc (E n ω - B n ω) (E n ω - A n ω)}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_Icc]
    apply not_congr
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub hc
  convert! hh using 1
  · funext n
    change P.real {ω | E n ω - v₀ ∉ Icc (A n ω) (B n ω)} = _
    rw [he, measureReal_compl (hm n), probReal_univ]
  · ring

end LectureNotes
