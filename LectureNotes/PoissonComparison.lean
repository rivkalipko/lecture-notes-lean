import LectureNotes.PoissonTests

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

/-- Exact probability of the finite sample on which the positive-rate MLE
is unattained. It is positive at every finite sample size and positive rate. -/
theorem poisson_all_zero_probability (n : ℕ) (r : ℝ≥0) :
    (poissonSampleExperiment n r).real {(fun _ : Fin n => (0 : ℕ))} =
      Real.exp (-(n : ℝ) * r) := by
  rw [poissonSampleLikelihood_mass, poissonSampleLikelihood_formula]
  simp

theorem iid_poisson_all_zero_probability {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℕ} {r : ℝ≥0}
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P) :
    P.real {ω | ∀ i, X i ω = 0} = Real.exp (-(n : ℝ) * r) := by
  have h : HasLaw (fun ω i => X i ω) (poissonSampleExperiment n r) P := hind.hasLaw_pi hX
  have he := h.measureReal_eq (p := fun x => x = (fun _ : Fin n => (0 : ℕ)))
    (measurableSet_singleton _)
  change P.real {ω | (fun i => X i ω) = (fun _ => 0)} =
    (poissonSampleExperiment n r).real {(fun _ : Fin n => (0 : ℕ))} at he
  rw [poisson_all_zero_probability] at he
  simpa only [funext_iff] using he

/-- Under every positive population rate the finite all-zero event becomes
negligible; at rate zero it instead has probability one. -/
theorem poisson_all_zero_probability_tendsto {r : ℝ≥0} (hr : 0 < r) :
    Tendsto (fun n : ℕ => (poissonSampleExperiment (n + 1) r).real
      {(fun _ : Fin (n + 1) => (0 : ℕ))}) atTop (𝓝 0) := by
  simp_rw [poisson_all_zero_probability]
  apply Real.tendsto_exp_atBot.comp
  have hh : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (r : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).atTop_mul_const hr
  simpa only [neg_mul, Function.comp_def] using! (tendsto_neg_atTop_atBot.comp hh)

theorem poisson_zero_rate_all_zero_probability (n : ℕ) :
    (poissonSampleExperiment n 0).real {(fun _ : Fin n => (0 : ℕ))} = 1 := by
  simp [poisson_all_zero_probability]

/-- An actual Poisson score statistic times a consistent vanishing coefficient
is negligible. This proves equivalence of statistics on the same sample. -/
theorem poisson_quadratic_coefficient_equivalence {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℕ} {r : ℝ≥0}
    (hr : 0 < r) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P)
    (g : ℝ → ℝ) (hgm : Measurable g) (hgc : ContinuousAt g r) (hgr : g r = 1) :
    ConvergesInProbability P (fun n ω =>
      poissonLM ((n : ℝ) + 1) (poissonMLESequence X n ω) r *
        (g (poissonMLESequence X n ω) - 1)) (fun _ => 0) := by
  have hc : ConvergesInProbability P (fun n ω => g (poissonMLESequence X n ω) - 1)
      (fun _ => 0) := by
    simpa only [hgr, sub_self] using continuous_mapping_probability_const (hgc.sub_const 1)
      (poissonMLE_consistency hXm hX hind)
  exact slutsky_mul_zero (poissonLM_limit hr hX hind) hc
    (fun n => ((hgm.comp (poissonMLESequence_measurable hXm n)).sub_const 1).aemeasurable)

/-- Wald minus score tends to zero in probability, stronger than merely
having the same marginal limit distribution. Zero empirical means are retained. -/
theorem poissonWald_sub_LM_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℕ} {r : ℝ≥0}
    (hr : 0 < r) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P) :
    ConvergesInProbability P (fun n ω =>
      poissonWald ((n : ℝ) + 1) (poissonMLESequence X n ω) r -
      poissonLM ((n : ℝ) + 1) (poissonMLESequence X n ω) r) (fun _ => 0) := by
  have hrR : (r : ℝ) ≠ 0 := ne_of_gt hr
  have hh := poisson_quadratic_coefficient_equivalence hr hXm hX hind
    (fun m : ℝ => (r : ℝ) / m) (by fun_prop)
    (continuousAt_const.div continuousAt_id hrR) (div_self hrR)
  convert! hh using 1
  funext n ω
  unfold poissonWald poissonLM
  field_simp
  <;> ring

/-- LR minus score tends to zero in probability, using the derived quadratic
coefficient of the genuine Poisson log likelihood. -/
theorem poissonLR_sub_LM_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℕ} {r : ℝ≥0}
    (hr : 0 < r) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P) :
    ConvergesInProbability P (fun n ω =>
      poissonLR ((n : ℝ) + 1) (poissonMLESequence X n ω) r -
      poissonLM ((n : ℝ) + 1) (poissonMLESequence X n ω) r) (fun _ => 0) := by
  have hrR : (0 : ℝ) < r := hr
  have hg : 2 * (r : ℝ) * poissonDevianceCoefficient r r = 1 := by
    simp only [poissonDevianceCoefficient, Function.update_self]
    field_simp
  have hh := poisson_quadratic_coefficient_equivalence hr hXm hX hind
    (fun m => 2 * (r : ℝ) * poissonDevianceCoefficient r m)
    ((poissonDevianceCoefficient_measurable r).const_mul _)
    ((poissonDevianceCoefficient_continuousAt hrR).const_mul _) hg
  convert! hh using 1
  funext n ω
  change 2 * ((n : ℝ) + 1) * poissonDeviance r _ - _ = _
  rw [poissonDeviance_factorization hrR]
  unfold poissonLM
  field_simp
  <;> ring

end LectureNotes
