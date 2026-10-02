import LectureNotes.BernoulliOdds
import LectureNotes.BernoulliLikelihoodRatio
import LectureNotes.PoissonTests

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- Bernoulli relative entropy is the sum of the success and failure
Poisson deviances. The identity includes zero empirical counts. -/
theorem bernoulliDivergence_eq_poissonDeviances {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (x : ℝ) : bernoulliDivergence x p =
      poissonDeviance p x + poissonDeviance (1 - p) (1 - x) := by
  have hlog (a r : ℝ) (hr : r ≠ 0) :
      a * Real.log (a / r) = a * (Real.log a - Real.log r) := by
    by_cases ha : a = 0
    · simp [ha]
    · rw [Real.log_div ha hr]
  unfold bernoulliDivergence poissonDeviance
  rw [hlog x p hp.1.ne', hlog (1 - x) (1 - p) (sub_pos.mpr hp.2).ne']
  ring

/-- A continuous version of the quadratic Bernoulli deviance coefficient
at an interior null, defined at all empirical proportions including 0 and 1. -/
def bernoulliDevianceCoefficient (p x : ℝ) : ℝ :=
  poissonDevianceCoefficient p x + poissonDevianceCoefficient (1 - p) (1 - x)

theorem bernoulliDevianceCoefficient_continuousAt {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt (bernoulliDevianceCoefficient p) p :=
  (poissonDevianceCoefficient_continuousAt hp.1).add
    ((poissonDevianceCoefficient_continuousAt (sub_pos.mpr hp.2)).comp
      (continuousAt_const.sub continuousAt_id))

theorem bernoulliDevianceCoefficient_measurable (p : ℝ) :
    Measurable (bernoulliDevianceCoefficient p) :=
  (poissonDevianceCoefficient_measurable p).add
    ((poissonDevianceCoefficient_measurable (1 - p)).comp (measurable_const.sub measurable_id))

theorem bernoulliDevianceCoefficient_self {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    bernoulliDevianceCoefficient p p = 1 / (2 * p * (1 - p)) := by
  simp only [bernoulliDevianceCoefficient, poissonDevianceCoefficient, Function.update_self]
  field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne']
  ring

/-- The exact factorization has no exceptional empirical sample. -/
theorem bernoulliDivergence_factorization {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (x : ℝ) :
    bernoulliDivergence x p = (x - p) ^ 2 * bernoulliDevianceCoefficient p x := by
  rw [bernoulliDivergence_eq_poissonDeviances hp,
    poissonDeviance_factorization hp.1,
    poissonDeviance_factorization (sub_pos.mpr hp.2)]
  unfold bernoulliDevianceCoefficient
  ring

/-- Twice the sample size times Bernoulli relative entropy is exactly the
likelihood-ratio statistic of the actual ordered Bernoulli likelihood. -/
theorem bernoulli_actual_LR_eq_deviance {n : ℕ} (hn : 0 < n)
    (x : Fin n → Fin 2) (p : Ioo (0 : ℝ) 1) :
    -2 * Real.log (likelihoodRatio
      (fun (y : Fin n → Fin 2) (q : Ioo (0 : ℝ) 1) => ∏ i, bernoulliMass q (y i)) {p} x) =
      2 * n * bernoulliDivergence (sampleMean (fun i => ((x i).val : ℝ))) p := by
  have hc : 0 < bernoulliSuccessCount x + bernoulliFailureCount x := by
    rwa [bernoulli_counts_sum]
  have hh : -2 * Real.log (likelihoodRatio
      (fun (_ : Unit) (q : Ioo (0 : ℝ) 1) =>
        bernoulliCountLikelihood (bernoulliSuccessCount x) (bernoulliFailureCount x) q) {p} ()) =
      2 * n * bernoulliDivergence (sampleMean (fun i => ((x i).val : ℝ))) p := by
    rw [bernoulli_likelihoodRatio hc,
      minus_two_log_ratio _ _ (bernoulliCountLikelihood_pos p.property)
        (bernoulliCountMLE_likelihood_pos hc), bernoulli_log_likelihood_loss hc p.property]
    have hm : bernoulliCountMLE (bernoulliSuccessCount x) (bernoulliFailureCount x) =
        sampleMean (fun i => ((x i).val : ℝ)) := by
      unfold bernoulliCountMLE sampleMean
      rw [← Nat.cast_add, bernoulli_counts_sum, bernoulliSuccessCount_eq_sum, Nat.cast_sum, Fintype.card_fin]
      ring
    rw [hm, ← Nat.cast_add, bernoulli_counts_sum]
    ring
  unfold likelihoodRatio at hh ⊢
  simpa only [bernoulli_product_likelihood] using hh

/-- The actual IID Bernoulli deviance has Wilks's chi-square limit at each
fixed interior success probability. Boundary empirical proportions remain
in the statistic at every finite sample size. -/
theorem bernoulli_deviance_limit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {p : Icc (0 : ℝ) 1}
    (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (bernoulliRealLaw p) P) (hind : iIndepFun X P) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => 2 * ((n : ℝ) + 1) * bernoulliDivergence (bernoulliProportion X n ω) p)
      (fun z => z ^ 2) := by
  have hv : 0 < (p : ℝ) * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  have hc : ConvergesInProbability P
      (fun n ω => bernoulliDevianceCoefficient p (bernoulliProportion X n ω))
      (fun _ => 1 / (2 * (p : ℝ) * (1 - p))) := by
    simpa only [bernoulliDevianceCoefficient_self hp] using
      continuous_mapping_probability_const (bernoulliDevianceCoefficient_continuousAt hp)
        (bernoulliProportion_consistent hXm hX hind)
  have hs := (bernoulliProportion_clt hp hX hind).continuous_comp
    (g := fun x : ℝ => 2 * x ^ 2) (by fun_prop)
  have hh := slutsky_mul hs hc (fun n =>
    ((bernoulliDevianceCoefficient_measurable p).comp
      (bernoulliProportion_measurable hXm n)).aemeasurable)
  apply TendstoInDistribution.congr _ _ hh
  · intro n
    apply ae_of_all
    intro ω
    simp only [Function.comp_apply, mul_pow,
      Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)]
    rw [bernoulliDivergence_factorization hp]
    ring
  · apply ae_of_all
    intro z
    simp only [Function.comp_apply, mul_pow, Real.sq_sqrt hv.le]
    field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne']

/-- Casting binary observations preserves their genuine Bernoulli law. -/
theorem bernoulli_fin_real_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → Fin 2} {p : Icc (0 : ℝ) 1}
    (hX : HasLaw X (bernoulliMeasure (1 : Fin 2) 0 p) P) :
    HasLaw (fun ω => ((X ω).val : ℝ)) (bernoulliRealLaw p) P := by
  have hm : Measurable (fun x : Fin 2 => (x.val : ℝ)) := Measurable.of_discrete
  have hh : HasLaw (fun x : Fin 2 => (x.val : ℝ)) (bernoulliRealLaw p)
      (bernoulliMeasure (1 : Fin 2) 0 p) := by
    refine ⟨hm.aemeasurable, ?_⟩
    simp only [map_bernoulliMeasure, bernoulliRealLaw, Fin.val_one, Nat.cast_one,
      Fin.val_zero, Nat.cast_zero]
  exact hh.fun_comp hX

/-- Wilks calibration for the actual supremum likelihood ratio on `(0,1)`.
The likelihood supremum also handles all-zero and all-one samples. -/
theorem bernoulli_actual_likelihoodRatio_limit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → Fin 2}
    {p : Icc (0 : ℝ) 1} (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (bernoulliMeasure (1 : Fin 2) 0 p) P)
    (hind : iIndepFun X P) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => -2 * Real.log (likelihoodRatio
        (fun (y : Fin (n + 1) → Fin 2) (q : Ioo (0 : ℝ) 1) => ∏ i, bernoulliMass q (y i))
        {(⟨(p : ℝ), hp⟩ : Ioo (0 : ℝ) 1)} (fun i => X i ω))) (fun z => z ^ 2) := by
  have hm : Measurable (fun x : Fin 2 => (x.val : ℝ)) := Measurable.of_discrete
  have h := bernoulli_deviance_limit hp (fun i => hm.comp (hXm i))
    (fun i => bernoulli_fin_real_hasLaw (hX i))
    (hind.comp (fun _ x => (x.val : ℝ)) (fun _ => hm))
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl)) h
  intro n
  apply ae_of_all
  intro ω
  simpa only [Nat.cast_add, Nat.cast_one, bernoulliProportion, Function.comp_apply] using!
    (bernoulli_actual_LR_eq_deviance (by omega : 0 < n + 1)
      (fun i => X i ω) ⟨(p : ℝ), hp⟩).symm

/-- The exact nonlinear likelihood-ratio confidence set has asymptotic
coverage `1−α` for every fixed interior Bernoulli parameter. -/
theorem bernoulli_LR_confidence_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → Fin 2}
    {p : Icc (0 : ℝ) 1} (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (bernoulliMeasure (1 : Fin 2) 0 p) P)
    (hind : iIndepFun X P) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => P.real {ω | (⟨(p : ℝ), hp⟩ : Ioo (0 : ℝ) 1) ∈
      {q : Ioo (0 : ℝ) 1 | -2 * Real.log (likelihoodRatio
        (fun (y : Fin (n + 1) → Fin 2) (t : Ioo (0 : ℝ) 1) => ∏ i, bernoulliMass t (y i))
        {q} (fun i => X i ω)) ≤ distributionQuantile (chiSquared 1) (1 - α)}})
      atTop (𝓝 (1 - α)) := by
  exact chiSquared_weak_limit_coverage (by norm_num : 0 < (1 : ℕ))
    (bernoulli_actual_likelihoodRatio_limit hp hXm hX hind)
    (standard_normal_square (show HasLaw id (gaussianReal 0 1) (gaussianReal 0 1) from HasLaw.id))
    (show 1 - α ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hα.2], by linarith [hα.1]⟩)

/-- The strict upper-tail LR test has asymptotic size α under the actual
Bernoulli experiment. This is a pointwise assertion at an interior null. -/
theorem bernoulli_actual_likelihoodRatio_null_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → Fin 2}
    {p : Icc (0 : ℝ) 1} (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (bernoulliMeasure (1 : Fin 2) 0 p) P)
    (hind : iIndepFun X P) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => P.real {ω | distributionQuantile (chiSquared 1) (1 - α) <
      -2 * Real.log (likelihoodRatio
        (fun (y : Fin (n + 1) → Fin 2) (q : Ioo (0 : ℝ) 1) => ∏ i, bernoulliMass q (y i))
        {(⟨(p : ℝ), hp⟩ : Ioo (0 : ℝ) 1)} (fun i => X i ω))}) atTop (𝓝 α) := by
  apply chiSquared_one_limit_rejection_size _
    (bernoulli_actual_likelihoodRatio_limit hp hXm hX hind) hα
  intro n
  simp_rw [bernoulli_actual_LR_eq_deviance (Nat.succ_pos n)]
  have hm i : Measurable (fun ω => ((X i ω).val : ℝ)) :=
    (Measurable.of_discrete : Measurable (fun x : Fin 2 => (x.val : ℝ))).comp (hXm i)
  unfold bernoulliDivergence sampleMean
  fun_prop

/-- L11's displayed nonlinear count inequality, with its chi-square cutoff,
has the claimed asymptotic coverage. Both empirical boundary samples are included. -/
theorem bernoulli_nonlinear_LR_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → Fin 2}
    {p : Icc (0 : ℝ) 1} (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (bernoulliMeasure (1 : Fin 2) 0 p) P)
    (hind : iIndepFun X P) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => P.real {ω |
      let x : Fin (n + 1) → Fin 2 := fun i => X i ω
      let s := bernoulliSuccessCount x
      let f := bernoulliFailureCount x
      2 * (s * Real.log (bernoulliCountMLE s f / p) +
        f * Real.log ((1 - bernoulliCountMLE s f) / (1 - p))) ≤
        distributionQuantile (chiSquared 1) (1 - α)}) atTop (𝓝 (1 - α)) := by
  convert! bernoulli_LR_confidence_coverage hp hXm hX hind hα using 1
  funext n
  congr 1
  ext ω
  simp only [mem_ofPred_eq]
  rw [bernoulli_product_LR_statistic (Nat.succ_pos n)]

end LectureNotes
