import LectureNotes.PoissonAsymptotics
import LectureNotes.PoissonOpenLikelihood

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

/-- A chi-square limit gives the strict upper-tail rejection probability,
with the exact interior quantile and its atomless boundary. -/
theorem chiSquared_one_limit_rejection_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : ℕ → Ω → ℝ}
    (hTm : ∀ n, Measurable (T n))
    (hT : ConvergesInDistribution P (gaussianReal 0 1) T (fun z => z ^ 2))
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => P.real {ω | distributionQuantile (chiSquared 1) (1 - α) < T n ω})
      atTop (𝓝 α) := by
  have hc := chiSquared_weak_limit_coverage (by norm_num : 0 < (1 : ℕ)) hT
    (standard_normal_square (show HasLaw id (gaussianReal 0 1) (gaussianReal 0 1) from HasLaw.id))
    (show 1 - α ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hα.2], by linarith [hα.1]⟩)
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub hc
  convert! hh using 1
  · funext n
    have he : {ω | distributionQuantile (chiSquared 1) (1 - α) < T n ω} =
        {ω | T n ω ≤ distributionQuantile (chiSquared 1) (1 - α)}ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, not_le]
    rw [he, measureReal_compl (measurableSet_le (hTm n) measurable_const), probReal_univ]
  · ring

section IID
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℕ} {r : ℝ≥0}

/-- The LR of the actual positive-rate product likelihood has Wilks's law.
The positive-domain supremum handles the all-zero sample without a false score root. -/
theorem poisson_actual_likelihoodRatio_limit (hr : 0 < r)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => -2 * Real.log (likelihoodRatio
        (fun (y : Fin (n + 1) → ℕ) (q : Ioi (0 : ℝ≥0)) => poissonSampleLikelihood y q)
        {(⟨r, hr⟩ : Ioi (0 : ℝ≥0))} (fun i => X i ω))) (fun z => z ^ 2) := by
  have h := poissonLR_limit hr hXm hX hind
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl)) h
  intro n
  apply ae_of_all
  intro ω
  simpa only [Nat.cast_add, Nat.cast_one, poissonMLESequence] using
    (poisson_positive_minus_two_log_likelihoodRatio (by omega : 0 < n + 1)
      (fun i => X i ω) ⟨r, hr⟩).symm

/-- The actual Poisson score test is asymptotically level α at any positive null rate. -/
theorem poissonLM_null_size (hr : 0 < r) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => P.real {ω | distributionQuantile (chiSquared 1) (1 - α) <
      poissonLM ((n : ℝ) + 1) (poissonMLESequence X n ω) r}) atTop (𝓝 α) := by
  apply chiSquared_one_limit_rejection_size _ (poissonLM_limit hr hX hind) hα
  intro n
  exact (((poissonMLESequence_measurable hXm n).sub_const _).pow_const 2).const_mul _ |>.div_const _

/-- The plug-in-information Poisson Wald test is asymptotically level α.
The formula retains its totalized value on finite all-zero samples. -/
theorem poissonWald_null_size (hr : 0 < r) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => P.real {ω | distributionQuantile (chiSquared 1) (1 - α) <
      poissonWald ((n : ℝ) + 1) (poissonMLESequence X n ω) r}) atTop (𝓝 α) := by
  apply chiSquared_one_limit_rejection_size _ (poissonWald_limit hr hXm hX hind) hα
  intro n
  exact ((((poissonMLESequence_measurable hXm n).sub_const _).pow_const 2).const_mul _).div
    (poissonMLESequence_measurable hXm n)

/-- The Poisson LR test, including boundary empirical samples, is asymptotically level α. -/
theorem poissonLR_null_size (hr : 0 < r) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => P.real {ω | distributionQuantile (chiSquared 1) (1 - α) <
      poissonLR ((n : ℝ) + 1) (poissonMLESequence X n ω) r}) atTop (𝓝 α) := by
  apply chiSquared_one_limit_rejection_size _ (poissonLR_limit hr hXm hX hind) hα
  intro n
  have hm := poissonMLESequence_measurable hXm n
  exact (((hm.mul ((hm.div_const _).log)).sub hm).add_const _).const_mul _

/-- Direct calibration of the likelihood-ratio definition on the source's
positive parameter domain, as distinct from just a displayed algebraic formula. -/
theorem poisson_actual_likelihoodRatio_null_size (hr : 0 < r)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => P.real {ω | distributionQuantile (chiSquared 1) (1 - α) <
      -2 * Real.log (likelihoodRatio
        (fun (y : Fin (n + 1) → ℕ) (q : Ioi (0 : ℝ≥0)) => poissonSampleLikelihood y q)
        {(⟨r, hr⟩ : Ioi (0 : ℝ≥0))} (fun i => X i ω))}) atTop (𝓝 α) := by
  convert! poissonLR_null_size hr hXm hX hind hα using 1
  funext n
  congr 1
  ext ω
  simp only [mem_ofPred_eq]
  rw [poisson_positive_minus_two_log_likelihoodRatio (by omega : 0 < n + 1)]
  simp only [Nat.cast_add, Nat.cast_one, poissonMLESequence]

end IID
end LectureNotes
