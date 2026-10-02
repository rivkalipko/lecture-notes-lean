import LectureNotes.Concentration

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- A finite collection of classifiers may share the same test set. Only
independence across observations within each classifier is required. -/
theorem classifier_accuracy_union_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n M : ℕ} (hn : 0 < n)
    {X : Fin M → Fin n → Ω → ℝ} {μ : Fin M → ℝ}
    (hX : ∀ j i, Integrable (X j i) P)
    (hb : ∀ j i, ∀ᵐ ω ∂P, X j i ω ∈ Icc (0 : ℝ) 1)
    (hm : ∀ j i, P[X j i] = μ j) (hi : ∀ j, iIndepFun (X j) P)
    {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ∃ j, ε ≤ |sampleMean (fun i => X j i ω) - μ j|} ≤
      2 * M * Real.exp (-2 * n * ε ^ 2) := by
  have h (j : Fin M) := hoeffding_sampleMean hn (by norm_num : (0 : ℝ) < 1)
    (hX j) (hb j) (hm j) (hi j) hε
  simp only [sub_zero, one_pow, div_one] at h
  have he : {ω | ∃ j, ε ≤ |sampleMean (fun i => X j i ω) - μ j|} =
      ⋃ j, {ω | ε ≤ |sampleMean (fun i => X j i ω) - μ j|} := by ext ω; simp
  rw [he]
  calc
    _ ≤ ∑ j, P.real {ω | ε ≤ |sampleMean (fun i => X j i ω) - μ j|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : Fin M, 2 * Real.exp (-2 * n * ε ^ 2) := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by simp; ring

/-- Solving the exponential union bound for the required sample size. -/
theorem classifier_budget_bound {n M : ℕ} (hM : 0 < M) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hn : Real.log (2 * M / δ) / (2 * ε ^ 2) ≤ (n : ℝ)) :
    2 * M * Real.exp (-2 * n * ε ^ 2) ≤ δ := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hlog : Real.log (2 * M / δ) ≤ 2 * n * ε ^ 2 := by
    have hh := (div_le_iff₀ (show 0 < 2 * ε ^ 2 by positivity)).mp hn
    nlinarith
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by positivity : 0 < 2 * (M : ℝ) / δ)] at he
  have hh := (div_le_iff₀ hδ).mp he
  calc
    _ = (2 * M) / Real.exp (2 * n * ε ^ 2) := by
      rw [show -2 * (n : ℝ) * ε ^ 2 = -(2 * n * ε ^ 2) by ring, Real.exp_neg]
      ring
    _ ≤ δ := (div_le_iff₀ (Real.exp_pos _)).mpr (by nlinarith)

/-- Simultaneous finite-sample accuracy guarantee from the displayed budget. -/
theorem classifier_accuracy_sample_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    {X : Fin M → Fin n → Ω → ℝ} {μ : Fin M → ℝ}
    (hX : ∀ j i, Integrable (X j i) P)
    (hb : ∀ j i, ∀ᵐ ω ∂P, X j i ω ∈ Icc (0 : ℝ) 1)
    (hm : ∀ j i, P[X j i] = μ j) (hi : ∀ j, iIndepFun (X j) P)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hbudget : Real.log (2 * M / δ) / (2 * ε ^ 2) ≤ (n : ℝ)) :
    P.real {ω | ∃ j, ε ≤ |sampleMean (fun i => X j i ω) - μ j|} ≤ δ :=
  (classifier_accuracy_union_bound hn hX hb hm hi hε).trans
    (classifier_budget_bound hM hε hδ hbudget)

/-- A rational Taylor lower bound for exp certifies the numerical budget;
there is no floating-point approximation in this proof. -/
theorem classifier_one_percent_budget :
    Real.log (2 / (1 / 100 : ℝ)) / (2 * (1 / 100 : ℝ) ^ 2) ≤ 26492 := by
  have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6623 / 1250) 20
  have h200 : (200 : ℝ) ≤ Real.exp (6623 / 1250) := by
    apply le_trans _ hsum
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hlog : Real.log (200 : ℝ) ≤ 6623 / 1250 :=
    (Real.log_le_iff_le_exp (by norm_num)).mpr h200
  norm_num at hlog ⊢
  linarith

/-- The source's single-classifier guarantee at 26,492 observations. -/
theorem classifier_one_percent_guarantee {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Fin 26492 → Ω → ℝ} {μ : ℝ}
    (hX : ∀ i, Integrable (X i) P)
    (hb : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc (0 : ℝ) 1)
    (hm : ∀ i, P[X i] = μ) (hi : iIndepFun X P) :
    P.real {ω | 1 / 100 ≤ |sampleMean (fun i => X i ω) - μ|} ≤ 1 / 100 := by
  have hh := classifier_accuracy_sample_size (by norm_num : 0 < 26492) (by norm_num : 0 < 1)
    (X := fun _ : Fin 1 => X) (μ := fun _ => μ) (fun _ => hX) (fun _ => hb)
    (fun _ => hm) (fun _ => hi) (by norm_num : (0 : ℝ) < 1 / 100)
    (by norm_num : (0 : ℝ) < 1 / 100)
    (by simpa using classifier_one_percent_budget)
  simpa using hh

end LectureNotes
