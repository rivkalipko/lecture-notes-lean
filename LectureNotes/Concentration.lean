import LectureNotes.Inequalities

/-! L3 Hoeffding's lemma and concentration for independent bounded variables. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Real
open scoped NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem hoeffding_lemma {X : Ω → ℝ} {a b : ℝ} (hm : AEMeasurable X P)
    (hb : ∀ᵐ ω ∂P, X ω ∈ Set.Icc a b) (hc : P[X] = 0) (t : ℝ) :
    (∫ ω, exp (t * X ω) ∂P) ≤ exp (t ^ 2 * (b - a) ^ 2 / 8) := by
  have h := (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hc).mgf_le t
  convert h using 1
  congr 1
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
    Real.norm_eq_abs, div_pow, sq_abs]
  ring

/-- Two-tail Chernoff bound. It combines the one-tail bounds for X and -X. -/
theorem subgaussian_two_sided {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c P) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ |X ω|} ≤ 2 * exp (-ε ^ 2 / (2 * c)) := by
  have hs : {ω | ε ≤ |X ω|} = {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [hs]
  have h1 := hX.measure_ge_le hε
  have h2 := hX.neg.measure_ge_le hε
  have hu := measureReal_union_le (μ := P) {ω | ε ≤ X ω} {ω | ε ≤ -X ω}
  change P.real {ω | ε ≤ -X ω} ≤ _ at h2
  linarith

/-- Independent bounded centered observations; no identical-distribution
assumption is necessary. This sum form is equivalent to the sample-mean bound. -/
theorem hoeffding_sum {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    {a b : ℝ} (hab : a < b)
    (hm : ∀ i, AEMeasurable (X i) P)
    (hb : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc a b)
    (hc : ∀ i, P[X i] = 0) (hind : iIndepFun X P)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ |∑ i, X i ω|} ≤
      2 * exp (-(2 * ε ^ 2) / (n * (b - a) ^ 2)) := by
  have hs := HasSubgaussianMGF.sum_of_iIndepFun hind
    (s := Finset.univ) (fun i _ =>
      hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hm i) (hb i) (hc i))
  have h := subgaussian_two_sided hs hε
  convert h using 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs, div_pow, sq_abs]
  congr 2
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hab' : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  field_simp

/-- L3 Theorem 5 in the displayed sample-mean form. -/
theorem hoeffding_sampleMean {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    {a b μ : ℝ} (hab : a < b) (hX : ∀ i, Integrable (X i) P)
    (hb : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc a b)
    (hμ : ∀ i, P[X i] = μ) (hind : iIndepFun X P) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |sampleMean (fun i => X i ω) - μ|} ≤
      2 * exp (-2 * n * ε ^ 2 / (b - a) ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := hoeffding_sum hn (X := fun i ω => X i ω - μ)
    (a := a - μ) (b := b - μ) (by linarith)
    (fun i => (hX i).aemeasurable.sub_const μ)
    (fun i => (hb i).mono (fun ω hω => ⟨by linarith [hω.1], by linarith [hω.2]⟩))
    (fun i => by rw [integral_sub (hX i) (integrable_const μ), hμ i]; simp)
    (hind.comp (fun _ x => x - μ) (fun _ => by fun_prop))
    (ε := n * ε) (by positivity)
  have he (ω) : (n : ℝ) * ε ≤ |∑ i, (X i ω - μ)| ↔
      ε ≤ |sampleMean (fun i => X i ω) - μ| := by
    have hid : (∑ i, (X i ω - μ)) =
        (n : ℝ) * (sampleMean (fun i => X i ω) - μ) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, sampleMean]
      field_simp
    rw [hid, abs_mul, abs_of_pos hn']
    exact mul_le_mul_iff_right₀ hn'
  simp only [he] at hs
  convert! hs using 1
  congr 2
  have hab' : b - a ≠ 0 := by linarith
  rw [show b - μ - (a - μ) = b - a by ring]
  field_simp
  <;> ring
end LectureNotes
