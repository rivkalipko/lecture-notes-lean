import LectureNotes.BernsteinAnalytic

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped Topology ENNReal NNReal

/-- Independence multiplies the variance-sensitive MGF bounds. -/
theorem bernstein_sum_mgf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : ∀ i, MemLp (X i) 2 P)
    {M v t : ℝ} (hM : 0 ≤ M) (hb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ M)
    (hm : ∀ i, P[X i] = 0) (hv : ∀ i, Var[X i; P] = v)
    (hind : iIndepFun X P) (ht : 0 ≤ t) (htM : t * M < 3) :
    mgf (fun ω => ∑ i, X i ω) P t ≤ exp (n * v * t ^ 2 / (2 * (1 - t * M / 3))) := by
  have he : mgf (fun ω => ∑ i, X i ω) P t = ∏ i, mgf (X i) P t := by
    convert hind.mgf_sum hXm Finset.univ (t := t) using 1
    congr 1
    funext ω
    simp
  rw [he]
  calc
    _ ≤ ∏ i : Fin n, exp (t ^ 2 * v / (2 * (1 - t * M / 3))) := by
      apply Finset.prod_le_prod (fun _ _ => mgf_nonneg)
      intro i _
      simpa only [hv i] using bernstein_mgf_bound (hX i) hM (hb i) (hm i) ht htM
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
      congr 1
      ring

/-- One-sided Bernstein for centered independent observations with common
variance, obtained by optimizing the Chernoff parameter. -/
theorem bernstein_sum_upper_pos_variance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, MemLp (X i) 2 P)
    {M v ε : ℝ} (hM : 0 ≤ M) (hb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ M)
    (hm : ∀ i, P[X i] = 0) (hv : ∀ i, Var[X i; P] = v) (hvpos : 0 < v)
    (hind : iIndepFun X P) (hε : 0 < ε) :
    P.real {ω | ε ≤ ∑ i, X i ω} ≤ exp (-ε ^ 2 / (2 * n * v + (2 / 3) * M * ε)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let t := ε / ((n : ℝ) * v + M * ε / 3)
  have hd : 0 < (n : ℝ) * v + M * ε / 3 := by positivity
  have ht : 0 < t := div_pos hε hd
  have htM : t * M < 3 := by
    dsimp only [t]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    nlinarith [mul_pos hnR hvpos]
  have hden : 0 < 1 - t * M / 3 := by linarith
  have hsumM : ∀ᵐ ω ∂P, (∑ i, X i ω) ≤ (n : ℝ) * M := by
    filter_upwards [ae_all_iff.mpr hb] with ω hω
    calc
      _ ≤ ∑ _i : Fin n, M := Finset.sum_le_sum (fun i _ => (le_abs_self _).trans (hω i))
      _ = _ := by simp
  have hI := integrable_exp_mul_of_le t ((n : ℝ) * M) ht.le (by fun_prop) hsumM
  calc
    _ ≤ exp (-t * ε) * mgf (fun ω => ∑ i, X i ω) P t :=
      measure_ge_le_exp_mul_mgf ε ht.le hI
    _ ≤ exp (-t * ε) * exp (n * v * t ^ 2 / (2 * (1 - t * M / 3))) :=
      mul_le_mul_of_nonneg_left (bernstein_sum_mgf hXm hX hM hb hm hv hind ht.le htM) (exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [t] at *
      field_simp
      <;> ring

/-- Bernstein's two-sided centered-sum inequality includes zero variance. -/
theorem bernstein_sum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    {M v ε : ℝ} (hM : 0 ≤ M) (hb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ M)
    (hm : ∀ i, P[X i] = 0) (hv : ∀ i, Var[X i; P] = v)
    (hind : iIndepFun X P) (hε : 0 < ε) :
    P.real {ω | ε ≤ |∑ i, X i ω|} ≤ 2 * exp (-ε ^ 2 / (2 * n * v + (2 / 3) * M * ε)) := by
  have hX i : MemLp (X i) 2 P :=
    MemLp.of_bound (hXm i).aestronglyMeasurable M (by simpa only [Real.norm_eq_abs] using hb i)
  have hv0 : 0 ≤ v := by rw [← hv ⟨0, hn⟩]; exact variance_nonneg _ _
  rcases hv0.eq_or_lt with hvzero | hvpos
  · have hz i : ∀ᵐ ω ∂P, X i ω = 0 := by
      filter_upwards [zero_variance_is_constant P (hX i) ((hv i).trans hvzero.symm)] with ω hω
      exact hω.trans (hm i)
    have he : {ω | ε ≤ |∑ i, X i ω|} =ᵐ[P] (∅ : Set Ω) := by
      filter_upwards [ae_all_iff.mpr hz] with ω hω
      apply propext
      change (ε ≤ |∑ i, X i ω|) ↔ False
      simp [hω, hε.not_ge]
    rw [measureReal_congr he, measureReal_empty]
    positivity
  · have h₁ := bernstein_sum_upper_pos_variance hn hXm hX hM hb hm hv hvpos hind hε
    have h₂ := bernstein_sum_upper_pos_variance hn (X := fun i ω => -X i ω)
      (fun i => (hXm i).neg) (fun i => (hX i).neg) hM
      (fun i => by simpa only [abs_neg] using hb i)
      (fun i => by rw [integral_neg, hm i, neg_zero])
      (fun i => by
        change Var[-X i; P] = v
        rw [variance_neg, hv i]) hvpos
      (hind.comp (fun _ x => -x) (fun _ => measurable_neg)) hε
    have he : {ω | ε ≤ |∑ i, X i ω|} =
        {ω | ε ≤ ∑ i, X i ω} ∪ {ω | ε ≤ ∑ i, -X i ω} := by
      ext ω
      simp only [mem_ofPred_eq, mem_union, Finset.sum_neg_distrib, le_abs]
    rw [he]
    exact (measureReal_union_le _ _).trans (by linarith)

/-- L3 Remark 1, with the exact printed variance and range constants.
The common variance can be zero; no identical-distribution assumption is needed. -/
theorem bernstein_sampleMean {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    {a b μ v ε : ℝ} (hab : a < b)
    (hb : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc a b)
    (hμ : ∀ i, P[X i] = μ) (hv : ∀ i, Var[X i; P] = v)
    (hind : iIndepFun X P) (hε : 0 < ε) :
    P.real {ω | ε ≤ |sampleMean (fun i => X i ω) - μ|} ≤
      2 * exp (-(n : ℝ) * ε ^ 2 / (2 * v + (2 / 3) * (b - a) * ε)) := by
  have hX i : MemLp (X i) 2 P := memLp_of_bounded (hb i) (hXm i).aestronglyMeasurable 2
  have hI i := (hX i).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have haμ : a ≤ μ := by
    have hh := integral_mono_ae (integrable_const a) (hI ⟨0, hn⟩) ((hb ⟨0, hn⟩).mono (fun _ h => h.1))
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, hμ] using hh
  have hμb : μ ≤ b := by
    have hh := integral_mono_ae (hI ⟨0, hn⟩) (integrable_const b) ((hb ⟨0, hn⟩).mono (fun _ h => h.2))
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, hμ] using hh
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := bernstein_sum hn (X := fun i ω => X i ω - μ)
    (fun i => (hXm i).sub_const μ) (sub_nonneg.mpr hab.le)
    (fun i => (hb i).mono (fun ω hω => abs_le.mpr ⟨by linarith [hω.1], by linarith [hω.2]⟩))
    (fun i => by rw [integral_sub (hI i) (integrable_const μ), hμ i]; simp)
    (fun i => by rw [variance_sub_const (hXm i).aestronglyMeasurable, hv i])
    (hind.comp (fun _ x => x - μ) (fun _ => by fun_prop)) (mul_pos hnR hε)
  have he (ω) : (n : ℝ) * ε ≤ |∑ i, (X i ω - μ)| ↔
      ε ≤ |sampleMean (fun i => X i ω) - μ| := by
    have hid : (∑ i, (X i ω - μ)) = (n : ℝ) * (sampleMean (fun i => X i ω) - μ) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, sampleMean]
      field_simp
    rw [hid, abs_mul, abs_of_pos hnR]
    exact mul_le_mul_iff_right₀ hnR
  simp only [he] at hh
  convert! hh using 1
  congr 2
  field_simp
  <;> ring

/-- An explicit range of deviations where the Bernstein upper bound is no
larger than the Hoeffding upper bound. Small variance alone does not compare
the bounds for every deviation. -/
theorem bernstein_bound_le_hoeffding {n M v ε : ℝ}
    (hn : 0 ≤ n) (hM : 0 < M) (hv : 0 ≤ v) (hε : 0 < ε)
    (hbetter : 2 * v + (2 / 3) * M * ε ≤ M ^ 2 / 2) :
    2 * exp (-n * ε ^ 2 / (2 * v + (2 / 3) * M * ε)) ≤
      2 * exp (-2 * n * ε ^ 2 / M ^ 2) := by
  have hd : 0 < 2 * v + (2 / 3) * M * ε := by positivity
  have hM2 : 0 < M ^ 2 := sq_pos_of_pos hM
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  rw [div_le_div_iff₀ hd hM2]
  nlinarith [mul_nonneg (mul_nonneg hn (sq_nonneg ε))
    (sub_nonneg.mpr hbetter)]

end LectureNotes
