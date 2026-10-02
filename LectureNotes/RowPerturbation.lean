import LectureNotes.RowStudentization
import LectureNotes.BootstrapVarianceConsistency

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- Markov's inequality for absolute error, in real-valued probability form. -/
theorem measureReal_abs_ge_le_firstMoment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : Integrable Y P) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |Y ω|} ≤ (∫ ω, |Y ω| ∂P) / ε := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (fun ω => abs_nonneg (Y ω))) hY.abs ε
  exact (le_div_iff₀ hε).mpr (by nlinarith)

/-- Small deterministic coefficients multiplying a random variable and its
square vanish in row probability whenever its second moments converge. -/
theorem row_small_polynomial_probability {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {Y : ∀ n, Ω n → ℝ}
    (hY : ∀ n, MemLp (Y n) 2 (P n)) {a b : ℕ → ℝ} {v : ℝ}
    (hM : Tendsto (fun n => ∫ ω, Y n ω ^ 2 ∂P n) atTop (𝓝 v))
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (P n).real
      {ω | ε ≤ |a n * Y n ω + b n * Y n ω ^ 2|}) atTop (𝓝 0) := by
  intro ε hε
  have hbound n : (∫ ω, |a n * Y n ω + b n * Y n ω ^ 2| ∂P n) ≤
      |a n| * (1 + ∫ ω, Y n ω ^ 2 ∂P n) + |b n| * (∫ ω, Y n ω ^ 2 ∂P n) := by
    have hi : Integrable (fun ω => a n * Y n ω + b n * Y n ω ^ 2) (P n) :=
      (((hY n).integrable (by norm_num)).const_mul _).add ((hY n).integrable_sq.const_mul _)
    have hh : Integrable (fun ω => |a n| * (1 + Y n ω ^ 2) + |b n| * Y n ω ^ 2) (P n) :=
      (((integrable_const 1).add (hY n).integrable_sq).const_mul _).add
        ((hY n).integrable_sq.const_mul _)
    have hm := integral_mono hi.abs hh (fun ω => show
        |a n * Y n ω + b n * Y n ω ^ 2| ≤
          |a n| * (1 + Y n ω ^ 2) + |b n| * Y n ω ^ 2 from by
      calc
        _ ≤ |a n * Y n ω| + |b n * Y n ω ^ 2| := abs_add_le _ _
        _ = |a n| * |Y n ω| + |b n| * Y n ω ^ 2 := by
          simp only [abs_mul, abs_pow, sq_abs]
        _ ≤ _ := by
          gcongr
          nlinarith [sq_nonneg (|Y n ω| - 1), sq_abs (Y n ω)])
    have hia : Integrable (fun ω => |a n| * (1 + Y n ω ^ 2)) (P n) :=
      ((integrable_const 1).add (hY n).integrable_sq).const_mul _
    have hib : Integrable (fun ω => |b n| * Y n ω ^ 2) (P n) := (hY n).integrable_sq.const_mul _
    have hI : (∫ ω, 1 + Y n ω ^ 2 ∂P n) = 1 + ∫ ω, Y n ω ^ 2 ∂P n := by
      simpa only [Pi.add_apply, integral_const, probReal_univ, smul_eq_mul, one_mul] using!
        integral_add (integrable_const (1 : ℝ)) (hY n).integrable_sq
    rw [integral_add hia hib, integral_const_mul, integral_const_mul, hI] at hm
    exact hm
  have hp : Tendsto
      (fun n => (|a n| * (1 + ∫ ω, Y n ω ^ 2 ∂P n) +
        |b n| * (∫ ω, Y n ω ^ 2 ∂P n)) / ε) atTop (𝓝 0) := by
    convert! ((ha.abs.mul (tendsto_const_nhds.add hM)).add (hb.abs.mul hM)).div_const ε using 1
    simp
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hp
  intro n
  exact (measureReal_abs_ge_le_firstMoment
    ((((hY n).integrable (by norm_num)).const_mul _).add ((hY n).integrable_sq.const_mul _)) hε).trans
      ((div_le_div_iff_of_pos_right hε).mpr (hbound n))

/-- Finite-sample CDF bounds after an additive error. -/
theorem additive_error_cdf_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y R : Ω → ℝ)
    (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    P.real {ω | Y ω ≤ t - δ} - P.real {ω | δ ≤ |R ω|} ≤
        P.real {ω | Y ω + R ω ≤ t} ∧
    P.real {ω | Y ω + R ω ≤ t} ≤
        P.real {ω | Y ω ≤ t + δ} + P.real {ω | δ ≤ |R ω|} := by
  constructor
  · have hsub : {ω | Y ω ≤ t - δ} ⊆
        {ω | Y ω + R ω ≤ t} ∪ {ω | δ ≤ |R ω|} := by
      intro ω hω
      by_cases hb : δ ≤ |R ω|
      · exact Or.inr hb
      · have hh := (abs_lt.mp (lt_of_not_ge hb)).2
        exact Or.inl (by change Y ω ≤ t - δ at hω; change Y ω + R ω ≤ t; linarith)
    have hh := (measureReal_mono (μ := P) hsub).trans (measureReal_union_le (μ := P) _ _)
    linarith
  · have hsub : {ω | Y ω + R ω ≤ t} ⊆
        {ω | Y ω ≤ t + δ} ∪ {ω | δ ≤ |R ω|} := by
      intro ω hω
      by_cases hb : δ ≤ |R ω|
      · exact Or.inr hb
      · have hh := (abs_lt.mp (lt_of_not_ge hb)).1
        exact Or.inl (by change Y ω + R ω ≤ t at hω; change Y ω ≤ t + δ; linarith)
    exact (measureReal_mono (μ := P) hsub).trans (measureReal_union_le (μ := P) _ _)

/-- Slutsky's additive-error principle for varying row spaces and row laws,
expressed by CDFs so no artificial coupling between rows is needed. -/
theorem dependent_rows_additive_error_cdf {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (Y R : ∀ n, Ω n → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hY : ∀ t, Tendsto (fun n => (P n).real {ω | Y n ω ≤ t}) atTop (𝓝 (cdf ν t)))
    (hR : ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ |R n ω|}) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n => (P n).real {ω | Y n ω + R n ω ≤ t}) atTop (𝓝 (cdf ν t)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hc : ContinuousAt (fun δ : ℝ => cdf ν (t - δ)) 0 :=
      (continuous_cdf_of_atomless ν).continuousAt.comp (by fun_prop)
    have hc' : Tendsto (fun δ : ℝ => cdf ν (t - δ)) (𝓝 0) (𝓝 (cdf ν t)) := by
      simpa using hc.tendsto
    have he := hc'.eventually (lt_mem_nhds ha)
    have hs : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ a < cdf ν (t - δ) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds he] with δ hδ0 hδ
      exact ⟨hδ0, hδ⟩
    obtain ⟨δ, hδ0, hδ⟩ := hs.exists
    have hl := (hY (t - δ)).sub (hR δ hδ0)
    simp only [sub_zero] at hl
    filter_upwards [hl.eventually (lt_mem_nhds hδ)] with n hn
    exact hn.trans_le (additive_error_cdf_bounds (P n) (Y n) (R n) t hδ0).1
  · intro b hb
    have hc : ContinuousAt (fun δ : ℝ => cdf ν (t + δ)) 0 :=
      (continuous_cdf_of_atomless ν).continuousAt.comp (by fun_prop)
    have hc' : Tendsto (fun δ : ℝ => cdf ν (t + δ)) (𝓝 0) (𝓝 (cdf ν t)) := by
      simpa using hc.tendsto
    have he := hc'.eventually (gt_mem_nhds hb)
    have hs : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ cdf ν (t + δ) < b := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds he] with δ hδ0 hδ
      exact ⟨hδ0, hδ⟩
    obtain ⟨δ, hδ0, hδ⟩ := hs.exists
    have hl := (hY (t + δ)).add (hR δ hδ0)
    simp only [add_zero] at hl
    filter_upwards [hl.eventually (gt_mem_nhds hδ)] with n hn
    exact ((additive_error_cdf_bounds (P n) (Y n) (R n) t hδ0).2).trans_lt hn

end LectureNotes
