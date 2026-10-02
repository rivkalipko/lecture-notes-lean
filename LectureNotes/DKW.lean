import LectureNotes.DKWUniform
import LectureNotes.DKWQuantileCoupling

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

/-- The sharp Dvoretzky–Kiefer–Wolfowitz inequality for the actual uniform
CDF error of an IID sample. Arbitrary real laws, including atoms, are allowed. -/
theorem dkw_inequality {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) μ P)
    {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε < empiricalCDFSupError μ (fun i => X i ω)} ≤
      2 * Real.exp (-2 * n * ε ^ 2) := by
  have h := ENNReal.toReal_mono (measure_ne_top (dkwProductLaw n) _)
    (iid_empiricalCDFSupError_le_uniform μ X hX hind hlaw ε)
  exact h.trans (dkw_uniform_two_sided_bound hn hε)

/-- Canonical product-law form of the same inequality. -/
theorem dkw_product_inequality (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin n => μ)).real {x | ε < empiricalCDFSupError μ x} ≤
      2 * Real.exp (-2 * n * ε ^ 2) := by
  have h := ENNReal.toReal_mono (measure_ne_top (dkwProductLaw n) _)
    (empiricalCDFSupError_quantile_event_le μ n ε)
  exact h.trans (dkw_uniform_two_sided_bound hn hε)

/-- A lower-CDF deviation event is contained in the two-sided supremum
event, so it inherits the same exponential upper bound. -/
theorem dkw_lower_deviation_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) μ P)
    {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ∃ t : ℝ, ε < cdf μ t - empiricalCDF (fun i => X i ω) t} ≤
      2 * Real.exp (-2 * n * ε ^ 2) := by
  apply (measureReal_mono (show {ω | ∃ t : ℝ, ε < cdf μ t - empiricalCDF (fun i => X i ω) t} ⊆
    {ω | ε < empiricalCDFSupError μ (fun i => X i ω)} from ?_)).trans
      (dkw_inequality μ hn X hX hind hlaw hε)
  rintro ω ⟨t, ht⟩
  apply ht.trans_le
  have h := le_csSup (empiricalCDF_error_bddAbove μ (fun i => X i ω)) (mem_range_self t)
  simpa only [empiricalCDFSupError, neg_sub] using (neg_le_abs (empiricalCDF (fun i => X i ω) t - cdf μ t)).trans h

end LectureNotes
