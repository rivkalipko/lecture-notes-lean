import LectureNotes.ConditionalExpectation

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- L1 Theorem 6 with extended nonnegative risks: every measurable competitor
is allowed, including predictors whose squared error has infinite expectation. -/
theorem conditional_expectation_best_predictor_extended
    {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    {Y g : Ω → ℝ} (hY : MemLp Y 2 P) (hgm : StronglyMeasurable[m] g) :
    (∫⁻ ω, ENNReal.ofReal ((Y ω - P[Y | m] ω) ^ 2) ∂P) ≤
      ∫⁻ ω, ENNReal.ofReal ((Y ω - g ω) ^ 2) ∂P := by
  by_cases hfin : (∫⁻ ω, ENNReal.ofReal ((Y ω - g ω) ^ 2) ∂P) = ∞
  · rw [hfin]
    exact le_top
  have hdiffm : AEStronglyMeasurable (fun ω => Y ω - g ω) P :=
    hY.aestronglyMeasurable.sub (hgm.mono hm).aestronglyMeasurable
  have hdiffi : Integrable (fun ω => (Y ω - g ω) ^ 2) P :=
    ⟨hdiffm.pow 2, (hasFiniteIntegral_iff_ofReal
      (ae_of_all P (fun ω => sq_nonneg (Y ω - g ω)))).2 (lt_top_iff_ne_top.2 hfin)⟩
  have hdiff : MemLp (fun ω => Y ω - g ω) 2 P :=
    (memLp_two_iff_integrable_sq hdiffm).2 hdiffi
  have hg : MemLp g 2 P := by
    simpa only [Pi.sub_def, sub_sub_cancel] using hY.sub hdiff
  have hCE := hY.condExp (m := m) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hresi : Integrable (fun ω => (Y ω - P[Y | m] ω) ^ 2) P :=
    (hY.sub hCE).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hresi
    (ae_of_all P (fun _ => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hdiffi
      (ae_of_all P (fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (conditional_expectation_best_predictor P hm hY hg hgm)

end LectureNotes
