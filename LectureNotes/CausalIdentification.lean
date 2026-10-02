import LectureNotes.ConditionalExpectation
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.Integration

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped Classical

/-- Conditional independence gives the conditional product identity for
integrable real variables whose product is integrable. -/
theorem condIndep_condExp_mul {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfi : Integrable f P)
    (hgi : Integrable g P) (hfgi : Integrable (f * g) P)
    (hind : CondIndepFun m hm f g P) :
    P[f * g | m] =ᵐ[P] (fun ω => P[f | m] ω * P[g | m] ω) := by
  have hj := (condIndepFun_iff_map_prod_eq_prod_map_map hf hg).mp hind
  have hk : ∀ᵐ ω ∂P, IndepFun f g (condExpKernel P m ω) := by
    filter_upwards [ae_of_ae_trim hm hj] with ω hω
    apply (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mpr
    simpa only [Kernel.map_apply _ hf, Kernel.map_apply _ hg,
      Kernel.map_apply _ (hf.prodMk hg), Kernel.prod_apply] using hω
  filter_upwards [hk, condExp_ae_eq_integral_condExpKernel hm hfi,
    condExp_ae_eq_integral_condExpKernel hm hgi,
    condExp_ae_eq_integral_condExpKernel hm hfgi] with ω hi hfω hgω hfgω
  rw [hfgω, hfω, hgω]
  exact hi.integral_mul_eq_mul_integral hf.aestronglyMeasurable hg.aestronglyMeasurable

/-- Binary treatment-group indicator. -/
def treatmentIndicator {Ω : Type*} (D : Ω → Bool) (b : Bool) (ω : Ω) : ℝ :=
  if D ω = b then 1 else 0

theorem treatmentIndicator_measurable {Ω : Type*} [MeasurableSpace Ω]
    {D : Ω → Bool} (hD : Measurable D) (b : Bool) :
    Measurable (treatmentIndicator D b) := by
  unfold treatmentIndicator
  exact Measurable.ite ((measurableSet_singleton b).preimage hD)
    measurable_const measurable_const

theorem treatmentIndicator_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : Ω → Bool} (hD : Measurable D) (b : Bool) :
    Integrable (treatmentIndicator D b) P := by
  have he : treatmentIndicator D b = (D ⁻¹' {b}).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    simp [treatmentIndicator, Set.indicator_apply]
  rw [he]
  exact (integrable_const _).indicator ((measurableSet_singleton b).preimage hD)

theorem treatmentIndicator_mul_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {D : Ω → Bool} (hD : Measurable D) (b : Bool)
    {Y : Ω → ℝ} (hY : Integrable Y P) :
    Integrable (fun ω => Y ω * treatmentIndicator D b ω) P := by
  have he : (fun ω => Y ω * treatmentIndicator D b ω) = (D ⁻¹' {b}).indicator Y := by
    funext ω
    simp [treatmentIndicator, Set.indicator_apply, mul_ite]
  rw [he]
  exact hY.indicator ((measurableSet_singleton b).preimage hD)

/-- The conditional mean in treatment group b, expressed entirely using the
observable outcome and treatment. Overlap is required where this ratio is used. -/
def conditionalTreatmentMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : MeasurableSpace Ω) (D : Ω → Bool) (Y : Ω → ℝ) (b : Bool) : Ω → ℝ :=
  fun ω => P[fun ξ => Y ξ * treatmentIndicator D b ξ | m] ω / P[treatmentIndicator D b | m] ω

/-- Conditional unconfoundedness, observed/potential-outcome consistency in
one treatment group, and overlap identify that potential outcome's mean. -/
theorem treatment_conditional_mean_identification {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {D : Ω → Bool} (hD : Measurable D)
    {U Y : Ω → ℝ} (hU : Measurable U) (hUi : Integrable U P)
    (b : Bool) (hind : CondIndepFun m hm U D P)
    (hcons : ∀ᵐ ω ∂P, D ω = b → Y ω = U ω)
    (hoverlap : ∀ᵐ ω ∂P, P[treatmentIndicator D b | m] ω ≠ 0) :
    conditionalTreatmentMean P m D Y b =ᵐ[P] P[U | m] := by
  have hI : Measurable (fun d : Bool => if d = b then (1 : ℝ) else 0) := Measurable.of_discrete
  have hi : CondIndepFun m hm U (treatmentIndicator D b) P :=
    hind.comp measurable_id hI
  have hp := condIndep_condExp_mul hm hU (treatmentIndicator_measurable hD b) hUi
    (treatmentIndicator_integrable hD b) (treatmentIndicator_mul_integrable hD b hUi) hi
  have he : (fun ω => Y ω * treatmentIndicator D b ω) =ᵐ[P]
      (fun ω => U ω * treatmentIndicator D b ω) := by
    filter_upwards [hcons] with ω hω
    by_cases hb : D ω = b
    · simp [treatmentIndicator, hb, hω hb]
    · simp [treatmentIndicator, hb]
  have hce := condExp_congr_ae (m := m) he
  filter_upwards [hp, hce, hoverlap] with ω hpω heω hn
  unfold conditionalTreatmentMean
  rw [heω]
  change P[U * treatmentIndicator D b | m] ω / P[treatmentIndicator D b | m] ω = _
  rw [hpω, mul_div_cancel_right₀ _ hn]


/-- Average treatment effect in the potential-outcome model. -/
def averageTreatmentEffect {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U0 U1 : Ω → ℝ) : ℝ := ∫ ω, U1 ω - U0 ω ∂P

/-- Lecture 6, Remark 1: the average treatment effect equals the average
observable conditional treatment-group mean difference. The two potential
outcomes are integrable, treatment is conditionally unconfounded, the observed
outcome satisfies consistency, and both treatment groups have positive
conditional probability almost everywhere. -/
theorem averageTreatmentEffect_identification
    {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {D : Ω → Bool} (hD : Measurable D)
    {U0 U1 Y : Ω → ℝ} (hU0 : Measurable U0) (hU1 : Measurable U1)
    (hi0 : Integrable U0 P) (hi1 : Integrable U1 P)
    (hind0 : CondIndepFun m hm U0 D P) (hind1 : CondIndepFun m hm U1 D P)
    (hcons : ∀ᵐ ω ∂P, Y ω = if D ω = true then U1 ω else U0 ω)
    (hov0 : ∀ᵐ ω ∂P, 0 < P[treatmentIndicator D false | m] ω)
    (hov1 : ∀ᵐ ω ∂P, 0 < P[treatmentIndicator D true | m] ω) :
    Integrable (fun ω => conditionalTreatmentMean P m D Y true ω -
      conditionalTreatmentMean P m D Y false ω) P ∧
    averageTreatmentEffect P U0 U1 =
      ∫ ω, conditionalTreatmentMean P m D Y true ω -
        conditionalTreatmentMean P m D Y false ω ∂P := by
  have hc0 : ∀ᵐ ω ∂P, D ω = false → Y ω = U0 ω := by
    filter_upwards [hcons] with ω hω hd
    simpa [hd] using hω
  have hc1 : ∀ᵐ ω ∂P, D ω = true → Y ω = U1 ω := by
    filter_upwards [hcons] with ω hω hd
    simpa [hd] using hω
  have he0 := treatment_conditional_mean_identification hm hD hU0 hi0 false
    hind0 hc0 (hov0.mono fun _ h => ne_of_gt h)
  have he1 := treatment_conditional_mean_identification hm hD hU1 hi1 true
    hind1 hc1 (hov1.mono fun _ h => ne_of_gt h)
  have he : (fun ω => conditionalTreatmentMean P m D Y true ω -
      conditionalTreatmentMean P m D Y false ω) =ᵐ[P]
      (fun ω => P[U1 | m] ω - P[U0 | m] ω) := he1.sub he0
  constructor
  · exact (integrable_condExp.sub integrable_condExp).congr he.symm
  · rw [averageTreatmentEffect, integral_congr_ae he,
      integral_sub integrable_condExp integrable_condExp,
      integral_condExp hm, integral_condExp hm, integral_sub hi1 hi0]

end LectureNotes
