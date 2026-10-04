import LectureNotes.CausalIdentification
import Mathlib.MeasureTheory.Function.FactorsThrough

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped Classical

/-- The propensity score is the conditional probability of binary treatment,
conditioned on the observed covariates. This version is a function on the
sample space, measurable with respect to the covariates. -/
def propensityScore {Ω S : Type*} [MeasurableSpace Ω] [mS : MeasurableSpace S]
    (P : Measure Ω) (D : Ω → Bool) (X : Ω → S) : Ω → ℝ :=
  P[treatmentIndicator D true | mS.comap X]

/-- A propensity-score version is a measurable function of the covariate
value, with no additional regularity or overlap assumption. -/
theorem propensityScore_factors {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (D : Ω → Bool) (X : Ω → S) :
    ∃ e : S → ℝ, Measurable e ∧ propensityScore P D X = e ∘ X := by
  exact (stronglyMeasurable_condExp (μ := P) (f := treatmentIndicator D true)
    (m := ‹MeasurableSpace S›.comap X)).measurable.exists_eq_measurable_comp

/-- Conditional treatment probabilities lie between zero and one almost surely. -/
theorem propensityScore_mem_Icc {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : Ω → Bool} {X : Ω → S}
    (hD : Measurable D) (hX : Measurable X) :
    ∀ᵐ ω ∂P, propensityScore P D X ω ∈ Icc (0 : ℝ) 1 := by
  have hl : (0 : Ω → ℝ) ≤ᵐ[P] P[treatmentIndicator D true | ‹MeasurableSpace S›.comap X] :=
    condExp_nonneg (ae_of_all _ (fun ω => by unfold treatmentIndicator; split_ifs <;> norm_num))
  have hu := condExp_mono (m := ‹MeasurableSpace S›.comap X)
    (treatmentIndicator_integrable hD true) (integrable_const (1 : ℝ))
    (ae_of_all P (fun ω => show treatmentIndicator D true ω ≤ 1 by
      unfold treatmentIndicator; split_ifs <;> norm_num))
  rw [condExp_const hX.comap_le] at hu
  filter_upwards [hl, hu] with ω hω hω'
  exact ⟨hω, hω'⟩

private theorem indicator_one_mul {Ω : Type*} (s : Set Ω) (f : Ω → ℝ) :
    f * s.indicator 1 = s.indicator f := by
  ext ω
  by_cases h : ω ∈ s <;> simp [h]

/-- If a conditional event probability at the finer information level is
already measurable at the coarser level, its event is conditionally independent
of every finer measurable event, given the coarser information. -/
theorem conditional_event_factor_of_measurable
    {Ω : Type*} {m M : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hmM : m ≤ M) (hM : M ≤ mΩ)
    {s t : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet[M] t)
    (he : AEStronglyMeasurable[m] (P⟦s | M⟧) P) :
    P⟦s ∩ t | m⟧ =ᵐ[P] P⟦s | m⟧ * P⟦t | m⟧ := by
  have hm := hmM.trans hM
  have hi : Integrable (s.indicator (1 : Ω → ℝ)) P := (integrable_const _).indicator hs
  have htI : Integrable (t.indicator (1 : Ω → ℝ)) P := (integrable_const _).indicator (hM _ ht)
  have hprod : Integrable ((P⟦s | M⟧) * t.indicator (1 : Ω → ℝ)) P := by
    rw [indicator_one_mul]
    exact integrable_condExp.indicator (hM _ ht)
  have hinner : P⟦s ∩ t | M⟧ =ᵐ[P] (P⟦s | M⟧) * t.indicator (1 : Ω → ℝ) := by
    rw [indicator_one_mul]
    have hset : (s ∩ t).indicator (fun _ : Ω => (1 : ℝ)) = t.indicator (s.indicator 1) := by
      ext ω
      by_cases hs : ω ∈ s <;> by_cases ht : ω ∈ t <;> simp [hs, ht]
    rw [hset]
    exact condExp_indicator hi ht
  have hsmall : P⟦s | M⟧ =ᵐ[P] P⟦s | m⟧ :=
    (condExp_of_aestronglyMeasurable' hm he integrable_condExp).symm.trans
      (condExp_condExp_of_le hmM hM)
  calc
    P⟦s ∩ t | m⟧ =ᵐ[P] P[P⟦s ∩ t | M⟧ | m] :=
      (condExp_condExp_of_le hmM hM).symm
    _ =ᵐ[P] P[(P⟦s | M⟧) * t.indicator (1 : Ω → ℝ) | m] := condExp_congr_ae hinner
    _ =ᵐ[P] (P⟦s | M⟧) * P⟦t | m⟧ :=
      condExp_mul_of_aestronglyMeasurable_left he hprod htI
    _ =ᵐ[P] P⟦s | m⟧ * P⟦t | m⟧ := hsmall.mul (Filter.EventuallyEq.refl _ _)

/-- For binary treatment, the conditional probabilities of all treatment
subsets are measurable whenever the conditional probability of treatment is.
This includes empty/full subsets and the complementary untreated event. -/
theorem binary_conditional_events_measurable
    {Ω : Type*} {m M : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : Ω → Bool}
    (hM : M ≤ mΩ) (hD : Measurable D)
    (he : AEStronglyMeasurable[m] (P[treatmentIndicator D true | M]) P)
    (s : Set Bool) : AEStronglyMeasurable[m] (P⟦D ⁻¹' s | M⟧) P := by
  have htrue : (D ⁻¹' {true}).indicator (fun _ : Ω => (1 : ℝ)) = treatmentIndicator D true := by
    ext ω
    simp [treatmentIndicator, Set.indicator_apply]
  have hfalse : (D ⁻¹' {false}).indicator (fun _ : Ω => (1 : ℝ)) = 1 - treatmentIndicator D true := by
    ext ω
    cases hd : D ω <;> simp [hd, treatmentIndicator]
  by_cases ht : true ∈ s <;> by_cases hf : false ∈ s
  · have hs : s = univ := by ext b; cases b <;> simp [ht, hf]
    simp only [hs, preimage_univ, indicator_univ]
    rw [condExp_const hM]
    exact stronglyMeasurable_const.aestronglyMeasurable
  · have hs : s = {true} := by ext b; cases b <;> simp [ht, hf]
    simpa only [hs, htrue] using he
  · have hs : s = {false} := by ext b; cases b <;> simp [ht, hf]
    rw [hs, hfalse]
    have hc := condExp_sub (μ := P) (integrable_const (1 : ℝ))
      (treatmentIndicator_integrable hD true) M
    rw [condExp_const hM] at hc
    exact (stronglyMeasurable_const.aestronglyMeasurable.sub he).congr hc.symm
  · have hs : s = ∅ := by ext b; cases b <;> simp [ht, hf]
    simp only [hs, preimage_empty, indicator_empty]
    change AEStronglyMeasurable[m] (P[(0 : Ω → ℝ) | M]) P
    rw [condExp_zero]
    exact stronglyMeasurable_zero.aestronglyMeasurable

/-- A covariate coarsening that retains the propensity score balances treatment
and covariates. Treatment may have conditional probability zero or one. -/
theorem propensityScore_balancing_of_measurable
    {Ω S : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] [mS : MeasurableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : Ω → Bool} {X : Ω → S}
    (hD : Measurable D) (hX : Measurable X) (hmX : m ≤ mS.comap X)
    (he : AEStronglyMeasurable[m] (propensityScore P D X) P) :
    CondIndepFun m (hmX.trans hX.comap_le) D X P := by
  apply (condIndepFun_iff_condExp_inter_preimage_eq_mul hD hX).mpr
  intro s t hs ht
  exact conditional_event_factor_of_measurable hmX hX.comap_le (hD hs)
    ⟨t, ht, rfl⟩ (binary_conditional_events_measurable hX.comap_le hD he s)

/-- L5 Remark 1: the propensity score itself balances binary treatment and
all observed covariates. No overlap assumption is needed for balancing. -/
theorem propensityScore_balancing
    {Ω S : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mS : MeasurableSpace S] {P : Measure Ω} [IsProbabilityMeasure P]
    {D : Ω → Bool} {X : Ω → S} (hD : Measurable D) (hX : Measurable X) :
    CondIndepFun ((borel ℝ).comap (propensityScore P D X))
      ((stronglyMeasurable_condExp.measurable.comap_le).trans hX.comap_le) D X P := by
  apply propensityScore_balancing_of_measurable hD hX
    stronglyMeasurable_condExp.measurable.comap_le
  exact (comap_measurable (propensityScore P D X)).stronglyMeasurable.aestronglyMeasurable

/-- Conditional independence under a covariate coarsening identifies the
conditional treatment probability there with the full propensity score. -/
theorem propensityScore_eq_condExp_of_balancing
    {Ω S : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] [mS : MeasurableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : Ω → Bool} {X : Ω → S}
    (hD : Measurable D) (hX : Measurable X) (hmX : m ≤ mS.comap X)
    (hind : CondIndepFun m (hmX.trans hX.comap_le) D X P) :
    propensityScore P D X =ᵐ[P] P[treatmentIndicator D true | m] := by
  have hm := hmX.trans hX.comap_le
  have htrue : (D ⁻¹' {true}).indicator (fun _ : Ω => (1 : ℝ)) = treatmentIndicator D true := by
    ext ω
    simp [treatmentIndicator, Set.indicator_apply]
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le
    (treatmentIndicator_integrable hD true)
    (fun _ _ _ => integrable_condExp.integrableOn) _
    (stronglyMeasurable_condExp.mono hmX).aestronglyMeasurable
  intro t ht _
  have hCI := (condIndepFun_iff m hm D X hD hX P).mp hind
    (D ⁻¹' {true}) t ⟨{true}, measurableSet_singleton _, rfl⟩ ht
  rw [htrue] at hCI
  have hprod : Integrable ((P[treatmentIndicator D true | m]) * t.indicator (1 : Ω → ℝ)) P := by
    rw [indicator_one_mul]
    exact integrable_condExp.indicator (hX.comap_le _ ht)
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (stronglyMeasurable_condExp (μ := P) (m := m) (f := treatmentIndicator D true)) hprod
    ((integrable_const _).indicator (hX.comap_le _ ht))
  have hset : (D ⁻¹' {true} ∩ t).indicator (1 : Ω → ℝ) = t.indicator (treatmentIndicator D true) := by
    rw [← htrue]
    ext ω
    by_cases hd : D ω = true <;> by_cases ht : ω ∈ t <;> simp [hd, ht]
  calc
    (∫ ω in t, P[treatmentIndicator D true | m] ω ∂P) =
        ∫ ω, ((P[treatmentIndicator D true | m]) * t.indicator (1 : Ω → ℝ)) ω ∂P := by
      rw [indicator_one_mul, integral_indicator (hX.comap_le _ ht)]
    _ = ∫ ω, P[((P[treatmentIndicator D true | m]) * t.indicator (1 : Ω → ℝ)) | m] ω ∂P :=
      (integral_condExp hm).symm
    _ = ∫ ω, (P[treatmentIndicator D true | m] * P⟦t | m⟧) ω ∂P := integral_congr_ae hpull
    _ = ∫ ω, (P⟦D ⁻¹' {true} ∩ t | m⟧) ω ∂P := integral_congr_ae hCI.symm
    _ = ∫ ω, (D ⁻¹' {true} ∩ t).indicator (1 : Ω → ℝ) ω ∂P := integral_condExp hm
    _ = ∫ ω in t, treatmentIndicator D true ω ∂P := by
      rw [hset, integral_indicator (hX.comap_le _ ht)]

/-- L5 Remark 1's coarseness statement: any measurable function of covariates
that balances treatment must measurably recover the propensity score, modulo
the sampling law's null sets. -/
theorem propensityScore_coarsest
    {Ω S R : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mS : MeasurableSpace S] [mR : MeasurableSpace R]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : Ω → Bool} {X : Ω → S}
    (hD : Measurable D) (hX : Measurable X) (b : S → R) (hb : Measurable b)
    (hind : CondIndepFun (mR.comap (b ∘ X)) (hb.comp hX).comap_le D X P) :
    ∃ r : R → ℝ, Measurable r ∧ propensityScore P D X =ᵐ[P] r ∘ b ∘ X := by
  have hsub : mR.comap (b ∘ X) ≤ mS.comap X :=
    MeasurableSpace.comap_le_comap_of_eq_comp b hb rfl
  have he := propensityScore_eq_condExp_of_balancing hD hX hsub hind
  obtain ⟨r, hr, heq⟩ := (stronglyMeasurable_condExp (μ := P)
    (f := treatmentIndicator D true) (m := mR.comap (b ∘ X))).measurable.exists_eq_measurable_comp
  exact ⟨r, hr, he.trans (Filter.EventuallyEq.of_eq heq)⟩

end LectureNotes
