import LectureNotes.HighestDensityExistence

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- Selecting any measurable part of a density plateau preserves the HPD
minimum-volume property. Every point strictly above the cutoff must be kept,
and no point strictly below it may be kept. -/
theorem highest_density_plateau_minimum_volume {Θ : Type*} [MeasurableSpace Θ]
    {ν : Measure Θ} {p : Θ → ℝ}
    (hi : Integrable p ν) (hn : ∀ θ, 0 ≤ p θ) {k : ℝ} (hk : 0 < k)
    {H : Set Θ} (hH : MeasurableSet H)
    (habove : {θ | k < p θ} ⊆ H) (hbelow : H ⊆ {θ | k ≤ p θ})
    (C : Set Θ) (hC : MeasurableSet C)
    (hcontent : (ν.withDensity (fun θ => ENNReal.ofReal (p θ))).real H ≤
      (ν.withDensity (fun θ => ENNReal.ofReal (p θ))).real C) : ν H ≤ ν C := by
  have hHfin : ν H ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono hbelow)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _)] using
      (hi.measure_norm_ge_lt_top hk).ne
  by_cases hCfin : ν C = ⊤
  · simp [hCfin]
  have hiH : IntegrableOn (fun θ => p θ - k) H ν :=
    hi.integrableOn.sub (integrableOn_const hHfin)
  have hiC : IntegrableOn (fun θ => p θ - k) C ν :=
    hi.integrableOn.sub (integrableOn_const hCfin)
  have hpoint (θ : Θ) : C.indicator (fun θ => p θ - k) θ ≤
      H.indicator (fun θ => p θ - k) θ := by
    by_cases hθH : θ ∈ H <;> by_cases hθC : θ ∈ C
    · simp [indicator_of_mem hθH, indicator_of_mem hθC]
    · simpa [indicator_of_mem hθH, indicator_of_notMem hθC] using
        sub_nonneg.mpr (show k ≤ p θ from hbelow hθH)
    · have hpk : p θ ≤ k := le_of_not_gt (fun h => hθH (habove h))
      simpa [indicator_of_notMem hθH, indicator_of_mem hθC] using sub_nonpos.mpr hpk
    · simp [indicator_of_notMem hθH, indicator_of_notMem hθC]
  have hc := integral_mono ((integrable_indicator_iff hC).mpr hiC)
    ((integrable_indicator_iff hH).mpr hiH) hpoint
  rw [integral_indicator hC, integral_indicator hH,
    integral_sub hi.integrableOn (integrableOn_const hCfin),
    integral_sub hi.integrableOn (integrableOn_const hHfin),
    integral_const, integral_const] at hc
  simp only [Measure.real, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, smul_eq_mul] at hc
  rw [density_event_eq_integral hi hn _ hH, density_event_eq_integral hi hn C hC] at hcontent
  apply (ENNReal.toReal_le_toReal hHfin hCfin).mp
  change ν.real H ≤ ν.real C
  change (∫ θ in C, p θ ∂ν) - ν.real C * k ≤
    (∫ θ in H, p θ ∂ν) - ν.real H * k at hc
  nlinarith

/-- A finite atomless measure on the real line can split any measurable set
to any prescribed mass between zero and its full mass, including endpoints. -/
theorem exists_measurable_subset_real_mass (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {S : Set ℝ} (hS : MeasurableSet S)
    {r : ℝ} (hr : 0 ≤ r) (hrs : r ≤ μ.real S) :
    ∃ B : Set ℝ, MeasurableSet B ∧ B ⊆ S ∧ μ.real B = r := by
  by_cases hz : r = 0
  · exact ⟨∅, MeasurableSet.empty, empty_subset S, by simp [hz]⟩
  by_cases he : r = μ.real S
  · exact ⟨S, hS, Subset.rfl, he.symm⟩
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
  have htotal : 0 < μ.real S := hrpos.trans_le hrs
  let ρ := μ.restrict S
  have hρ : ρ ≠ 0 := by
    intro hzero
    have hzρ : ρ.real univ = 0 := by rw [hzero]; simp
    have : μ.real S = 0 := by simpa only [ρ, measureReal_restrict_apply_univ] using hzρ
    linarith
  have : NeZero ρ := ⟨hρ⟩
  let η := (ρ univ)⁻¹ • ρ
  have : NullSingletonClass η := ⟨fun x => by simp [η, Measure.smul_apply]⟩
  have hq : r / μ.real S ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hrpos htotal, (div_lt_one htotal).mpr (lt_of_le_of_ne hrs he)⟩
  let x := distributionQuantile η (r / μ.real S)
  have hcal := distributionQuantile_exact η (r / μ.real S) hq
  refine ⟨Iic x ∩ S, measurableSet_Iic.inter hS, inter_subset_right, ?_⟩
  change η.real (Iic x) = r / μ.real S at hcal
  simp only [η, ρ, measureReal_ennreal_smul_apply, ENNReal.toReal_inv,
    Measure.restrict_apply MeasurableSet.univ, univ_inter,
    measureReal_restrict_apply measurableSet_Iic] at hcal
  change (μ.real S)⁻¹ * μ.real (Iic x ∩ S) = r / μ.real S at hcal
  have htotalne := htotal.ne'
  field_simp [htotalne] at hcal
  exact hcal

/-- Every real density relative to an atomless reference measure has an
exactly calibrated minimum-volume credible set at an interior probability
level. If the cutoff density has positive posterior mass, a measurable part
of that plateau is selected. Atomlessness is required of the parameter law,
not of the distribution of its density values. -/
theorem exists_highest_density_region_with_plateaus (ν : Measure ℝ)
    [NullSingletonClass ν] (p : ℝ → ℝ) (hp : Measurable p) (hi : Integrable p ν)
    (hn : ∀ θ, 0 ≤ p θ) (h1 : (∫ θ, p θ ∂ν) = 1)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    ∃ k : ℝ, ∃ H : Set ℝ, 0 < k ∧ MeasurableSet H ∧
      {θ | k < p θ} ⊆ H ∧ H ⊆ {θ | k ≤ p θ} ∧
      (ν.withDensity (fun θ => ENNReal.ofReal (p θ))).real H = 1 - α ∧
      ∀ C : Set ℝ, MeasurableSet C →
        1 - α ≤ (ν.withDensity (fun θ => ENNReal.ofReal (p θ))).real C → ν H ≤ ν C := by
  let P := ν.withDensity (fun θ => ENNReal.ofReal (p θ))
  have : IsProbabilityMeasure P := density_model_isProbabilityMeasure hi (ae_of_all _ hn) h1
  let μ := P.map p
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hp.aemeasurable
  have hpos : ∀ᵐ x ∂μ, 0 < x := by
    exact (ae_map_iff hp.aemeasurable (by measurability)).mpr (density_positive_ae ν hp)
  let k := distributionQuantile μ α
  have hk : 0 < k := distributionQuantile_pos μ hpos hα
  let A := {θ | k < p θ}
  let T := {θ | p θ = k}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hp
  have hT : MeasurableSet T := measurableSet_eq_fun hp measurable_const
  have hdis : Disjoint A T := disjoint_left.mpr (by
    intro θ hθ hEq
    exact (ne_of_gt (show k < p θ from hθ)) (show p θ = k from hEq))
  have hbracket := distributionQuantile_bracket μ α hα
  change μ.real (Iio k) ≤ α ∧ α ≤ μ.real (Iic k) at hbracket
  rw [map_measureReal_apply hp measurableSet_Iio,
    map_measureReal_apply hp measurableSet_Iic] at hbracket
  change P.real {θ | p θ < k} ≤ α ∧ α ≤ P.real {θ | p θ ≤ k} at hbracket
  have hAc : A = {θ | p θ ≤ k}ᶜ := by ext θ; simp [A]
  have hAT : A ∪ T = {θ | p θ < k}ᶜ := by
    ext θ
    simp only [A, T, mem_union, mem_compl_iff, mem_ofPred_eq, not_lt]
    constructor
    · rintro (h | h)
      · exact h.le
      · exact h.symm.le
    · intro h
      rcases lt_or_eq_of_le h with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
  have hlow : P.real A ≤ 1 - α := by
    rw [hAc, measureReal_compl (measurableSet_le hp measurable_const), probReal_univ]
    linarith [hbracket.2]
  have hupp : 1 - α ≤ P.real A + P.real T := by
    rw [← measureReal_union hdis hT, hAT,
      measureReal_compl (measurableSet_lt hp measurable_const), probReal_univ]
    linarith [hbracket.1]
  obtain ⟨B, hB, hBT, hcalB⟩ := exists_measurable_subset_real_mass P hT
    (show 0 ≤ 1 - α - P.real A by linarith)
    (show 1 - α - P.real A ≤ P.real T by linarith)
  have hAB : Disjoint A B := hdis.mono_right hBT
  have hH : MeasurableSet (A ∪ B) := hA.union hB
  have habove : {θ | k < p θ} ⊆ A ∪ B := subset_union_left
  have hbelow : A ∪ B ⊆ {θ | k ≤ p θ} := by
    intro θ hθ
    rcases hθ with hθ | hθ
    · exact le_of_lt (show k < p θ from hθ)
    · exact le_of_eq (hBT hθ).symm
  have hcal : P.real (A ∪ B) = 1 - α := by
    rw [measureReal_union hAB hB, hcalB]
    ring
  refine ⟨k, A ∪ B, hk, hH, habove, hbelow, hcal, fun C hC hc => ?_⟩
  apply highest_density_plateau_minimum_volume hi hn hk hH habove hbelow C hC
  change P.real (A ∪ B) ≤ P.real C
  rwa [hcal]

end LectureNotes
