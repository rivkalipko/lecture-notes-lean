import LectureNotes.PosteriorAsymptotics

set_option autoImplicit false

/-! L12 highest posterior density sets minimize reference volume when their
posterior content is calibrated. Ties and threshold existence are separate
questions: an arbitrarily oversized credible region need not be shortest. -/
noncomputable section
namespace LectureNotes
open MeasureTheory Set
variable {Θ : Type*} [MeasurableSpace Θ] {ν : Measure Θ}

def highestDensityRegion (p : Θ → ℝ) (k : ℝ) : Set Θ := {θ | k ≤ p θ}

theorem highestDensityRegion_measurable {p : Θ → ℝ} (hp : Measurable p) (k : ℝ) :
    MeasurableSet (highestDensityRegion p k) := measurableSet_le measurable_const hp

theorem density_event_eq_integral {p : Θ → ℝ} (hp : Integrable p ν)
    (hp0 : ∀ θ, 0 ≤ p θ) (A : Set Θ) (hA : MeasurableSet A) :
    (ν.withDensity (fun θ => ENNReal.ofReal (p θ))).real A = ∫ θ in A, p θ ∂ν := by
  rw [measureReal_def, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal hp.integrableOn (ae_of_all _ hp0),
    ENNReal.toReal_ofReal (integral_nonneg hp0)]

/-- Every measurable competitor with at least as much posterior probability
has at least as much reference volume. This allows infinite competitor volume
and proves the threshold region itself has finite volume when k > 0. -/
theorem highest_density_minimum_volume {p : Θ → ℝ} (hp : Measurable p)
    (hpi : Integrable p ν) (hp0 : ∀ θ, 0 ≤ p θ) {k : ℝ} (hk : 0 < k)
    (C : Set Θ) (hC : MeasurableSet C)
    (hcontent : (ν.withDensity (fun θ => ENNReal.ofReal (p θ))).real
      (highestDensityRegion p k) ≤
        (ν.withDensity (fun θ => ENNReal.ofReal (p θ))).real C) :
    ν (highestDensityRegion p k) ≤ ν C := by
  let H := highestDensityRegion p k
  have hH : MeasurableSet H := highestDensityRegion_measurable hp k
  have hHfin : ν H ≠ ⊤ := by
    have h := (hpi.measure_norm_ge_lt_top hk).ne
    simpa only [H, highestDensityRegion, Real.norm_eq_abs, abs_of_nonneg (hp0 _)] using h
  by_cases hCfin : ν C = ⊤
  · simp [hCfin]
  have hiH : IntegrableOn (fun θ => p θ - k) H ν :=
    hpi.integrableOn.sub (integrableOn_const hHfin)
  have hiC : IntegrableOn (fun θ => p θ - k) C ν :=
    hpi.integrableOn.sub (integrableOn_const hCfin)
  have hpoint (θ : Θ) : C.indicator (fun θ => p θ - k) θ ≤
      H.indicator (fun θ => p θ - k) θ := by
    by_cases hθH : θ ∈ H <;> by_cases hθC : θ ∈ C
    · simp [indicator_of_mem hθH, indicator_of_mem hθC]
    · simpa [indicator_of_mem hθH, indicator_of_notMem hθC] using
        sub_nonneg.mpr (show k ≤ p θ from hθH)
    · have hpk : p θ < k := lt_of_not_ge hθH
      simpa [indicator_of_notMem hθH, indicator_of_mem hθC] using (sub_neg.mpr hpk).le
    · simp [indicator_of_notMem hθH, indicator_of_notMem hθC]
  have hc := integral_mono ((integrable_indicator_iff hC).mpr hiC)
    ((integrable_indicator_iff hH).mpr hiH) hpoint
  rw [integral_indicator hC, integral_indicator hH,
    integral_sub hpi.integrableOn (integrableOn_const hCfin),
    integral_sub hpi.integrableOn (integrableOn_const hHfin),
    integral_const, integral_const] at hc
  simp only [Measure.real, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, smul_eq_mul] at hc
  rw [density_event_eq_integral hpi hp0 _ hH,
    density_event_eq_integral hpi hp0 C hC] at hcontent
  apply (ENNReal.toReal_le_toReal hHfin hCfin).mp
  change ν.real H ≤ ν.real C
  change (∫ θ in C, p θ ∂ν) - ν.real C * k ≤
    (∫ θ in H, p θ ∂ν) - ν.real H * k at hc
  change (∫ θ in H, p θ ∂ν) ≤ (∫ θ in C, p θ ∂ν) at hcontent
  nlinarith

/-- If the threshold region has posterior content exactly equal to the
desired level, it has minimum volume among all credible sets at that level. -/
theorem calibrated_highest_density_minimum_volume {p : Θ → ℝ} (hp : Measurable p)
    (hpi : Integrable p ν) (hp0 : ∀ θ, 0 ≤ p θ) {k : ℝ} (hk : 0 < k)
    (level : ℝ)
    (hcal : (ν.withDensity (fun θ => ENNReal.ofReal (p θ))).real
      (highestDensityRegion p k) = level)
    (C : Set Θ) (hC : MeasurableSet C)
    (hcredible : level ≤ (ν.withDensity (fun θ => ENNReal.ofReal (p θ))).real C) :
    ν (highestDensityRegion p k) ≤ ν C := by
  apply highest_density_minimum_volume hp hpi hp0 hk C hC
  rwa [hcal]

end LectureNotes
