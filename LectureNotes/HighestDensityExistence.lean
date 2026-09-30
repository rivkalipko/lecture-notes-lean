import LectureNotes.HighestDensity
import LectureNotes.NormalConfidenceIntervals

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- A density is positive almost surely under the measure it defines, even
when it vanishes on a set of positive reference measure. -/
theorem density_positive_ae {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
    {p : Θ → ℝ} (hp : Measurable p) :
    ∀ᵐ θ ∂ν.withDensity (fun θ => ENNReal.ofReal (p θ)), 0 < p θ := by
  rw [ae_withDensity_iff (by fun_prop)]
  exact ae_of_all _ (fun θ hθ => ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hθ))

/-- Existence of an exactly calibrated HPD cutoff when the density value has
an atomless posterior law. This excludes flat density plateaus carrying
posterior mass; those require a separate rule for breaking ties. -/
theorem exists_highest_density_region {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) (p : Θ → ℝ) (hp : Measurable p) (hi : Integrable p ν)
    (hn : ∀ θ, 0 ≤ p θ) (h1 : (∫ θ, p θ ∂ν) = 1)
    [NullSingletonClass ((ν.withDensity (fun θ => ENNReal.ofReal (p θ))).map p)]
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    ∃ k, 0 < k ∧
      (ν.withDensity (fun θ => ENNReal.ofReal (p θ))).real (highestDensityRegion p k) = 1 - α ∧
      ∀ C : Set Θ, MeasurableSet C →
        1 - α ≤ (ν.withDensity (fun θ => ENNReal.ofReal (p θ))).real C →
        ν (highestDensityRegion p k) ≤ ν C := by
  let P := ν.withDensity (fun θ => ENNReal.ofReal (p θ))
  have : IsProbabilityMeasure P := density_model_isProbabilityMeasure hi (ae_of_all _ hn) h1
  let μ := P.map p
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hp.aemeasurable
  have hpos : ∀ᵐ x ∂μ, 0 < x := by
    exact (ae_map_iff hp.aemeasurable (by measurability)).mpr (density_positive_ae ν hp)
  let k := distributionQuantile μ α
  have hk : 0 < k := distributionQuantile_pos μ hpos hα
  have hl : P.real {θ | p θ < k} = α := by
    have hcal := distributionQuantile_exact μ α hα
    have he : μ.real (Iio k) = μ.real (Iic k) := measureReal_congr Iio_ae_eq_Iic
    change μ.real (Iic k) = α at hcal
    rw [← he, map_measureReal_apply hp measurableSet_Iio] at hcal
    exact hcal
  have hcal : P.real (highestDensityRegion p k) = 1 - α := by
    have he : highestDensityRegion p k = {θ | p θ < k}ᶜ := by ext θ; simp [highestDensityRegion]
    rw [he, measureReal_compl (measurableSet_lt hp measurable_const), probReal_univ, hl]
  refine ⟨k, hk, hcal, fun C hC hcontent => ?_⟩
  exact calibrated_highest_density_minimum_volume hp hi hn hk (1 - α) hcal C hC hcontent

end LectureNotes
