import LectureNotes.QuantileConvergence

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- A family of real probability laws has measurable interior lower quantiles
whenever its CDF is measurable in the parameter at every fixed argument. -/
theorem measurable_distributionQuantile {Ω : Type*} [MeasurableSpace Ω]
    (μ : Ω → Measure ℝ) [∀ ω, IsProbabilityMeasure (μ ω)]
    (hF : ∀ t : ℝ, Measurable (fun ω => cdf (μ ω) t))
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun ω => distributionQuantile (μ ω) q) := by
  apply measurable_of_Iic
  intro t
  have he : (fun ω => distributionQuantile (μ ω) q) ⁻¹' Iic t =
      {ω | q ≤ cdf (μ ω) t} := by
    ext ω
    exact distributionQuantile_le_iff (μ ω) hq
  rw [he]
  exact measurableSet_le measurable_const (hF t)

/-- Markov kernels therefore have measurable lower quantile functions at
all interior probability levels, without atomlessness assumptions. -/
theorem measurable_kernel_distributionQuantile {Ω : Type*} [MeasurableSpace Ω]
    (κ : Kernel Ω ℝ) [IsMarkovKernel κ] {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun ω => distributionQuantile (κ ω) q) := by
  apply measurable_distributionQuantile κ _ hq
  intro t
  simp_rw [cdf_eq_real, measureReal_def]
  exact (κ.measurable_coe measurableSet_Iic).ennreal_toReal

/-- A jointly measurable statistic with a fixed sampling measure has a CDF
that is measurable in its parameter, even when its law is discrete. -/
theorem measurable_cdf_map_family {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (f : Ω × Ξ → ℝ) (hf : Measurable f) (t : ℝ) :
    Measurable (fun ω => cdf (P.map (fun ξ => f (ω, ξ))) t) := by
  have hm (ω : Ω) : Measurable (fun ξ => f (ω, ξ)) :=
    hf.comp measurable_prodMk_left
  have (ω : Ω) : IsProbabilityMeasure (P.map (fun ξ => f (ω, ξ))) :=
    Measure.isProbabilityMeasure_map (hm ω).aemeasurable
  have he (ω : Ω) : cdf (P.map (fun ξ => f (ω, ξ))) t =
      (P (Prod.mk ω ⁻¹' {z | f z ≤ t})).toReal := by
    rw [cdf_eq_real, map_measureReal_apply (hm ω) measurableSet_Iic]
    rfl
  simp_rw [he]
  exact (measurable_measure_prodMk_left (measurableSet_le hf measurable_const)).ennreal_toReal

end LectureNotes
