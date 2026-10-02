import LectureNotes.BootstrapStudentizedLaw
import LectureNotes.SamplingMoments

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

variable {n : ℕ} [NeZero n]

/-- The actual centered denominator-(n-1) bootstrap variance law. For n=1,
Lean's total division makes the sample variance and this error identically zero. -/
def bootstrapSampleVarianceDifferenceLaw (x : Fin n → ℝ) : Measure ℝ :=
  (bootstrapLaw x).map (fun b => sampleVariance b - sampleVariance x)

/-- A scaled version of the same conditional resampling error. -/
def bootstrapSampleVarianceErrorLaw (x : Fin n → ℝ) (τ : ℝ) : Measure ℝ :=
  (bootstrapLaw x).map (fun b => Real.sqrt n / τ * (sampleVariance b - sampleVariance x))

theorem measurable_bootstrapSampleVariance_statistic (τ : ℝ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      Real.sqrt n / τ * (sampleVariance z.2 - sampleVariance z.1)) := by
  unfold sampleVariance sampleMean
  fun_prop

instance bootstrapSampleVarianceDifferenceLaw_isProbabilityMeasure (x : Fin n → ℝ) :
    IsProbabilityMeasure (bootstrapSampleVarianceDifferenceLaw x) := by
  have : IsProbabilityMeasure (bootstrapLaw x) := bootstrapLaw_isProbabilityMeasure x
  exact Measure.isProbabilityMeasure_map (by unfold sampleVariance sampleMean; fun_prop)

instance bootstrapSampleVarianceErrorLaw_isProbabilityMeasure (x : Fin n → ℝ) (τ : ℝ) :
    IsProbabilityMeasure (bootstrapSampleVarianceErrorLaw x τ) := by
  have : IsProbabilityMeasure (bootstrapLaw x) := bootstrapLaw_isProbabilityMeasure x
  exact Measure.isProbabilityMeasure_map
    (measurable_bootstrapSampleVariance_statistic τ |>.comp measurable_prodMk_left).aemeasurable

theorem bootstrapSampleVarianceDifferenceLaw_index_map (x : Fin n → ℝ) :
    bootstrapSampleVarianceDifferenceLaw x = (bootstrapIndexLaw n).map
      (fun b : Fin n → Fin n => sampleVariance (bootstrapSample x b) - sampleVariance x) := by
  apply bootstrap_statistic_index_map
  unfold sampleVariance sampleMean
  fun_prop

theorem bootstrapSampleVarianceErrorLaw_index_map (x : Fin n → ℝ) (τ : ℝ) :
    bootstrapSampleVarianceErrorLaw x τ = (bootstrapIndexLaw n).map
      (fun b : Fin n → Fin n => Real.sqrt n / τ *
        (sampleVariance (bootstrapSample x b) - sampleVariance x)) := by
  apply bootstrap_statistic_index_map
  have hs : Measurable (sampleVariance : (Fin n → ℝ) → ℝ) := by
    unfold sampleVariance sampleMean
    fun_prop
  exact measurable_const.mul (hs.sub measurable_const)

theorem measurable_bootstrapSampleVarianceDifferenceLaw_cdf (t : ℝ) :
    Measurable (fun x : Fin n → ℝ => cdf (bootstrapSampleVarianceDifferenceLaw x) t) := by
  have : IsProbabilityMeasure (bootstrapIndexLaw n) := by unfold bootstrapIndexLaw; infer_instance
  simp_rw [bootstrapSampleVarianceDifferenceLaw_index_map]
  apply measurable_cdf_map_family (bootstrapIndexLaw n)
    (fun z : (Fin n → ℝ) × (Fin n → Fin n) =>
      sampleVariance (bootstrapSample z.1 z.2) - sampleVariance z.1) _ t
  have hs : Measurable (sampleVariance : (Fin n → ℝ) → ℝ) := by
    unfold sampleVariance sampleMean
    fun_prop
  exact (hs.comp measurable_bootstrapSample_pair).sub (hs.comp measurable_fst)

theorem measurable_bootstrapSampleVarianceErrorLaw_cdf (τ t : ℝ) :
    Measurable (fun x : Fin n → ℝ => cdf (bootstrapSampleVarianceErrorLaw x τ) t) := by
  have : IsProbabilityMeasure (bootstrapIndexLaw n) := by unfold bootstrapIndexLaw; infer_instance
  simp_rw [bootstrapSampleVarianceErrorLaw_index_map]
  apply measurable_cdf_map_family (bootstrapIndexLaw n)
    (fun z : (Fin n → ℝ) × (Fin n → Fin n) => Real.sqrt n / τ *
      (sampleVariance (bootstrapSample z.1 z.2) - sampleVariance z.1)) _ t
  have hs : Measurable (sampleVariance : (Fin n → ℝ) → ℝ) := by
    unfold sampleVariance sampleMean
    fun_prop
  exact measurable_const.mul ((hs.comp measurable_bootstrapSample_pair).sub (hs.comp measurable_fst))

theorem measurable_bootstrapSampleVarianceDifferenceLaw_quantile {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun x : Fin n → ℝ => distributionQuantile (bootstrapSampleVarianceDifferenceLaw x) q) :=
  measurable_distributionQuantile bootstrapSampleVarianceDifferenceLaw
    measurable_bootstrapSampleVarianceDifferenceLaw_cdf hq

theorem measurable_bootstrapSampleVarianceErrorLaw_quantile (τ : ℝ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun x : Fin n → ℝ => distributionQuantile (bootstrapSampleVarianceErrorLaw x τ) q) :=
  measurable_distributionQuantile (fun x => bootstrapSampleVarianceErrorLaw x τ)
    (measurable_bootstrapSampleVarianceErrorLaw_cdf τ) hq

theorem measurable_data_bootstrapSampleVarianceDifferenceLaw_quantile
    {Ω : Type*} [MeasurableSpace Ω] (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun ω => distributionQuantile
      (bootstrapSampleVarianceDifferenceLaw (fun i => X i ω)) q) :=
  (measurable_bootstrapSampleVarianceDifferenceLaw_quantile hq).comp (measurable_pi_lambda _ hX)

theorem measurable_data_bootstrapSampleVarianceErrorLaw_quantile
    {Ω : Type*} [MeasurableSpace Ω] (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (τ : ℝ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun ω => distributionQuantile
      (bootstrapSampleVarianceErrorLaw (fun i => X i ω) τ) q) :=
  (measurable_bootstrapSampleVarianceErrorLaw_quantile τ hq).comp (measurable_pi_lambda _ hX)

/-- The positive scaling factor cancels exactly in every interior quantile. -/
theorem bootstrapSampleVarianceErrorLaw_quantile_rescale (x : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    distributionQuantile (bootstrapSampleVarianceErrorLaw x τ) q * (τ / Real.sqrt n) =
      distributionQuantile (bootstrapSampleVarianceDifferenceLaw x) q := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  let e := OrderIso.mulLeft₀ (Real.sqrt n / τ) (div_pos hs hτ)
  have he : bootstrapSampleVarianceErrorLaw x τ = (bootstrapSampleVarianceDifferenceLaw x).map e := by
    unfold bootstrapSampleVarianceErrorLaw bootstrapSampleVarianceDifferenceLaw
    rw [Measure.map_map (by fun_prop) (by unfold sampleVariance sampleMean; fun_prop)]
    rfl
  rw [he, distributionQuantile_orderIso _ e hq]
  change ((Real.sqrt n / τ) * _) * (τ / Real.sqrt n) = _
  field_simp

end LectureNotes
