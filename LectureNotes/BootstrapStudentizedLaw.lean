import LectureNotes.BootstrapMeanQuantiles

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

variable {n : ℕ} [NeZero n]

/-- Any measurable bootstrap statistic is the image of the fixed index law. -/
theorem bootstrap_statistic_index_map (x : Fin n → ℝ)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) :
    (bootstrapLaw x).map f = (bootstrapIndexLaw n).map
      (fun b : Fin n → Fin n => f (bootstrapSample x b)) := by
  have hm : Measurable (fun b : Fin n → Fin n => bootstrapSample x b) := Measurable.of_discrete
  rw [← (bootstrapSample_hasLaw x).map_eq]
  simpa only [Function.comp_def] using! (Measure.map_map (μ := bootstrapIndexLaw n) hf hm)

/-- The studentized bootstrap error is defined on every resample, including
zero empirical variance via Lean's total real division. -/
def bootstrapStudentizedMeanLaw (x : Fin n → ℝ) : Measure ℝ :=
  (bootstrapLaw x).map (fun b => Real.sqrt n * (sampleMean b - sampleMean x) /
    Real.sqrt (empiricalVariance b))

theorem measurable_bootstrapStudentizedMean_statistic :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      Real.sqrt n * (sampleMean z.2 - sampleMean z.1) / Real.sqrt (empiricalVariance z.2)) := by
  unfold empiricalVariance sampleMean
  fun_prop

instance bootstrapStudentizedMeanLaw_isProbabilityMeasure (x : Fin n → ℝ) :
    IsProbabilityMeasure (bootstrapStudentizedMeanLaw x) := by
  have : IsProbabilityMeasure (bootstrapLaw x) := bootstrapLaw_isProbabilityMeasure x
  apply Measure.isProbabilityMeasure_map
  exact (measurable_bootstrapStudentizedMean_statistic.comp measurable_prodMk_left).aemeasurable

theorem bootstrapStudentizedMeanLaw_index_map (x : Fin n → ℝ) :
    bootstrapStudentizedMeanLaw x = (bootstrapIndexLaw n).map
      (fun b : Fin n → Fin n => Real.sqrt n *
        (sampleMean (bootstrapSample x b) - sampleMean x) /
        Real.sqrt (empiricalVariance (bootstrapSample x b))) := by
  apply bootstrap_statistic_index_map
  exact measurable_bootstrapStudentizedMean_statistic.comp measurable_prodMk_left

theorem measurable_bootstrapStudentizedMeanLaw_cdf (t : ℝ) :
    Measurable (fun x : Fin n → ℝ => cdf (bootstrapStudentizedMeanLaw x) t) := by
  have : IsProbabilityMeasure (bootstrapIndexLaw n) := by unfold bootstrapIndexLaw; infer_instance
  simp_rw [bootstrapStudentizedMeanLaw_index_map]
  apply measurable_cdf_map_family (bootstrapIndexLaw n)
    (fun z : (Fin n → ℝ) × (Fin n → Fin n) => Real.sqrt n *
      (sampleMean (bootstrapSample z.1 z.2) - sampleMean z.1) /
      Real.sqrt (empiricalVariance (bootstrapSample z.1 z.2))) _ t
  have hp : Measurable (fun z : (Fin n → ℝ) × (Fin n → Fin n) =>
      (z.1, bootstrapSample z.1 z.2)) := measurable_fst.prodMk measurable_bootstrapSample_pair
  exact (measurable_bootstrapStudentizedMean_statistic (n := n)).comp hp

theorem measurable_bootstrapStudentizedMeanLaw_quantile {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun x : Fin n → ℝ => distributionQuantile (bootstrapStudentizedMeanLaw x) q) :=
  measurable_distributionQuantile bootstrapStudentizedMeanLaw measurable_bootstrapStudentizedMeanLaw_cdf hq

theorem measurable_data_bootstrapStudentizedMeanLaw_quantile {Ω : Type*} [MeasurableSpace Ω]
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun ω => distributionQuantile (bootstrapStudentizedMeanLaw (fun i => X i ω)) q) :=
  (measurable_bootstrapStudentizedMeanLaw_quantile hq).comp (measurable_pi_lambda _ hX)

end LectureNotes
