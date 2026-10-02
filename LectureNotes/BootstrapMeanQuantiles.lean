import LectureNotes.BootstrapConditionalCLT
import LectureNotes.QuantileMeasurability

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- Resampling is jointly measurable in the data and the finite index vector. -/
theorem measurable_bootstrapSample_pair {n : ℕ} :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → Fin n) => bootstrapSample z.1 z.2) := by
  classical
  apply measurable_pi_lambda
  intro i
  have he : (fun z : (Fin n → ℝ) × (Fin n → Fin n) => bootstrapSample z.1 z.2 i) =
      (fun z => ∑ j : Fin n, if z.2 i = j then z.1 j else 0) := by
    funext z
    simp [bootstrapSample]
  rw [he]
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite (measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_snd)
    measurable_const) ((measurable_pi_apply j).comp measurable_fst) measurable_const

/-- The normalized bootstrap error is the image of one fixed index law. -/
theorem bootstrapMeanErrorLaw_index_map {n : ℕ} [NeZero n]
    (x : Fin n → ℝ) (σ : ℝ) :
    bootstrapMeanErrorLaw x σ = (bootstrapIndexLaw n).map
      (fun b : Fin n → Fin n => Real.sqrt n / σ * (sampleMean (bootstrapSample x b) - sampleMean x)) := by
  have hm : Measurable (fun b : Fin n → ℝ => Real.sqrt n / σ * (sampleMean b - sampleMean x)) := by
    unfold sampleMean
    fun_prop
  have hm' : Measurable (fun b : Fin n → Fin n => bootstrapSample x b) := Measurable.of_discrete
  rw [bootstrapMeanErrorLaw, ← (bootstrapSample_hasLaw x).map_eq]
  simpa only [Function.comp_def] using! (Measure.map_map (μ := bootstrapIndexLaw n) hm hm')

/-- The actual finite-sample conditional bootstrap CDF is measurable in the
original data, with no density or atomlessness requirement. -/
theorem measurable_bootstrapMeanErrorLaw_cdf {n : ℕ} [NeZero n] (σ t : ℝ) :
    Measurable (fun x : Fin n → ℝ => cdf (bootstrapMeanErrorLaw x σ) t) := by
  have : IsProbabilityMeasure (bootstrapIndexLaw n) := by unfold bootstrapIndexLaw; infer_instance
  simp_rw [bootstrapMeanErrorLaw_index_map]
  apply measurable_cdf_map_family (bootstrapIndexLaw n)
    (fun z : (Fin n → ℝ) × (Fin n → Fin n) =>
      Real.sqrt n / σ * (sampleMean (bootstrapSample z.1 z.2) - sampleMean z.1)) _ t
  have hs : Measurable (sampleMean : (Fin n → ℝ) → ℝ) := by unfold sampleMean; fun_prop
  exact measurable_const.mul ((hs.comp measurable_bootstrapSample_pair).sub (hs.comp measurable_fst))

/-- Interior quantiles of the actual conditional bootstrap law are measurable. -/
theorem measurable_bootstrapMeanErrorLaw_quantile {n : ℕ} [NeZero n]
    (σ : ℝ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun x : Fin n → ℝ => distributionQuantile (bootstrapMeanErrorLaw x σ) q) :=
  measurable_distributionQuantile (fun x => bootstrapMeanErrorLaw x σ)
    (measurable_bootstrapMeanErrorLaw_cdf σ) hq

/-- Measurable observed coordinates give measurable bootstrap critical values. -/
theorem measurable_data_bootstrapMeanErrorLaw_quantile {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (σ : ℝ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun ω => distributionQuantile (bootstrapMeanErrorLaw (fun i => X i ω) σ) q) :=
  (measurable_bootstrapMeanErrorLaw_quantile σ hq).comp (measurable_pi_lambda _ hX)

end LectureNotes
