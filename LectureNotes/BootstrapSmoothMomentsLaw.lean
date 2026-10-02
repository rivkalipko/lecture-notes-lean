import LectureNotes.BootstrapVarianceLaw

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- A continuous scalar function of the actual first and denominator-(n-1)
second sample moments. -/
def smoothMomentStatistic {n : ℕ} (h : C(ℝ × ℝ, ℝ)) (x : Fin n → ℝ) : ℝ :=
  h (sampleMean x, sampleVariance x)

theorem measurable_smoothMomentStatistic {n : ℕ} (h : C(ℝ × ℝ, ℝ)) :
    Measurable (smoothMomentStatistic (n := n) h) := by
  unfold smoothMomentStatistic sampleVariance sampleMean
  fun_prop

variable {n : ℕ} [NeZero n]

/-- Exact conditional resampling error for a smooth function of mean and variance. -/
def bootstrapSmoothMomentDifferenceLaw (h : C(ℝ × ℝ, ℝ)) (x : Fin n → ℝ) : Measure ℝ :=
  (bootstrapLaw x).map (fun b => smoothMomentStatistic h b - smoothMomentStatistic h x)

/-- The positively standardized conditional resampling error. -/
def bootstrapSmoothMomentErrorLaw (h : C(ℝ × ℝ, ℝ)) (x : Fin n → ℝ) (τ : ℝ) : Measure ℝ :=
  (bootstrapLaw x).map (fun b => Real.sqrt n / τ *
    (smoothMomentStatistic h b - smoothMomentStatistic h x))

instance bootstrapSmoothMomentDifferenceLaw_isProbabilityMeasure
    (h : C(ℝ × ℝ, ℝ)) (x : Fin n → ℝ) :
    IsProbabilityMeasure (bootstrapSmoothMomentDifferenceLaw h x) := by
  have : IsProbabilityMeasure (bootstrapLaw x) := bootstrapLaw_isProbabilityMeasure x
  exact Measure.isProbabilityMeasure_map
    ((measurable_smoothMomentStatistic h).sub measurable_const).aemeasurable

instance bootstrapSmoothMomentErrorLaw_isProbabilityMeasure
    (h : C(ℝ × ℝ, ℝ)) (x : Fin n → ℝ) (τ : ℝ) :
    IsProbabilityMeasure (bootstrapSmoothMomentErrorLaw h x τ) := by
  have : IsProbabilityMeasure (bootstrapLaw x) := bootstrapLaw_isProbabilityMeasure x
  exact Measure.isProbabilityMeasure_map
    (measurable_const.mul ((measurable_smoothMomentStatistic h).sub measurable_const)).aemeasurable

theorem bootstrapSmoothMomentErrorLaw_index_map (h : C(ℝ × ℝ, ℝ)) (x : Fin n → ℝ) (τ : ℝ) :
    bootstrapSmoothMomentErrorLaw h x τ = (bootstrapIndexLaw n).map
      (fun b : Fin n → Fin n => Real.sqrt n / τ *
        (smoothMomentStatistic h (bootstrapSample x b) - smoothMomentStatistic h x)) := by
  apply bootstrap_statistic_index_map
  exact measurable_const.mul ((measurable_smoothMomentStatistic h).sub measurable_const)

theorem measurable_bootstrapSmoothMomentErrorLaw_cdf (h : C(ℝ × ℝ, ℝ)) (τ t : ℝ) :
    Measurable (fun x : Fin n → ℝ => cdf (bootstrapSmoothMomentErrorLaw h x τ) t) := by
  have : IsProbabilityMeasure (bootstrapIndexLaw n) := by unfold bootstrapIndexLaw; infer_instance
  simp_rw [bootstrapSmoothMomentErrorLaw_index_map]
  apply measurable_cdf_map_family (bootstrapIndexLaw n)
    (fun z : (Fin n → ℝ) × (Fin n → Fin n) => Real.sqrt n / τ *
      (smoothMomentStatistic h (bootstrapSample z.1 z.2) - smoothMomentStatistic h z.1)) _ t
  exact measurable_const.mul (((measurable_smoothMomentStatistic h).comp measurable_bootstrapSample_pair).sub
    ((measurable_smoothMomentStatistic h).comp measurable_fst))

theorem measurable_bootstrapSmoothMomentErrorLaw_quantile (h : C(ℝ × ℝ, ℝ))
    (τ : ℝ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun x : Fin n → ℝ => distributionQuantile (bootstrapSmoothMomentErrorLaw h x τ) q) :=
  measurable_distributionQuantile (fun x => bootstrapSmoothMomentErrorLaw h x τ)
    (measurable_bootstrapSmoothMomentErrorLaw_cdf h τ) hq

theorem measurable_data_bootstrapSmoothMomentErrorLaw_quantile
    {Ω : Type*} [MeasurableSpace Ω] (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (h : C(ℝ × ℝ, ℝ)) (τ : ℝ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun ω => distributionQuantile
      (bootstrapSmoothMomentErrorLaw h (fun i => X i ω) τ) q) :=
  (measurable_bootstrapSmoothMomentErrorLaw_quantile h τ hq).comp (measurable_pi_lambda _ hX)

/-- The population normalization cancels exactly from all interior quantiles. -/
theorem bootstrapSmoothMomentErrorLaw_quantile_rescale (h : C(ℝ × ℝ, ℝ))
    (x : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    distributionQuantile (bootstrapSmoothMomentErrorLaw h x τ) q * (τ / Real.sqrt n) =
      distributionQuantile (bootstrapSmoothMomentDifferenceLaw h x) q := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  let e := OrderIso.mulLeft₀ (Real.sqrt n / τ) (div_pos hs hτ)
  have he : bootstrapSmoothMomentErrorLaw h x τ = (bootstrapSmoothMomentDifferenceLaw h x).map e := by
    unfold bootstrapSmoothMomentErrorLaw bootstrapSmoothMomentDifferenceLaw
    have hm : Measurable (fun b : Fin n → ℝ => smoothMomentStatistic h b - smoothMomentStatistic h x) :=
      (measurable_smoothMomentStatistic h).sub measurable_const
    rw [Measure.map_map (show Measurable e from by fun_prop) hm]
    rfl
  rw [he, distributionQuantile_orderIso _ e hq]
  change ((Real.sqrt n / τ) * _) * (τ / Real.sqrt n) = _
  field_simp

end LectureNotes
