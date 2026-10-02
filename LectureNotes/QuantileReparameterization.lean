import LectureNotes.QuantileConvergence
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- The CDF at a transformed point for a strictly increasing map. Surjectivity
is unnecessary, and the original law may have atoms. -/
theorem cdf_map_strictMono (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {g : ℝ → ℝ} (hg : StrictMono g) (x : ℝ) :
    cdf (μ.map g) (g x) = cdf μ x := by
  have : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.monotone.measurable.aemeasurable
  rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply hg.monotone.measurable measurableSet_Iic]
  congr 1
  ext y
  exact hg.le_iff_le

/-- Continuous increasing transformations commute with lower quantiles even
when the transformation has a proper subinterval as its range. -/
theorem distributionQuantile_continuous_strictMono (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {g : ℝ → ℝ} (hc : Continuous g) (hg : StrictMono g)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    distributionQuantile (μ.map g) q = g (distributionQuantile μ q) := by
  have : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hc.measurable.aemeasurable
  apply le_antisymm
  · apply (distributionQuantile_le_iff _ hq).mpr
    rw [cdf_map_strictMono μ hg, cdf_eq_real]
    exact (distributionQuantile_bracket μ q hq).2
  · apply le_of_tendsto (hc.continuousAt.continuousWithinAt (s := Iio (distributionQuantile μ q)))
    filter_upwards [self_mem_nhdsWithin] with x hx
    apply le_of_lt
    apply (lt_distributionQuantile_iff _ hq).mpr
    rw [cdf_map_strictMono μ hg]
    exact (lt_distributionQuantile_iff μ hq).mp hx

/-- Increasing continuous transformations take the whole quantile interval
to the transformed law's quantile interval. -/
theorem quantile_interval_continuous_strictMono (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {g : ℝ → ℝ} (hc : Continuous g) (hg : StrictMono g)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    g '' Icc (distributionQuantile μ a) (distributionQuantile μ b) =
      Icc (distributionQuantile (μ.map g) a) (distributionQuantile (μ.map g) b) := by
  rw [distributionQuantile_continuous_strictMono μ hc hg ha,
    distributionQuantile_continuous_strictMono μ hc hg hb]
  exact hc.image_Icc_of_strictMono hg

/-- For an atomless law, a decreasing map exchanges the lower and upper tails. -/
theorem cdf_map_strictAnti (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {g : ℝ → ℝ} (hg : StrictAnti g) (x : ℝ) :
    cdf (μ.map g) (g x) = 1 - cdf μ x := by
  have : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.antitone.measurable.aemeasurable
  rw [cdf_eq_real, map_measureReal_apply hg.antitone.measurable measurableSet_Iic]
  have he : g ⁻¹' Iic (g x) = Ici x := by
    ext y
    exact hg.le_iff_ge
  rw [he, ← compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ,
    measureReal_congr Iio_ae_eq_Iic, ← cdf_eq_real]

/-- For a continuous strictly decreasing transformation, the quantile levels
are reversed. The strict CDF condition excludes ambiguity at gaps in support. -/
theorem distributionQuantile_continuous_strictAnti (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (hF : StrictMono (cdf μ))
    {g : ℝ → ℝ} (hc : Continuous g) (hg : StrictAnti g)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    distributionQuantile (μ.map g) q = g (distributionQuantile μ (1 - q)) := by
  have : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hc.measurable.aemeasurable
  have hq' : 1 - q ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hq.2], by linarith [hq.1]⟩
  have hcut : cdf μ (distributionQuantile μ (1 - q)) = 1 - q := by
    rw [cdf_eq_real, distributionQuantile_exact μ _ hq']
  apply le_antisymm
  · apply (distributionQuantile_le_iff _ hq).mpr
    rw [cdf_map_strictAnti μ hg, hcut]
    linarith
  · apply le_of_tendsto (hc.continuousAt.continuousWithinAt (s := Ioi (distributionQuantile μ (1 - q))))
    filter_upwards [self_mem_nhdsWithin] with x hx
    apply le_of_lt
    apply (lt_distributionQuantile_iff _ hq).mpr
    rw [cdf_map_strictAnti μ hg]
    have hh := hF hx
    rw [hcut] at hh
    linarith

/-- Decreasing transformations exchange the two endpoints and tail levels. -/
theorem quantile_interval_continuous_strictAnti (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (hF : StrictMono (cdf μ))
    {g : ℝ → ℝ} (hc : Continuous g) (hg : StrictAnti g)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    g '' Icc (distributionQuantile μ a) (distributionQuantile μ b) =
      Icc (distributionQuantile (μ.map g) (1 - b))
        (distributionQuantile (μ.map g) (1 - a)) := by
  have ha' : 1 - a ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ha.2], by linarith [ha.1]⟩
  have hb' : 1 - b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.2], by linarith [hb.1]⟩
  rw [distributionQuantile_continuous_strictAnti μ hF hc hg hb',
    distributionQuantile_continuous_strictAnti μ hF hc hg ha']
  have hea : 1 - (1 - a) = a := by ring
  have heb : 1 - (1 - b) = b := by ring
  rw [hea, heb]
  exact hc.continuousOn.image_Icc_of_antitoneOn
    (distributionQuantile_mono μ ha hb hab) (hg.antitone.antitoneOn _)

end LectureNotes
