import LectureNotes.QuantileConvergence

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem random_critical_value_strict_probability {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T C : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {ν : Measure ℝ}
    [IsProbabilityMeasure ν] [NullSingletonClass ν] {c : ℝ}
    (hT : ConvergesInDistribution P Q T Z) (hZ : HasLaw Z ν Q)
    (hC : ConvergesInProbability P C (fun _ => c))
    (hm : ∀ n, AEMeasurable (C n) P) :
    Tendsto (fun n => P.real {ω | T n ω < C n ω}) atTop (𝓝 (cdf ν c)) := by
  have hd : ConvergesInDistribution P Q (fun n ω => T n ω - C n ω) (fun ω => Z ω - c) :=
    TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun z : ℝ × ℝ => z.1 - z.2) (by fun_prop) hT hC hm
  have hzm : AEMeasurable (fun ω => Z ω - c) Q := hZ.aemeasurable.sub aemeasurable_const
  have hz : (Q.map (fun ω => Z ω - c)) (frontier (Iio (0 : ℝ))) = 0 := by
    rw [frontier_Iio, Measure.map_apply_of_aemeasurable hzm (measurableSet_singleton _)]
    have he : (fun ω => Z ω - c) ⁻¹' {0} = Z ⁻¹' {c} := by ext ω; simp [sub_eq_zero]
    rw [he, ← Measure.map_apply_of_aemeasurable hZ.aemeasurable (measurableSet_singleton c),
      hZ.map_eq, measure_singleton]
  have h := asymptotic_rejection_probability hd (Iio 0) measurableSet_Iio hz
  have he : Q.real {ω | Z ω < c} = cdf ν c := by
    have h₁ : Q.real {ω | Z ω < c} = ν.real (Iio c) :=
      hZ.measureReal_eq (p := fun x => x < c) measurableSet_Iio
    rw [h₁, measureReal_congr Iio_ae_eq_Iic, cdf_eq_real]
  simpa only [mem_Iio, sub_neg, he] using h

/-- Two consistent, ordered random critical values give the limiting mass
between them. The critical values may depend on the statistic's own data. -/
theorem random_interval_probability {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T A B : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {ν : Measure ℝ}
    [IsProbabilityMeasure ν] [NullSingletonClass ν] {a b : ℝ}
    (hT : ConvergesInDistribution P Q T Z) (hZ : HasLaw Z ν Q)
    (hA : ConvergesInProbability P A (fun _ => a))
    (hB : ConvergesInProbability P B (fun _ => b))
    (hmT : ∀ n, Measurable (T n)) (hmA : ∀ n, Measurable (A n)) (hmB : ∀ n, Measurable (B n))
    (hAB : ∀ n ω, A n ω ≤ B n ω) :
    Tendsto (fun n => P.real {ω | T n ω ∈ Icc (A n ω) (B n ω)}) atTop
      (𝓝 (cdf ν b - cdf ν a)) := by
  have h₁ := random_critical_value_probability hT hZ hB (fun n => (hmB n).aemeasurable)
  have h₂ := random_critical_value_strict_probability hT hZ hA (fun n => (hmA n).aemeasurable)
  have he (n) : P.real {ω | T n ω ∈ Icc (A n ω) (B n ω)} =
      P.real {ω | T n ω ≤ B n ω} - P.real {ω | T n ω < A n ω} := by
    have hs : {ω | T n ω ∈ Icc (A n ω) (B n ω)} =
        {ω | T n ω ≤ B n ω} \ {ω | T n ω < A n ω} := by
      ext ω; simp only [mem_setOf_eq, mem_Icc, Set.mem_sdiff, not_lt, and_comm]
    rw [hs, measureReal_sdiff]
    · intro ω hω; exact hω.le.trans (hAB n ω)
    · exact measurableSet_lt (hmT n) (hmA n)
  simp_rw [he]
  exact h₁.sub h₂

/-- L11's basic and studentized bootstrap intervals, conditional on a valid
bootstrap CDF approximation for the normalized error. Use a deterministic
inverse convergence rate for the basic interval, or an estimated standard
error for studentization. The conditional limit must be established for the
chosen resampling model; convergence of unscaled errors to zero is insufficient. -/
theorem bootstrap_interval_coverage {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : ℕ → Ω → Measure ℝ) (ν : Measure ℝ)
    [∀ n ω, IsProbabilityMeasure (B n ω)] [IsProbabilityMeasure ν] [NullSingletonClass ν]
    {E S : ℕ → Ω → ℝ} {θ : ℝ} {Z : Ω' → ℝ}
    (hS : ∀ n, ∀ᵐ ω ∂P, 0 < S n ω)
    (hm : ∀ n, Measurable (fun ω => (E n ω - θ) / S n ω))
    (hT : ConvergesInDistribution P Q (fun n ω => (E n ω - θ) / S n ω) Z)
    (hZ : HasLaw Z ν Q) (hstrict : StrictMono (cdf ν))
    (hconv : ∀ᵐ ω ∂P, ∀ x, Tendsto (fun n => cdf (B n ω) x) atTop (𝓝 (cdf ν x)))
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b)
    (hma : ∀ n, Measurable (fun ω => distributionQuantile (B n ω) a))
    (hmb : ∀ n, Measurable (fun ω => distributionQuantile (B n ω) b)) :
    Tendsto (fun n => P.real {ω | θ ∈ Icc
      (E n ω - distributionQuantile (B n ω) b * S n ω)
      (E n ω - distributionQuantile (B n ω) a * S n ω)}) atTop (𝓝 (b - a)) := by
  have hA := bootstrap_quantile_consistency B ν hstrict hconv ha (fun n => (hma n).aemeasurable)
  have hB := bootstrap_quantile_consistency B ν hstrict hconv hb (fun n => (hmb n).aemeasurable)
  have h := random_interval_probability hT hZ hA hB hm hma hmb
    (fun n ω => distributionQuantile_mono (B n ω) ha hb hab)
  rw [cdf_eq_real, cdf_eq_real, distributionQuantile_exact ν a ha,
    distributionQuantile_exact ν b hb] at h
  have he (n) : P.real {ω | θ ∈ Icc
      (E n ω - distributionQuantile (B n ω) b * S n ω)
      (E n ω - distributionQuantile (B n ω) a * S n ω)} =
      P.real {ω | (E n ω - θ) / S n ω ∈ Icc
        (distributionQuantile (B n ω) a) (distributionQuantile (B n ω) b)} := by
    apply measureReal_congr
    filter_upwards [hS n] with ω hω
    exact propext (location_pivot_inversion _ _ _ _ _ hω).symm
  simpa only [he] using h

end LectureNotes
