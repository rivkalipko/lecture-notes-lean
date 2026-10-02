import LectureNotes.UniformEndpoint

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

theorem beta_shape_one {a : ℝ} (ha : 0 < a) : beta a 1 = 1 / a := by
  unfold beta
  rw [Real.Gamma_one, mul_one, Real.Gamma_add_one ha.ne']
  field_simp [(Real.Gamma_pos_of_pos ha).ne']

theorem beta_shape_one_density {a : ℝ} (ha : 0 < a) (x : ℝ) :
    betaPDFReal a 1 x = (Ioo (0 : ℝ) 1).indicator (fun x => a * x ^ (a - 1)) x := by
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · simp [betaPDFReal, hx.1, hx.2, hx, beta_shape_one ha]
  · have hh : ¬(0 < x ∧ x < 1) := hx
    simp [betaPDFReal, hh, hx]

theorem beta_shape_one_cdf {a : ℝ} (ha : 0 < a) (t : ℝ) :
    cdf (betaMeasure a 1) t = max (min t 1) 0 ^ a := by
  have : IsProbabilityMeasure (betaMeasure a 1) := isProbabilityMeasureBeta ha zero_lt_one
  have heq : betaPDFReal a 1 =ᵐ[volume]
      (Icc (0 : ℝ) 1).indicator (fun x => a * x ^ (a - 1)) := by
    filter_upwards [Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)] with x hx
    rw [beta_shape_one_density ha]
    have hiff : x ∈ Ioo (0 : ℝ) 1 ↔ x ∈ Icc (0 : ℝ) 1 := Eq.to_iff hx
    by_cases hx' : x ∈ Ioo (0 : ℝ) 1
    · rw [indicator_of_mem hx', indicator_of_mem (hiff.mp hx')]
    · rw [indicator_of_notMem hx', indicator_of_notMem (fun h => hx' (hiff.mpr h))]
  rw [cdf_eq_real]
  change (volume.withDensity (fun x => ENNReal.ofReal (betaPDFReal a 1 x))).real (Iic t) = _
  rw [density_event_eq_integral (beta_density_integrable ha zero_lt_one)
    (beta_density_nonneg ha zero_lt_one) _ measurableSet_Iic]
  rw [setIntegral_congr_ae measurableSet_Iic (heq.mono (fun _ hx _ => hx)),
    integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  have hset : Icc (0 : ℝ) 1 ∩ Iic t = Icc 0 (min t 1) := by ext x; simp; tauto
  rw [hset]
  by_cases ht : 0 ≤ min t 1
  · rw [max_eq_left ht, integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht, integral_rpow (Or.inl (by linarith : -1 < a - 1))]
    rw [sub_add_cancel, Real.zero_rpow ha.ne', sub_zero]
    exact mul_div_cancel₀ _ ha.ne'
  · have he : Icc (0 : ℝ) (min t 1) = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge ht)
    simp [he, max_eq_right (le_of_not_ge ht), Real.zero_rpow ha.ne']

/-- The actual distribution of the square of a uniform [0,1] observation. -/
def uniformUnitSquareLaw : Measure ℝ := (uniformEndpointLaw 1).map (fun x : ℝ => x ^ 2)

instance uniformUnitSquareLaw_probability : IsProbabilityMeasure uniformUnitSquareLaw := by
  have := uniformEndpointLaw_probability (by norm_num : (0 : ℝ) < 1)
  exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

theorem uniformUnitSquare_cdf (t : ℝ) :
    cdf uniformUnitSquareLaw t = Real.sqrt (max (min t 1) 0) := by
  rw [cdf_eq_real, uniformUnitSquareLaw,
    map_measureReal_apply (by fun_prop) measurableSet_Iic]
  have hu : uniformEndpointLaw 1 = volume.restrict (Icc (0 : ℝ) 1) := by simp [uniformEndpointLaw]
  rw [hu, measureReal_restrict_apply (measurableSet_Iic.preimage (by fun_prop))]
  by_cases ht : 0 ≤ t
  · have hs : (fun x : ℝ => x ^ 2) ⁻¹' Iic t ∩ Icc 0 1 = Icc 0 (min (Real.sqrt t) 1) := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc, le_min_iff]
      constructor
      · rintro ⟨hx, hx0, hx1⟩
        exact ⟨hx0, (Real.le_sqrt hx0 ht).mpr hx, hx1⟩
      · rintro ⟨hx0, hxs, hx1⟩
        exact ⟨(Real.le_sqrt hx0 ht).mp hxs, hx0, hx1⟩
    rw [hs, Real.volume_real_Icc, sub_zero, max_eq_left (le_min (Real.sqrt_nonneg t) zero_le_one)]
    by_cases ht1 : t ≤ 1
    · rw [min_eq_left (Real.sqrt_le_one.mpr ht1), min_eq_left ht1, max_eq_left ht]
    · have ht1' : 1 ≤ t := le_of_not_ge ht1
      rw [min_eq_right (Real.one_le_sqrt.mpr ht1'), min_eq_right ht1', max_eq_left zero_le_one, Real.sqrt_one]
  · have hs : (fun x : ℝ => x ^ 2) ⁻¹' Iic t ∩ Icc 0 1 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact not_le_of_gt (lt_of_not_ge ht) ((sq_nonneg x).trans hx.1)
    rw [hs, measureReal_empty]
    have hm : min t 1 ≤ 0 := (min_le_left _ _).trans (le_of_not_ge ht)
    rw [max_eq_right hm, Real.sqrt_zero]

theorem uniformUnitSquare_eq_beta : uniformUnitSquareLaw = betaMeasure (1 / 2) 1 := by
  have : IsProbabilityMeasure (betaMeasure (1 / 2) 1) := isProbabilityMeasureBeta (by norm_num) zero_lt_one
  apply Measure.eq_of_cdf
  ext t
  rw [uniformUnitSquare_cdf, beta_shape_one_cdf (by norm_num : (0 : ℝ) < 1 / 2), Real.sqrt_eq_rpow]

/-- L1 Example 2: the density is 1/(2 sqrt y) on the open unit interval.
Endpoint choices do not alter the probability law. -/
theorem uniformUnitSquare_density :
    uniformUnitSquareLaw = volume.withDensity (fun y => ENNReal.ofReal
      ((Ioo (0 : ℝ) 1).indicator (fun y => 1 / (2 * Real.sqrt y)) y)) := by
  rw [uniformUnitSquare_eq_beta]
  change volume.withDensity (fun y => ENNReal.ofReal (betaPDFReal (1 / 2) 1 y)) = _
  congr 1
  funext y
  rw [beta_shape_one_density (by norm_num : (0 : ℝ) < 1 / 2)]
  congr 1
  by_cases hy : y ∈ Ioo (0 : ℝ) 1
  · rw [indicator_of_mem hy, indicator_of_mem hy]
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by ring,
      Real.rpow_neg hy.1.le, ← Real.sqrt_eq_rpow]
    ring
  · rw [indicator_of_notMem hy, indicator_of_notMem hy]

end LectureNotes
