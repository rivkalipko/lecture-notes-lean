import LectureNotes.ExponentialFamilySufficiency

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped ENNReal NNReal

/-- The standard Gaussian density in Euclidean coordinates. -/
theorem stdGaussian_radial_density (n : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) = volume.withDensity (fun x =>
      ENNReal.ofReal ((1 / Real.sqrt (2 * Real.pi)) ^ n * Real.exp (-‖x‖ ^ 2 / 2))) := by
  rw [← map_pi_eq_stdGaussian]
  rw [iid_product_withDensity volume (gaussianReal 0 1) (gaussianPDF 0 1)
    (measurable_gaussianPDF 0 1) (gaussianReal_of_var_ne_zero 0 (by norm_num)).symm n]
  let e := MeasurableEquiv.toLp 2 (Fin n → ℝ)
  change ((volume : Measure (Fin n → ℝ)).withDensity (fun x => ∏ i, gaussianPDF 0 1 (x i))).map e = _
  rw [map_withDensity_equiv _ e _ (by fun_prop)]
  rw [show (volume : Measure (Fin n → ℝ)).map e = volume from
    (PiLp.volume_preserving_toLp (Fin n)).map_eq]
  congr 1
  funext x
  simp only [Function.comp_def, gaussianPDF_def, gaussianPDFReal, NNReal.coe_one,
    mul_one, sub_zero]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (by positivity) (Real.exp_pos _).le)]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  simp only [one_div]
  congr 2
  change (∑ i, -(x i) ^ 2 / 2) = -‖x‖ ^ 2 / 2
  rw [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_div, Finset.sum_neg_distrib]

/-- The Gaussian factor changes behavior at infinity, but not the
integrability threshold of a power at zero. -/
theorem integrableOn_power_gaussian_iff (a : ℝ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun r : ℝ => r ^ a * Real.exp (-b * r ^ 2)) (Ioi 0) ↔ -1 < a := by
  constructor
  · intro h
    have hi := h.mono_set (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hx => hx.1)
    have hp : IntegrableOn (fun r : ℝ => r ^ a) (Ioo 0 1) := by
      apply (hi.const_mul (Real.exp b)).mono' (by fun_prop)
      filter_upwards [ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1))] with r hr
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hr.1.le a)]
      have hf : 1 ≤ Real.exp b * Real.exp (-b * r ^ 2) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        nlinarith [sq_nonneg r, mul_nonneg hb.le (show 0 ≤ 1 - r ^ 2 by nlinarith [hr.1, hr.2])]
      have hp := Real.rpow_nonneg hr.1.le a
      nlinarith [mul_le_mul_of_nonneg_left hf hp]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mp hp
  · exact fun ha => integrableOn_rpow_mul_exp_neg_mul_sq hb ha

/-- An inverse radial moment of the standard Gaussian is finite precisely
when its exponent is smaller than the dimension. -/
theorem stdGaussian_inverse_norm_integrable_iff {n : ℕ} (hn : 0 < n) (s : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ (-s))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ↔ s < n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hc : (1 / Real.sqrt (2 * Real.pi)) ^ n ≠ 0 := by positivity
  rw [stdGaussian_radial_density]
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop) (by filter_upwards [] with x; exact ENNReal.ofReal_lt_top)]
  have he : (fun x : EuclideanSpace ℝ (Fin n) =>
      (ENNReal.ofReal ((1 / Real.sqrt (2 * Real.pi)) ^ n * Real.exp (-‖x‖ ^ 2 / 2))).toReal •
        ‖x‖ ^ (-s)) = fun x => (1 / Real.sqrt (2 * Real.pi)) ^ n *
          (‖x‖ ^ (-s) * Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)) := by
    funext x
    rw [ENNReal.toReal_ofReal (by positivity)]
    simp only [smul_eq_mul]
    rw [show -‖x‖ ^ 2 / 2 = -(1 / 2 : ℝ) * ‖x‖ ^ 2 by ring]
    ring
  rw [he, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc)]
  rw [integrable_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (f := fun r : ℝ => r ^ (-s) * Real.exp (-(1 / 2 : ℝ) * r ^ 2))]
  have he' : (fun r : ℝ => r ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1) •
      (r ^ (-s) * Real.exp (-(1 / 2 : ℝ) * r ^ 2))) =ᵐ[volume.restrict (Ioi 0)]
      fun r => r ^ ((n : ℝ) - 1 - s) * Real.exp (-(1 / 2 : ℝ) * r ^ 2) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with r hr
    simp only [smul_eq_mul, finrank_euclideanSpace, Fintype.card_fin]
    rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hr]
    congr 2
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  change Integrable _ (volume.restrict (Ioi (0 : ℝ))) ↔ _
  rw [integrable_congr he']
  change IntegrableOn _ (Ioi (0 : ℝ)) volume ↔ _
  rw [integrableOn_power_gaussian_iff _ (by norm_num : (0 : ℝ) < 1 / 2)]
  constructor <;> intro h <;> linarith

end LectureNotes
