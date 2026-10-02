import LectureNotes.NormalConjugacy
import LectureNotes.ExponentialFamilySufficiency
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory WithLp

variable {d : ℕ}

theorem stdGaussian_product_density :
    (volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity
      (fun z => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (z i))) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  let e := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have hbase : volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) =
      gaussianReal 0 1 := by
    rw [gaussianReal_of_var_ne_zero _ one_ne_zero]
    rfl
  have hpi := iid_product_withDensity volume (gaussianReal 0 1)
    (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) (by fun_prop) hbase d
  rw [← map_pi_eq_stdGaussian]
  change _ = (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map e
  rw [hpi, map_withDensity_equiv _ e _ (by fun_prop)]
  have hvol : (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).map e = volume :=
    (PiLp.volume_preserving_toLp (Fin d)).map_eq
  rw [hvol]
  congr 1
  funext z
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)

theorem stdGaussian_product_density_integrable :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => ∏ i, gaussianPDFReal 0 1 (z i)) volume := by
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding]
  exact Integrable.fintype_prod (fun _ => integrable_gaussianPDFReal 0 1)

theorem stdGaussian_product_density_integral :
    (∫ z : EuclideanSpace ℝ (Fin d), ∏ i, gaussianPDFReal 0 1 (z i)) = 1 := by
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding]
  change (∫ z : Fin d → ℝ, ∏ i, gaussianPDFReal 0 1 (z i)) = 1
  rw [integral_fintype_prod_volume_eq_prod]
  simp [integral_gaussianPDFReal_eq_one 0 one_ne_zero]

theorem stdGaussian_product_density_eq_kernel (z : EuclideanSpace ℝ (Fin d)) :
    (∏ i, gaussianPDFReal 0 1 (z i)) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-‖z‖ ^ 2 / 2) := by
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Finset.sum_div, ← Finset.sum_neg_distrib]

theorem normalized_stdGaussian_kernel :
    bayesUpdate volume (fun z : EuclideanSpace ℝ (Fin d) => Real.exp (-‖z‖ ^ 2 / 2)) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  have hnormalized :
      bayesUpdate volume (fun z : EuclideanSpace ℝ (Fin d) => ∏ i, gaussianPDFReal 0 1 (z i)) =
        stdGaussian (EuclideanSpace ℝ (Fin d)) := by
    unfold bayesUpdate evidence
    rw [stdGaussian_product_density_integral]
    simpa only [div_one] using stdGaussian_product_density (d := d)
  simp_rw [stdGaussian_product_density_eq_kernel] at hnormalized
  rw [bayesUpdate_scale _ _ (pow_ne_zero d (inv_ne_zero
    ((Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).ne')))] at hnormalized
  exact hnormalized

theorem stdGaussian_kernel_integrable :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => Real.exp (-‖z‖ ^ 2 / 2)) volume := by
  have hc : (Real.sqrt (2 * Real.pi))⁻¹ ^ d ≠ 0 :=
    pow_ne_zero d (inv_ne_zero ((Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).ne'))
  have hi := (stdGaussian_product_density_integrable (d := d)).const_mul
    (((Real.sqrt (2 * Real.pi))⁻¹ ^ d)⁻¹)
  simpa only [stdGaussian_product_density_eq_kernel, ← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hi

theorem stdGaussian_kernel_integral_pos :
    0 < ∫ z : EuclideanSpace ℝ (Fin d), Real.exp (-‖z‖ ^ 2 / 2) := by
  have he := stdGaussian_product_density_integral (d := d)
  simp_rw [stdGaussian_product_density_eq_kernel] at he
  rw [integral_const_mul] at he
  have hc : 0 < (Real.sqrt (2 * Real.pi))⁻¹ ^ d := by positivity
  nlinarith

end LectureNotes
