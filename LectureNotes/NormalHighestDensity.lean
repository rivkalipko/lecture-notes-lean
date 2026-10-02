import LectureNotes.HighestDensity
import LectureNotes.QuantileReparameterization
import LectureNotes.NormalTestPower

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- Standard Gaussian quantiles have the symmetry used in equal-tailed
credible intervals and two-sided normal tests. -/
theorem standardNormal_quantile_symmetry {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    distributionQuantile (gaussianReal 0 1) (1 - q) =
      -distributionQuantile (gaussianReal 0 1) q := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have h := distributionQuantile_continuous_strictAnti (gaussianReal 0 1)
    (gaussian_cdf_strictMono 0 1 (by norm_num)) (continuous_neg)
    (show StrictAnti (fun x : ℝ => -x) from fun _ _ h => neg_lt_neg h) hq
  rw [gaussianReal_map_neg, neg_zero] at h
  linarith

theorem standardNormal_quantile_half :
    distributionQuantile (gaussianReal 0 1) (1 / 2) = 0 := by
  have h := standardNormal_quantile_symmetry (q := 1 / 2) (by constructor <;> norm_num)
  norm_num at h
  linarith

theorem standardNormal_quantile_pos {q : ℝ} (hq : q ∈ Ioo (1 / 2 : ℝ) 1) :
    0 < distributionQuantile (gaussianReal 0 1) q := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have h := distributionQuantile_strictMono (gaussianReal 0 1)
    (a := 1 / 2) (by constructor <;> norm_num) (show q ∈ Ioo (0 : ℝ) 1 from
      ⟨by linarith [hq.1], hq.2⟩) hq.1
  rwa [standardNormal_quantile_half] at h

/-- A central Gaussian interval is exactly a density superlevel set, with
the boundary density as its cutoff. -/
theorem gaussian_highestDensityRegion_eq_Icc (m : ℝ) (v : ℝ≥0) (hv : 0 < v)
    (r : ℝ) (hr : 0 ≤ r) :
    highestDensityRegion (gaussianPDFReal m v) (gaussianPDFReal m v (m + r)) =
      Icc (m - r) (m + r) := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hden : (0 : ℝ) < 2 * v := by positivity
  have hfactor : (0 : ℝ) < (Real.sqrt (2 * Real.pi * v))⁻¹ := by positivity
  ext x
  simp only [highestDensityRegion, mem_ofPred_eq, gaussianPDFReal]
  rw [mul_le_mul_iff_right₀ hfactor, Real.exp_le_exp, div_le_div_iff_of_pos_right hden,
    show m + r - m = r by ring, neg_le_neg_iff]
  rw [← sq_abs (x - m), sq_le_sq₀ (abs_nonneg _) hr, abs_le]
  simp only [mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Every centered Gaussian interval minimizes Lebesgue volume among all
measurable regions having at least its posterior probability. -/
theorem gaussian_central_interval_minimum_volume (m : ℝ) (v : ℝ≥0) (hv : 0 < v)
    (r : ℝ) (hr : 0 ≤ r) (C : Set ℝ) (hC : MeasurableSet C)
    (hc : (gaussianReal m v).real (Icc (m - r) (m + r)) ≤ (gaussianReal m v).real C) :
    volume (Icc (m - r) (m + r)) ≤ volume C := by
  have h := highest_density_minimum_volume (ν := volume)
    (measurable_gaussianPDFReal m v) (integrable_gaussianPDFReal m v)
    (gaussianPDFReal_nonneg m v) (gaussianPDFReal_pos m v (m + r) hv.ne') C hC
  rw [gaussian_highestDensityRegion_eq_Icc m v hv r hr] at h
  apply h
  rw [gaussianReal_of_var_ne_zero m hv.ne'] at hc
  exact hc

/-- The equal-tailed Gaussian credible interval has exact posterior content
and minimum volume even among measurable competitors that are not intervals. -/
theorem gaussian_equalTailed_minimum_volume (m : ℝ) (v : ℝ≥0) (hv : 0 < v)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    let r := distributionQuantile (gaussianReal 0 1) (1 - α / 2) * Real.sqrt v
    (gaussianReal m v).real (Icc (m - r) (m + r)) = 1 - α ∧
      ∀ C : Set ℝ, MeasurableSet C → 1 - α ≤ (gaussianReal m v).real C →
        volume (Icc (m - r) (m + r)) ≤ volume C := by
  let r := distributionQuantile (gaussianReal 0 1) (1 - α / 2) * Real.sqrt v
  have ha : α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hb : 1 - α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hsym : distributionQuantile (gaussianReal 0 1) (α / 2) =
      -distributionQuantile (gaussianReal 0 1) (1 - α / 2) := by
    have h := standardNormal_quantile_symmetry ha
    linarith
  have hcal := gaussian_credible_interval m v hv ha hb (by linarith [hα.2])
  rw [hsym, neg_mul, ← sub_eq_add_neg] at hcal
  have hcal' : (gaussianReal m v).real (Icc (m - r) (m + r)) = 1 - α := by
    convert hcal using 1; ring
  have hr : 0 ≤ r := mul_nonneg
    (standardNormal_quantile_pos ⟨by linarith [hα.2], hb.2⟩).le (Real.sqrt_nonneg _)
  refine ⟨hcal', fun C hC hc => ?_⟩
  apply gaussian_central_interval_minimum_volume m v hv r hr C hC
  rwa [hcal']

end LectureNotes
