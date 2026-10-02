import LectureNotes.NeymanScott
import LectureNotes.NormalVarianceRisk

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- The log of the actual normal likelihood, with both mean and variance
unknown. The variance parameter is strictly positive. -/
theorem normal_sample_log_density {n : ℕ} (x : Fin n → ℝ) (μ : ℝ)
    {v : ℝ≥0} (hv : 0 < v) :
    Real.log (∏ i, gaussianPDFReal μ v (x i)) =
      -(n : ℝ) / 2 * Real.log (2 * Real.pi) - n / 2 * Real.log v -
        (∑ i, (x i - μ) ^ 2) / (2 * v) := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hc : (Real.sqrt (2 * Real.pi * v))⁻¹ ≠ 0 := by positivity
  have hp : 2 * Real.pi ≠ 0 := by positivity
  rw [Real.log_prod (fun i _ => (gaussianPDFReal_pos _ _ _ hv.ne').ne')]
  simp only [gaussianPDFReal, Real.log_mul hc (Real.exp_ne_zero _), Real.log_exp,
    Real.log_inv, Real.log_sqrt (by positivity : 0 ≤ 2 * Real.pi * (v : ℝ)),
    Real.log_mul hp hvR.ne', Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div,
    Finset.sum_neg_distrib]
  ring

/-- Positive empirical variance gives the global normal likelihood maximum
at the sample mean and the central second moment with denominator n. -/
theorem normal_mean_variance_maximizes_density {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (ha : 0 < empiricalVariance x) (μ : ℝ)
    {v : ℝ≥0} (hv : 0 < v) :
    (∏ i, gaussianPDFReal μ v (x i)) ≤
      ∏ i, gaussianPDFReal (sampleMean x) ⟨empiricalVariance x, ha.le⟩ (x i) := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have haN : (0 : ℝ≥0) < ⟨empiricalVariance x, ha.le⟩ := ha
  have he : (∑ i, (x i - sampleMean x) ^ 2) = n * empiricalVariance x := by
    unfold empiricalVariance
    field_simp
  apply (Real.log_le_log_iff
    (Finset.prod_pos (fun i _ => gaussianPDFReal_pos _ _ _ hv.ne'))
    (Finset.prod_pos (fun i _ => gaussianPDFReal_pos _ _ _ haN.ne'))).mp
  rw [normal_sample_log_density x μ hv, normal_sample_log_density x _ haN,
    sum_squared_error_decomposition hn x μ, he]
  change -(n : ℝ) / 2 * Real.log (2 * Real.pi) - n / 2 * Real.log v -
      (n * empiricalVariance x + n * (μ - sampleMean x) ^ 2) / (2 * v) ≤
    -(n : ℝ) / 2 * Real.log (2 * Real.pi) - n / 2 * Real.log (empiricalVariance x) -
      (n * empiricalVariance x) / (2 * empiricalVariance x)
  have hm := neymanScott_profile_maximum hn ha hvR
  have hs : 0 ≤ (n : ℝ) * (μ - sampleMean x) ^ 2 / v := by positivity
  have hc : (n : ℝ) * empiricalVariance x / (2 * empiricalVariance x) = n / 2 := by
    field_simp
  rw [hc]
  have he' : ((n : ℝ) * empiricalVariance x + n * (μ - sampleMean x) ^ 2) /
      (2 * v) = ((n : ℝ) * empiricalVariance x / v + n * (μ - sampleMean x) ^ 2 / v) / 2 := by ring
  rw [he']
  linarith

/-- If the empirical variance is zero, the claimed positive-variance MLE
does not exist. Fitting the mean and halving any positive candidate variance
strictly increases the actual likelihood. -/
theorem normal_zero_empiricalVariance_no_maximum {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (ha : empiricalVariance x = 0) (μ : ℝ)
    {v : ℝ≥0} (hv : 0 < v) :
    (∏ i, gaussianPDFReal μ v (x i)) <
      ∏ i, gaussianPDFReal (sampleMean x) (v / 2) (x i) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hvN : (0 : ℝ≥0) < v / 2 := div_pos hv (by norm_num)
  have hz : (∑ i, (x i - sampleMean x) ^ 2) = 0 := by
    unfold empiricalVariance at ha
    exact (div_eq_zero_iff.mp ha).resolve_right hnR.ne'
  apply (Real.log_lt_log_iff
    (Finset.prod_pos (fun i _ => gaussianPDFReal_pos _ _ _ hv.ne'))
    (Finset.prod_pos (fun i _ => gaussianPDFReal_pos _ _ _ hvN.ne'))).mp
  rw [normal_sample_log_density x μ hv, normal_sample_log_density x _ hvN, hz]
  simp only [zero_div, sub_zero, NNReal.coe_div, NNReal.coe_ofNat]
  rw [Real.log_div hvR.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  have hres : 0 ≤ (∑ i, (x i - μ) ^ 2) / (2 * v) := by positivity
  have hlog : 0 < (n : ℝ) * Real.log 2 := mul_pos hnR (Real.log_pos (by norm_num))
  nlinarith

/-- Under a nondegenerate normal sampling model and n>1, the exceptional
zero-variance sample has probability zero. -/
theorem normal_empiricalVariance_pos_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 1 < n)
    {X : Fin n → Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hv : 0 < v)
    (hX : ∀ i, HasLaw (X i) (gaussianReal μ v) P) (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P, 0 < empiricalVariance (fun i => X i ω) := by
  filter_upwards [normal_sampleVariance_pos hn hv hX hind] with ω hω
  rw [empiricalVariance_eq_scaled_sampleVariance hn]
  apply mul_pos _ hω
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  exact div_pos (sub_pos.mpr hnR) (by positivity)

end LectureNotes
