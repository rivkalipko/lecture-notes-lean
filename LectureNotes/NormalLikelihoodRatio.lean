import LectureNotes.BoundaryNormalMLE
import LectureNotes.LikelihoodRatio
import LectureNotes.NormalConfidenceIntervals
import LectureNotes.NormalHighestDensity

set_option autoImplicit false

/-! L9's normal likelihood-ratio example. The statistic is identified from the
suprema of the actual product density, and its finite-sample null law and size
are proved for a nonempty independent sample with known unit variance. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- The actual likelihood for a normal sample with known unit variance. -/
def normalUnitLikelihood {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) : ℝ :=
  ∏ i, gaussianPDFReal θ 1 (x i)

theorem normalUnitLikelihood_pos {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) :
    0 < normalUnitLikelihood x θ :=
  Finset.prod_pos (fun i _ => gaussianPDFReal_pos θ 1 (x i) (by norm_num))

/-- A nonempty sample has the sample mean as its global maximum. -/
theorem normalUnitLikelihood_isMLE {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    IsMLE normalUnitLikelihood x (sampleMean x) := by
  intro θ
  apply (Real.log_le_log_iff (normalUnitLikelihood_pos x θ)
    (normalUnitLikelihood_pos x (sampleMean x))).mp
  simp only [normalUnitLikelihood, normal_unit_sample_log_density]
  rw [sum_squared_error_decomposition hn x θ]
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg (θ - sampleMean x))]

/-- The maximum is unique; this does not merely posit a solution of the score equation. -/
theorem normalUnitLikelihood_isMLE_iff {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (θ : ℝ) :
    IsMLE normalUnitLikelihood x θ ↔ θ = sampleMean x := by
  refine ⟨fun h => ?_, fun h => h ▸ normalUnitLikelihood_isMLE hn x⟩
  have he := le_antisymm (h (sampleMean x)) (normalUnitLikelihood_isMLE hn x θ)
  have hl := congrArg Real.log he
  simp only [normalUnitLikelihood, normal_unit_sample_log_density] at hl
  rw [sum_squared_error_decomposition hn x θ] at hl
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hz : (θ - sampleMean x) ^ 2 = 0 := by nlinarith
  nlinarith [sq_nonneg (θ - sampleMean x)]

/-- The ratio of suprema equals the displayed ratio of maximized likelihoods. -/
theorem normal_likelihoodRatio_eq_ratio {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (θ₀ : ℝ) :
    likelihoodRatio normalUnitLikelihood {θ₀} x =
      normalUnitLikelihood x θ₀ / normalUnitLikelihood x (sampleMean x) := by
  exact likelihoodRatio_eq_of_maximizers normalUnitLikelihood {θ₀} x (mem_singleton θ₀)
    (by intro θ hθ; rw [mem_singleton_iff.mp hθ]) (normalUnitLikelihood_isMLE hn x)

/-- L9's cancellation of the residual sum of squares, for the actual likelihood ratio. -/
theorem normal_likelihoodRatio_formula {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (θ₀ : ℝ) :
    likelihoodRatio normalUnitLikelihood {θ₀} x =
      Real.exp (-(n : ℝ) / 2 * (sampleMean x - θ₀) ^ 2) := by
  rw [normal_likelihoodRatio_eq_ratio hn]
  have hp := div_pos (normalUnitLikelihood_pos x θ₀)
    (normalUnitLikelihood_pos x (sampleMean x))
  rw [← Real.exp_log hp]
  congr 1
  rw [Real.log_div (normalUnitLikelihood_pos x θ₀).ne'
    (normalUnitLikelihood_pos x (sampleMean x)).ne']
  simp only [normalUnitLikelihood, normal_unit_sample_log_density]
  rw [sum_squared_error_decomposition hn x θ₀]
  ring

/-- For an empty sample both suprema equal one and the ratio carries no information. -/
theorem normal_likelihoodRatio_empty (x : Fin 0 → ℝ) (θ₀ : ℝ) :
    likelihoodRatio normalUnitLikelihood {θ₀} x = 1 := by
  have hm : IsMLE normalUnitLikelihood x 0 := by intro θ; simp [normalUnitLikelihood]
  rw [likelihoodRatio_eq_of_maximizers normalUnitLikelihood {θ₀} x (mem_singleton θ₀)
    (by intro θ hθ; rw [mem_singleton_iff.mp hθ]) hm]
  simp [normalUnitLikelihood]

/-- The exact log-likelihood-ratio statistic is the squared standardized mean. -/
theorem normal_minus_two_log_likelihoodRatio {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (θ₀ : ℝ) :
    -2 * Real.log (likelihoodRatio normalUnitLikelihood {θ₀} x) =
      n * (sampleMean x - θ₀) ^ 2 := by
  rw [normal_likelihoodRatio_formula hn, Real.log_exp]
  ring

/-- Small likelihood ratios correspond to large squared errors. Both boundaries
are included here, as in the definition of the LRT rejection rule. -/
theorem normal_likelihoodRatio_reject_iff {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (θ₀ q : ℝ) :
    likelihoodRatio normalUnitLikelihood {θ₀} x ≤ Real.exp (-q / 2) ↔
      q ≤ n * (sampleMean x - θ₀) ^ 2 := by
  rw [normal_likelihoodRatio_formula hn, Real.exp_le_exp]
  constructor <;> intro h <;> linarith

/-- The normal LRT rejection region has the usual absolute-error form. -/
theorem normal_likelihoodRatio_reject_abs {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (θ₀ : ℝ) {q : ℝ} (_hq : 0 ≤ q) :
    likelihoodRatio normalUnitLikelihood {θ₀} x ≤ Real.exp (-q / 2) ↔
      Real.sqrt (q / n) ≤ |sampleMean x - θ₀| := by
  rw [normal_likelihoodRatio_reject_iff hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mul_comm (n : ℝ), ← div_le_iff₀ hnR]
  rw [Real.sqrt_le_iff]
  simp only [abs_nonneg, true_and, sq_abs]

/-- In this model the chi-square law is exact at every positive sample size. -/
theorem normal_likelihoodRatio_null_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {θ₀ : ℝ}
    (hX : ∀ i, HasLaw (X i) (gaussianReal θ₀ 1) P) (hind : iIndepFun X P) :
    HasLaw (fun ω => -2 * Real.log
      (likelihoodRatio normalUnitLikelihood {θ₀} (fun i => X i ω))) (chiSquared 1) P := by
  have hv : (0 : ℝ≥0) < 1 / n := div_pos zero_lt_one (by exact_mod_cast hn)
  have h := standard_normal_square (normal_standardize hv (normal_sampleMean hn hX hind))
  convert! h using 1
  funext ω
  rw [normal_minus_two_log_likelihoodRatio hn, div_pow]
  simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast]
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 / n)]
  field_simp

/-- The rejection boundary has zero probability under the null. Thus the
notes' strict and non-strict versions of this rejection rule have the same size. -/
theorem normal_likelihoodRatio_boundary_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {θ₀ : ℝ}
    (hX : ∀ i, HasLaw (X i) (gaussianReal θ₀ 1) P) (hind : iIndepFun X P) (q : ℝ) :
    P.real {ω | likelihoodRatio normalUnitLikelihood {θ₀} (fun i => X i ω) =
      Real.exp (-q / 2)} = 0 := by
  have : NullSingletonClass (chiSquared 1) := chiSquared_nullSingletonClass (by decide)
  have he : {ω | likelihoodRatio normalUnitLikelihood {θ₀} (fun i => X i ω) =
      Real.exp (-q / 2)} = {ω | -2 * Real.log
        (likelihoodRatio normalUnitLikelihood {θ₀} (fun i => X i ω)) = q} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [normal_minus_two_log_likelihoodRatio hn, normal_likelihoodRatio_formula hn,
      Real.exp_eq_exp]
    constructor <;> intro h <;> linarith
  rw [he, (normal_likelihoodRatio_null_law hn hX hind).measureReal_eq
    (p := fun x => x = q) (measurableSet_singleton q)]
  change (chiSquared 1).real {q} = 0
  simp [measureReal_def]

/-- Exact size, calibrated by the (atomless) chi-square null distribution.
The cutoff is derived from the actual ratio of the likelihood suprema. -/
theorem normal_likelihoodRatio_exact_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {θ₀ : ℝ}
    (hX : ∀ i, HasLaw (X i) (gaussianReal θ₀ 1) P) (hind : iIndepFun X P)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    P.real {ω | likelihoodRatio normalUnitLikelihood {θ₀} (fun i => X i ω) ≤
      Real.exp (-distributionQuantile (chiSquared 1) (1 - α) / 2)} = α := by
  have : NullSingletonClass (chiSquared 1) := chiSquared_nullSingletonClass (by decide)
  have hq : 1 - α ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hα.1, hα.2]
  let q := distributionQuantile (chiSquared 1) (1 - α)
  have he : {ω | likelihoodRatio normalUnitLikelihood {θ₀} (fun i => X i ω) ≤
      Real.exp (-q / 2)} = {ω | q ≤ -2 * Real.log
        (likelihoodRatio normalUnitLikelihood {θ₀} (fun i => X i ω))} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [normal_minus_two_log_likelihoodRatio hn]
    exact normal_likelihoodRatio_reject_iff hn _ _ _
  rw [he, (normal_likelihoodRatio_null_law hn hX hind).measureReal_eq measurableSet_Ici]
  change (chiSquared 1).real (Ici q) = α
  rw [← compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ,
    measureReal_congr Iio_ae_eq_Iic, distributionQuantile_exact _ _ hq]
  ring

/-- Squaring a standard normal converts its central interval to a chi-square
lower tail; this connects the two exact critical-value presentations. -/
theorem chiSquared_one_central_normal (z : ℝ) (hz : 0 ≤ z) :
    (chiSquared 1).real (Iic (z ^ 2)) = (gaussianReal 0 1).real (Icc (-z) z) := by
  have h := standard_normal_square
    (show HasLaw id (gaussianReal 0 1) (gaussianReal 0 1) from HasLaw.id)
  have he := h.measureReal_eq (p := fun x => x ≤ z ^ 2) measurableSet_Iic
  change (gaussianReal 0 1).real {x | x ^ 2 ≤ z ^ 2} = (chiSquared 1).real (Iic (z ^ 2)) at he
  rw [← he]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, mem_Icc]
  rw [← sq_abs x, sq_le_sq₀ (abs_nonneg x) hz, abs_le]

/-- L9's displayed standard-normal critical value gives exact size for the
likelihood ratio, with the boundary included as in its definition. -/
theorem normal_likelihoodRatio_normal_quantile_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {θ₀ : ℝ}
    (hX : ∀ i, HasLaw (X i) (gaussianReal θ₀ 1) P) (hind : iIndepFun X P)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    P.real {ω | likelihoodRatio normalUnitLikelihood {θ₀} (fun i => X i ω) ≤
      Real.exp (-(distributionQuantile (gaussianReal 0 1) (1 - α / 2)) ^ 2 / 2)} = α := by
  have : NullSingletonClass (chiSquared 1) := chiSquared_nullSingletonClass (by decide)
  let z := distributionQuantile (gaussianReal 0 1) (1 - α / 2)
  have hz : 0 < z := standardNormal_quantile_pos ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hcal : (gaussianReal 0 1).real (Icc (-z) z) = 1 - α := by
    simpa [z] using (gaussian_equalTailed_minimum_volume 0 1 (by norm_num) hα).1
  have he : {ω | likelihoodRatio normalUnitLikelihood {θ₀} (fun i => X i ω) ≤
      Real.exp (-z ^ 2 / 2)} = {ω | z ^ 2 ≤ -2 * Real.log
        (likelihoodRatio normalUnitLikelihood {θ₀} (fun i => X i ω))} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [normal_minus_two_log_likelihoodRatio hn]
    exact normal_likelihoodRatio_reject_iff hn _ _ _
  rw [he, (normal_likelihoodRatio_null_law hn hX hind).measureReal_eq measurableSet_Ici]
  change (chiSquared 1).real (Ici (z ^ 2)) = α
  rw [← compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ,
    measureReal_congr Iio_ae_eq_Iic, chiSquared_one_central_normal z hz.le, hcal]
  ring

/-- The same calibrated LRT is a two-sided test of the sample mean, with the
source's critical distance `z_(1-α/2) / sqrt n`. -/
theorem normal_likelihoodRatio_normal_quantile_region {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (θ₀ : ℝ) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    likelihoodRatio normalUnitLikelihood {θ₀} x ≤
      Real.exp (-(distributionQuantile (gaussianReal 0 1) (1 - α / 2)) ^ 2 / 2) ↔
      distributionQuantile (gaussianReal 0 1) (1 - α / 2) / Real.sqrt n ≤
        |sampleMean x - θ₀| := by
  have hz := standardNormal_quantile_pos
    (show 1 - α / 2 ∈ Ioo (1 / 2 : ℝ) 1 from ⟨by linarith [hα.2], by linarith [hα.1]⟩)
  rw [normal_likelihoodRatio_reject_abs hn x θ₀ (sq_nonneg _),
    Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hz.le]

end LectureNotes
