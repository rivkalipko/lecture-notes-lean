import LectureNotes.SigmaFiniteFactorization
import LectureNotes.GaussianBayesRisk
import LectureNotes.SamplingMoments

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- A normal mean or regression slope together with a strictly positive
variance. The variance-zero point masses are a different experiment. -/
abbrev NormalLocationScaleParameter := ℝ × {v : ℝ≥0 // 0 < v}

/-- Independent normal regression observations with fixed design and unknown
slope and variance, as in L5 Example 12. -/
def normalRegressionExperiment {n : ℕ} (x : Fin n → ℝ)
    (θ : NormalLocationScaleParameter) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => gaussianReal (θ.1 * x i) θ.2.val)

instance normalRegressionExperiment_probability {n : ℕ} (x : Fin n → ℝ)
    (θ : NormalLocationScaleParameter) : IsProbabilityMeasure (normalRegressionExperiment x θ) := by
  unfold normalRegressionExperiment
  infer_instance

/-- The independent-error formulation in the source has exactly this joint law. -/
theorem normalRegression_error_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (x : Fin n → ℝ)
    (θ : NormalLocationScaleParameter) {e : Fin n → Ω → ℝ}
    (he : ∀ i, HasLaw (e i) (gaussianReal 0 θ.2.val) P) (hind : iIndepFun e P) :
    HasLaw (fun ω i => θ.1 * x i + e i ω) (normalRegressionExperiment x θ) P := by
  apply (hind.comp (fun i z => θ.1 * x i + z) (fun _ => by fun_prop)).hasLaw_pi
  intro i
  convert! gaussianReal_add_const (he i) (θ.1 * x i) using 1 <;> simp [add_comm, Function.comp_def]

/-- Expansion of the actual joint density, retaining its normalizing constant. -/
theorem normal_regression_density_factorization {n : ℕ} (x y : Fin n → ℝ)
    (β : ℝ) (v : ℝ≥0) :
    (∏ i, gaussianPDF (β * x i) v (y i)) =
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹ ^ n * Real.exp
        (-((∑ i, y i ^ 2) - 2 * β * (∑ i, x i * y i) +
          β ^ 2 * (∑ i, x i ^ 2)) / (2 * v))) := by
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)]
  simp only [gaussianPDFReal]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 3
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  congr 2
  simp_rw [sub_sq, mul_pow]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The pair in L5 Example 12 is sufficient on the full continuous sample
space. No rank assumption on the fixed design is needed for sufficiency. -/
theorem normal_regression_pair_sufficient {n : ℕ} (x : Fin n → ℝ) :
    IsSufficientStatistic (normalRegressionExperiment x)
      (fun y : Fin n → ℝ => ((∑ i, y i ^ 2), (∑ i, x i * y i))) := by
  apply sufficient_of_sigmaFinite_reference_factorization volume (by fun_prop)
  intro θ
  refine ⟨fun t : ℝ × ℝ => ENNReal.ofReal
    ((Real.sqrt (2 * Real.pi * θ.2.val))⁻¹ ^ n * Real.exp
      (-(t.1 - 2 * θ.1 * t.2 + θ.1 ^ 2 * (∑ i, x i ^ 2)) / (2 * θ.2.val))),
    by fun_prop, ?_⟩
  rw [normalRegressionExperiment, normal_pi_withDensity _ _ θ.2.property.ne']
  apply withDensity_congr_ae
  exact ae_of_all _ (fun y => (normal_regression_density_factorization x y θ.1 θ.2.val).symm)

/-- The actual IID normal experiment when both mean and variance are unknown. -/
def normalJointExperiment (n : ℕ) (θ : NormalLocationScaleParameter) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal θ.1 θ.2.val)

instance normalJointExperiment_probability (n : ℕ) (θ : NormalLocationScaleParameter) :
    IsProbabilityMeasure (normalJointExperiment n θ) := by
  unfold normalJointExperiment
  infer_instance

/-- L5 Example 11's sufficient raw-moment pair, with the sum as first coordinate. -/
theorem normal_joint_density_factorization {n : ℕ} (y : Fin n → ℝ) (μ : ℝ) (v : ℝ≥0) :
    (∏ i, gaussianPDF μ v (y i)) = ENNReal.ofReal
      ((Real.sqrt (2 * Real.pi * v))⁻¹ ^ n * Real.exp
        (-((∑ i, y i ^ 2) - 2 * μ * (∑ i, y i) + n * μ ^ 2) / (2 * v))) := by
  simpa [mul_comm] using normal_regression_density_factorization (fun _ => 1) y μ v

theorem normal_joint_sum_squares_sufficient (n : ℕ) :
    IsSufficientStatistic (normalJointExperiment n)
      (fun y : Fin n → ℝ => ((∑ i, y i), (∑ i, y i ^ 2))) := by
  apply sufficient_of_sigmaFinite_reference_factorization volume (by fun_prop)
  intro θ
  refine ⟨fun t : ℝ × ℝ => ENNReal.ofReal
    ((Real.sqrt (2 * Real.pi * θ.2.val))⁻¹ ^ n * Real.exp
      (-(t.2 - 2 * θ.1 * t.1 + n * θ.1 ^ 2) / (2 * θ.2.val))), by fun_prop, ?_⟩
  rw [normalJointExperiment, normal_pi_withDensity _ _ θ.2.property.ne']
  apply withDensity_congr_ae
  exact ae_of_all _ (fun y => (normal_joint_density_factorization y θ.1 θ.2.val).symm)

/-- The raw moments can be recovered exactly from the sample mean and the
variance with denominator n−1. -/
theorem raw_moments_from_mean_variance {n : ℕ} (hn : 1 < n) (y : Fin n → ℝ) :
    ((∑ i, y i), (∑ i, y i ^ 2)) =
      (n * sampleMean y, (n - 1) * sampleVariance y + n * sampleMean y ^ 2) := by
  let : NeZero n := ⟨by omega⟩
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := (sub_pos.mpr hnR).ne'
  have hs := sum_centered_sq_sampleMean y
  simp only [Fintype.card_fin] at hs
  apply Prod.ext
  · simp only [sampleMean, Fintype.card_fin]
    field_simp
  · unfold sampleVariance
    rw [hs]
    field_simp [hn1]
    ring

/-- The same density expressed through the two usual sample statistics. -/
theorem normal_joint_mean_variance_factorization {n : ℕ} (hn : 1 < n)
    (y : Fin n → ℝ) (μ : ℝ) (v : ℝ≥0) :
    (∏ i, gaussianPDF μ v (y i)) = ENNReal.ofReal
      ((Real.sqrt (2 * Real.pi * v))⁻¹ ^ n * Real.exp
        (-((n - 1) * sampleVariance y + n * (sampleMean y - μ) ^ 2) / (2 * v))) := by
  rw [normal_joint_density_factorization]
  have he := raw_moments_from_mean_variance hn y
  have hsum := congrArg Prod.fst he
  have hsq := congrArg Prod.snd he
  change (∑ i, y i) = n * sampleMean y at hsum
  change (∑ i, y i ^ 2) = (n - 1) * sampleVariance y + n * sampleMean y ^ 2 at hsq
  rw [hsum, hsq]
  congr 3
  ring

/-- The sample mean and n−1 sample variance together are sufficient when both
normal parameters vary. This explicitly requires a nontrivial variance sample. -/
theorem normal_joint_mean_variance_sufficient {n : ℕ} (hn : 1 < n) :
    IsSufficientStatistic (normalJointExperiment n)
      (fun y : Fin n → ℝ => (sampleMean y, sampleVariance y)) := by
  apply sufficient_of_sigmaFinite_reference_factorization volume (by unfold sampleVariance sampleMean; fun_prop)
  intro θ
  refine ⟨fun t : ℝ × ℝ => ENNReal.ofReal
    ((Real.sqrt (2 * Real.pi * θ.2.val))⁻¹ ^ n * Real.exp
      (-((n - 1) * t.2 + n * (t.1 - θ.1) ^ 2) / (2 * θ.2.val))), by fun_prop, ?_⟩
  rw [normalJointExperiment, normal_pi_withDensity _ _ θ.2.property.ne']
  apply withDensity_congr_ae
  exact ae_of_all _ (fun y => (normal_joint_mean_variance_factorization hn y θ.1 θ.2.val).symm)

end LectureNotes
