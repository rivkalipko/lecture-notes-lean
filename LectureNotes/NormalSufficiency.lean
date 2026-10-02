import LectureNotes.MinimalSufficiency
import LectureNotes.GaussianBayesRisk
import LectureNotes.NormalUMPNonexistence

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The actual experiment of independent normal observations with common mean
and known variance, on the full continuous sample space. -/
def normalLocationExperiment (n : ℕ) (v : ℝ≥0) (μ : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal μ v)

instance normalLocationExperiment_probability (n : ℕ) (v : ℝ≥0) (μ : ℝ) :
    IsProbabilityMeasure (normalLocationExperiment n v μ) := by
  unfold normalLocationExperiment
  infer_instance

/-- The full sample density relative to the zero-mean model depends on the
sample only through its sum. -/
theorem normal_location_density_factorization {n : ℕ} {v : ℝ≥0} (hv : 0 < v)
    (μ : ℝ) (x : Fin n → ℝ) :
    (∏ i, gaussianPDF μ v (x i)) = (∏ i, gaussianPDF 0 v (x i)) *
      ENNReal.ofReal (Real.exp ((μ * (∑ i, x i) - n * μ ^ 2 / 2) / v)) := by
  have hi (i : Fin n) : gaussianPDFReal μ v (x i) = gaussianPDFReal 0 v (x i) *
      Real.exp ((μ * x i - μ ^ 2 / 2) / v) := by
    have h := (div_eq_iff (gaussianPDFReal_pos 0 v (x i) hv.ne').ne').mp
      (gaussian_density_ratio hv 0 μ (x i))
    rw [h, mul_comm]
    congr 2 <;> ring
  have he : (∏ i, gaussianPDFReal μ v (x i)) = (∏ i, gaussianPDFReal 0 v (x i)) *
      Real.exp ((μ * (∑ i, x i) - n * μ ^ 2 / 2) / v) := by
    simp_rw [hi]
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    congr 2
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
    <;> ring
  simp only [gaussianPDF, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)), he]

/-- The sample mean is sufficient in the continuous normal experiment with
known positive variance. This conclusion uses a common regular conditional
kernel, not a putative Lebesgue density on a hyperplane. -/
theorem normal_sampleMean_sufficient {n : ℕ} (hn : 0 < n) {v : ℝ≥0} (hv : 0 < v) :
    IsSufficientStatistic (normalLocationExperiment n v) (sampleMean : (Fin n → ℝ) → ℝ) := by
  apply sufficient_of_density_factorization (P := normalLocationExperiment n v)
    volume (0 : ℝ) (fun μ x => ∏ i, gaussianPDF μ v (x i)) (by intro μ; fun_prop)
    (fun μ => (normal_pi_withDensity (fun _ => μ) v hv.ne').symm) (by
      unfold sampleMean; fun_prop)
    (fun μ t => ENNReal.ofReal (Real.exp ((μ * (n * t) - n * μ ^ 2 / 2) / v)))
    (by intro μ; fun_prop)
  intro μ
  apply ae_of_all
  intro x
  have hm : (n : ℝ) * sampleMean x = ∑ i, x i := by
    simp only [sampleMean, Fintype.card_fin]
    field_simp
  dsimp only
  rw [hm]
  exact normal_location_density_factorization hv μ x

/-- An explicit density of every model relative to the zero-mean model. -/
theorem normal_location_reference_density {n : ℕ} {v : ℝ≥0} (hv : 0 < v) (μ : ℝ) :
    (normalLocationExperiment n v 0).withDensity
      (fun x => ENNReal.ofReal (Real.exp ((μ * (∑ i, x i) - n * μ ^ 2 / 2) / v))) =
      normalLocationExperiment n v μ := by
  unfold normalLocationExperiment
  rw [normal_pi_withDensity (fun _ => 0) v hv.ne',
    ← withDensity_mul _ (by fun_prop) (by fun_prop), normal_pi_withDensity (fun _ => μ) v hv.ne']
  apply withDensity_congr_ae
  exact ae_of_all _ (fun x => (normal_location_density_factorization hv μ x).symm)

/-- One nonzero mean contrast recovers the sample mean from its likelihood
ratio, so no sufficient statistic can lose the sample mean. -/
theorem normal_sampleMean_minimal_sufficient {n : ℕ} (hn : 0 < n) {v : ℝ≥0} (hv : 0 < v) :
    IsMinimalSufficientStatistic (normalLocationExperiment n v)
      (sampleMean : (Fin n → ℝ) → ℝ) := by
  have hdom (μ : ℝ) : normalLocationExperiment n v μ ≪ normalLocationExperiment n v 0 := by
    rw [← normal_location_reference_density hv μ]
    exact withDensity_absolutelyContinuous _ _
  let decode (r : Fin 1 → ℝ≥0∞) := ((v : ℝ) * Real.log (r 0).toReal + n / 2) / n
  apply minimal_sufficient_of_likelihood_ratio_recovery
    (normalLocationExperiment n v) (normal_sampleMean_sufficient hn hv) 0 hdom
    (fun _ : Fin 1 => (1 : ℝ)) decode (by dsimp only [decode]; fun_prop)
  have hr : (normalLocationExperiment n v 1).rnDeriv (normalLocationExperiment n v 0) =ᵐ[
      normalLocationExperiment n v 0]
      (fun x => ENNReal.ofReal (Real.exp (((∑ i, x i) - n / 2) / v))) := by
    have h := Measure.rnDeriv_withDensity (normalLocationExperiment n v 0)
      (show Measurable (fun x : Fin n → ℝ =>
        ENNReal.ofReal (Real.exp ((1 * (∑ i, x i) - n * (1 : ℝ) ^ 2 / 2) / v))) by fun_prop)
    rw [normal_location_reference_density hv 1] at h
    simpa only [one_mul, one_pow, mul_one] using h
  filter_upwards [hr] with x hx
  dsimp only [decode]
  rw [hx, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]
  simp only [sampleMean, Fintype.card_fin]
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  field_simp
  <;> ring

end LectureNotes
