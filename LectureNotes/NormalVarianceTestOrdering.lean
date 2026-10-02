import LectureNotes.NormalUnknownVarianceMLE
import LectureNotes.LikelihoodRatio
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The log density of a zero-mean normal observation with variance v>0. -/
def normalVarianceLogDensity (x v : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (2 * Real.pi) - (1 / 2 : ℝ) * Real.log v - x ^ 2 / (2 * v)

def normalVarianceScore (x v : ℝ) : ℝ := -1 / (2 * v) + x ^ 2 / (2 * v ^ 2)

def normalVarianceInformation (v : ℝ) : ℝ := 1 / (2 * v ^ 2)

theorem normalVarianceLogDensity_actual (x : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    Real.log (gaussianPDFReal 0 v x) = normalVarianceLogDensity x v := by
  have h := normal_sample_log_density (fun _ : Fin 1 => x) 0 hv
  norm_num at h
  dsimp [normalVarianceLogDensity]
  linarith

theorem normalVarianceLogDensity_derivative (x : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (normalVarianceLogDensity x) (normalVarianceScore x v) v := by
  have h := ((hasDerivAt_const v (-(1 / 2 : ℝ) * Real.log (2 * Real.pi))).sub
    (((hasDerivAt_id v).log hv.ne').const_mul (1 / 2))).sub
    ((hasDerivAt_const v (x ^ 2)).div ((hasDerivAt_id v).const_mul 2) (by positivity))
  convert! h using 1
  dsimp [normalVarianceScore]
  field_simp
  <;> ring

theorem normalVarianceScore_derivative (x : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (normalVarianceScore x) (1 / (2 * v ^ 2) - x ^ 2 / v ^ 3) v := by
  have h := ((hasDerivAt_const v (-1 : ℝ)).div
    ((hasDerivAt_id v).const_mul 2) (by positivity)).add
    ((hasDerivAt_const v (x ^ 2)).div (((hasDerivAt_id v).pow 2).const_mul 2) (by simpa using (show 2 * v ^ 2 ≠ 0 by positivity)))
  convert! h using 1
  simp only [id_eq, Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one]
  field_simp
  <;> ring

/-- The information used in the example is the actual expected negative
log-likelihood curvature, under the normalized Gaussian model. -/
theorem normalVariance_expected_information {v : ℝ≥0} (hv : 0 < v) :
    -(∫ x : ℝ, (1 / (2 * (v : ℝ) ^ 2) - x ^ 2 / (v : ℝ) ^ 3) ∂gaussianReal 0 v) =
      normalVarianceInformation v := by
  have hm : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = v := by
    have h := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := v) 2)
    simpa using h.symm
  rw [integral_sub (integrable_const _)
    (((normal_square_memLp 0 v).integrable (by norm_num)).div_const _),
    integral_const, integral_div, hm]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  dsimp [normalVarianceInformation]
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  field_simp
  <;> ring

/-- With a known zero mean the actual positive-variance density is globally
maximized at x² whenever the observed value is nonzero. -/
theorem normalVariance_density_maximum {x : ℝ} (hx : x ≠ 0)
    {v : ℝ≥0} (hv : 0 < v) :
    gaussianPDFReal 0 v x ≤ gaussianPDFReal 0 ⟨x ^ 2, sq_nonneg x⟩ x := by
  have ha : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have haN : (0 : ℝ≥0) < ⟨x ^ 2, sq_nonneg x⟩ := ha
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  apply (Real.log_le_log_iff (gaussianPDFReal_pos _ _ _ hv.ne')
    (gaussianPDFReal_pos _ _ _ haN.ne')).mp
  rw [normalVarianceLogDensity_actual x hv, normalVarianceLogDensity_actual x haN]
  have h := neymanScott_profile_maximum (n := 1) (by norm_num) ha hvR
  norm_num only [Nat.cast_one, one_mul] at h
  dsimp [normalVarianceLogDensity]
  change -(1 / 2 : ℝ) * Real.log (2 * Real.pi) - (1 / 2 : ℝ) * Real.log v - x ^ 2 / (2 * v) ≤
    -(1 / 2 : ℝ) * Real.log (2 * Real.pi) - (1 / 2 : ℝ) * Real.log (x ^ 2) - x ^ 2 / (2 * x ^ 2)
  have he : x ^ 2 / (2 * x ^ 2) = (1 : ℝ) / 2 := by field_simp
  rw [he, show x ^ 2 / (2 * (v : ℝ)) = (x ^ 2 / (v : ℝ)) / 2 by ring]
  linarith

/-- The LR value is computed from actual positive Gaussian density values. -/
theorem normalVariance_example_lr :
    -2 * Real.log (gaussianPDFReal 0 1 (Real.sqrt 2) /
      gaussianPDFReal 0 2 (Real.sqrt 2)) = 1 - Real.log 2 := by
  rw [minus_two_log_ratio _ _ (gaussianPDFReal_pos _ _ _ (by norm_num))
    (gaussianPDFReal_pos _ _ _ (by norm_num)),
    normalVarianceLogDensity_actual _ (by norm_num),
    normalVarianceLogDensity_actual _ (by norm_num)]
  norm_num [normalVarianceLogDensity, Real.sq_sqrt]
  ring

/-- A genuine normal variance test contradicts a blanket finite-sample
LM≤LR≤W ordering: here the ordering is strictly reversed. -/
theorem normalVariance_example_reverse_order :
    scalarWald 1 2 1 (1 / normalVarianceInformation 2) <
      -2 * Real.log (gaussianPDFReal 0 1 (Real.sqrt 2) / gaussianPDFReal 0 2 (Real.sqrt 2)) ∧
    -2 * Real.log (gaussianPDFReal 0 1 (Real.sqrt 2) / gaussianPDFReal 0 2 (Real.sqrt 2)) <
      scalarScoreStatistic (normalVarianceScore (Real.sqrt 2) 1) (normalVarianceInformation 1) := by
  rw [normalVariance_example_lr]
  norm_num [scalarWald, scalarScoreStatistic, normalVarianceInformation,
    normalVarianceScore, Real.sq_sqrt]
  have hl := Real.sum_range_le_log_div (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 1
  have hu := Real.log_div_le_sum_range_add (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

end LectureNotes
