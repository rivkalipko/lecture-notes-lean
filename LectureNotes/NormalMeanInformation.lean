import LectureNotes.NormalUnknownVarianceMLE
import LectureNotes.Information

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Log density as a function of the unknown mean, with known variance. -/
def normalMeanLogDensity (v x m : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (2 * Real.pi) - (1 / 2 : ℝ) * Real.log v - (x - m) ^ 2 / (2 * v)

def normalMeanScore (v m x : ℝ) : ℝ := (x - m) / v

theorem normalMeanLogDensity_actual (x m : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    Real.log (gaussianPDFReal m v x) = normalMeanLogDensity v x m := by
  have hh := normal_sample_log_density (fun _ : Fin 1 => x) m hv
  norm_num at hh
  dsimp [normalMeanLogDensity]
  linarith

/-- The actual mean score, differentiated from the log density. -/
theorem normalMeanLogDensity_derivative (x m : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (normalMeanLogDensity v x) (normalMeanScore v m x) m := by
  have hh := (hasDerivAt_const m (-(1 / 2 : ℝ) * Real.log (2 * Real.pi) -
    (1 / 2 : ℝ) * Real.log v)).sub
    ((((hasDerivAt_const m x).sub (hasDerivAt_id m)).pow 2).div_const (2 * v))
  convert! hh using 1
  simp only [normalMeanScore, Pi.sub_apply, id_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  field_simp
  <;> ring

theorem normalMeanScore_derivative (x m v : ℝ) :
    HasDerivAt (fun t => normalMeanScore v t x) (-1 / v) m := by
  simpa only [normalMeanScore, Pi.sub_apply, id_eq, zero_sub] using!
    ((hasDerivAt_const m x).sub (hasDerivAt_id m)).div_const v

theorem normalMeanScore_memLp_two (m : ℝ) (v : ℝ≥0) :
    MemLp (normalMeanScore v m) 2 (gaussianReal m v) := by
  simpa only [normalMeanScore, div_eq_mul_inv, Pi.sub_apply, id_eq] using!
    (((memLp_id_gaussianReal (μ := m) (v := v) 2).sub (memLp_const m)).mul_const (v : ℝ)⁻¹)

theorem normalMeanScore_mean (m : ℝ) (v : ℝ≥0) :
    (∫ x, normalMeanScore v m x ∂gaussianReal m v) = 0 := by
  unfold normalMeanScore
  have hi : Integrable (fun x : ℝ => x) (gaussianReal m v) :=
    (memLp_id_gaussianReal (μ := m) (v := v) 2).integrable (by norm_num)
  rw [integral_div, integral_sub hi (integrable_const m)]
  simp

/-- L6 Example 6 uses actual squared-score expectation, with positive known
variance so the model has the displayed Lebesgue density. -/
theorem normalMean_fisherInformation (m : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    FisherInformation (gaussianReal m v) (normalMeanScore v m) = 1 / (v : ℝ) := by
  have hmoment : (∫ x : ℝ, (x - m) ^ 2 ∂gaussianReal m v) = v := by
    have hh := variance_eq_integral (μ := gaussianReal m v) (X := id) (by fun_prop)
    simpa using hh.symm
  unfold FisherInformation normalMeanScore
  simp only [div_pow]
  rw [integral_div, hmoment]
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  field_simp

/-- The second information identity holds in this regular location model. -/
theorem normalMean_information_identity (m : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    FisherInformation (gaussianReal m v) (normalMeanScore v m) =
      -(∫ _x : ℝ, (-1 / (v : ℝ)) ∂gaussianReal m v) := by
  rw [normalMean_fisherInformation m hv]
  simp [div_eq_mul_inv]

end LectureNotes
