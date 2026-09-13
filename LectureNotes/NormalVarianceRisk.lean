import LectureNotes.NormalSamplingDistribution
import LectureNotes.ChiSquaredMoments
import LectureNotes.Estimation

/-! L5 Example 5: exact risks of the two normal variance estimators. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The centered empirical second moment uses denominator `n`. -/
def empiricalVariance {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, (x i - sampleMean x) ^ 2) / n

theorem empiricalVariance_eq_scaled_sampleVariance {n : ℕ} (hn : 1 < n)
    (x : Fin n → ℝ) :
    empiricalVariance x = ((n : ℝ) - 1) / n * sampleVariance x := by
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  simp only [empiricalVariance, sampleVariance]
  field_simp

section Normal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n : ℕ} (hn : 1 < n) {X : Fin n → Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
  (hv : 0 < v) (hX : ∀ i, HasLaw (X i) (gaussianReal μ v) P) (hind : iIndepFun X P)
include hn hv hX hind

theorem normal_sampleVariance_memLp :
    MemLp (fun ω => sampleVariance (fun i => X i ω)) 2 P := by
  have hQ := normal_sampleVariance hn hv hX hind
  have hLp := (hQ.identDistrib HasLaw.id).memLp_iff.mpr (chiSquared_memLp (n - 1))
  have hrec := hLp.const_mul ((v : ℝ) / ((n : ℝ) - 1))
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  convert! hrec using 1
  funext ω
  field_simp

omit hv in
theorem normal_sampleVariance_mean : P[fun ω => sampleVariance (fun i => X i ω)] = (v : ℝ) :=
  sampleVariance_unbiased (μ := μ) (σ2 := (v : ℝ)) hn (fun i => (hX i).hasGaussianLaw.memLp_two)
    (fun _ _ hij => hind.indepFun hij)
    (fun i => (hX i).integral_eq.trans (by simp))
    (fun i => (hX i).variance_eq.trans (by simp))

theorem normal_sampleVariance_variance :
    Var[fun ω => sampleVariance (fun i => X i ω); P] = 2 * (v : ℝ) ^ 2 / ((n : ℝ) - 1) := by
  have hQ := normal_sampleVariance hn hv hX hind
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have he : (fun ω => (v : ℝ) / ((n : ℝ) - 1) *
      (((n : ℝ) - 1) * sampleVariance (fun i => X i ω) / v)) =
      (fun ω => sampleVariance (fun i => X i ω)) := by
    funext ω
    field_simp
  rw [← he, variance_const_mul, hQ.variance_eq, chiSquared_variance,
    Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  field_simp

theorem normal_sampleVariance_mse :
    mse P (fun ω => sampleVariance (fun i => X i ω)) v =
      2 * (v : ℝ) ^ 2 / ((n : ℝ) - 1) := by
  rw [mse_eq_variance_add_bias_sq P (normal_sampleVariance_memLp hn hv hX hind),
    normal_sampleVariance_variance hn hv hX hind]
  simp [bias, normal_sampleVariance_mean hn hX hind]

theorem normal_empiricalVariance_bias :
    bias P (fun ω => empiricalVariance (fun i => X i ω)) v = -(v : ℝ) / n := by
  simp only [bias, empiricalVariance_eq_scaled_sampleVariance hn]
  rw [integral_const_mul, normal_sampleVariance_mean hn hX hind]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp
  ring

theorem normal_empiricalVariance_mse :
    mse P (fun ω => empiricalVariance (fun i => X i ω)) v =
      (2 * (n : ℝ) - 1) * (v : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
  have hS := normal_sampleVariance_memLp hn hv hX hind
  have hV := normal_sampleVariance_variance hn hv hX hind
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hE : MemLp (fun ω => empiricalVariance (fun i => X i ω)) 2 P := by
    simpa only [empiricalVariance_eq_scaled_sampleVariance hn] using
      hS.const_mul (((n : ℝ) - 1) / n)
  rw [mse_eq_variance_add_bias_sq P hE, normal_empiricalVariance_bias hn hv hX hind]
  simp only [empiricalVariance_eq_scaled_sampleVariance hn]
  rw [variance_const_mul, hV]
  field_simp
  ring

theorem normal_empiricalVariance_variance :
    Var[fun ω => empiricalVariance (fun i => X i ω); P] =
      2 * (v : ℝ) ^ 2 * ((n : ℝ) - 1) / (n : ℝ) ^ 2 := by
  simp only [empiricalVariance_eq_scaled_sampleVariance hn]
  rw [variance_const_mul, normal_sampleVariance_variance hn hv hX hind]
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  field_simp

/-- The biased estimator has strictly smaller MSE at every positive variance. -/
theorem normal_empiricalVariance_strictly_improves_mse :
    mse P (fun ω => empiricalVariance (fun i => X i ω)) v <
      mse P (fun ω => sampleVariance (fun i => X i ω)) v := by
  rw [normal_empiricalVariance_mse hn hv hX hind, normal_sampleVariance_mse hn hv hX hind]
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  rw [div_lt_div_iff₀ (sq_pos_of_pos (by linarith : (0 : ℝ) < n)) (by linarith)]
  nlinarith [mul_pos (sq_pos_of_pos hvR) (show (0 : ℝ) < 3 * n - 1 by linarith)]

end Normal
end LectureNotes
