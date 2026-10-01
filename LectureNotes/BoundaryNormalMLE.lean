import LectureNotes.IIDScoreAsymptotics
import LectureNotes.NormalTestPower

set_option autoImplicit false

/-! L7's boundary example: the normal mean restricted to `[0,∞)`.
The maximum is proved for the actual sample density. At the boundary its
normalized limit is the positive part of a normal variable and has an atom. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

def nonnegativeNormalMLE {n : ℕ} (x : Fin n → ℝ) : ℝ := max 0 (sampleMean x)

theorem sum_squared_error_decomposition {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (t : ℝ) :
    (∑ i, (x i - t) ^ 2) = (∑ i, (x i - sampleMean x) ^ 2) +
      n * (t - sampleMean x) ^ 2 := by
  have hm : (∑ i, x i) = (n : ℝ) * sampleMean x := by
    simpa using (sampleMean_eq_iff x _
      (by simpa using (Nat.cast_ne_zero.mpr hn.ne' : (n : ℝ) ≠ 0))).mp rfl
  have hc : (∑ i, (x i - sampleMean x)) = 0 := by
    simp [Finset.sum_sub_distrib, hm]
  calc
    (∑ i, (x i - t) ^ 2) = ∑ i, ((x i - sampleMean x) ^ 2 +
        (t - sampleMean x) ^ 2 - 2 * (t - sampleMean x) * (x i - sampleMean x)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hc]
      simp

theorem nonnegativeNormalMLE_least_squares {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ i, (x i - nonnegativeNormalMLE x) ^ 2) ≤ ∑ i, (x i - t) ^ 2 := by
  rw [sum_squared_error_decomposition hn x (nonnegativeNormalMLE x),
    sum_squared_error_decomposition hn x t]
  refine add_le_add (le_refl _) (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))
  unfold nonnegativeNormalMLE
  by_cases hm : 0 ≤ sampleMean x
  · rw [max_eq_right hm, sub_self]
    simpa only [zero_pow (by decide : 2 ≠ 0)] using sq_nonneg (t - sampleMean x)
  · rw [max_eq_left (le_of_not_ge hm)]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ht (le_of_not_ge hm), sq_nonneg t]

theorem normal_unit_sample_log_density {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    Real.log (∏ i, gaussianPDFReal t 1 (x i)) =
      n * Real.log (Real.sqrt (2 * Real.pi))⁻¹ - (∑ i, (x i - t) ^ 2) / 2 := by
  rw [Real.log_prod (fun i _ => (gaussianPDFReal_pos t 1 (x i) (by norm_num)).ne')]
  have hc : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 := by positivity
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, Real.log_mul hc (Real.exp_ne_zero _),
    Real.log_exp, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, Finset.sum_neg_distrib]
  ring

/-- This is a global maximum over the constrained parameter space. -/
theorem nonnegativeNormalMLE_maximizes_density {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    (∏ i, gaussianPDFReal t 1 (x i)) ≤ ∏ i, gaussianPDFReal (nonnegativeNormalMLE x) 1 (x i) := by
  apply (Real.log_le_log_iff
    (Finset.prod_pos (fun i _ => gaussianPDFReal_pos t 1 (x i) (by norm_num)))
    (Finset.prod_pos (fun i _ => gaussianPDFReal_pos _ 1 (x i) (by norm_num)))).mp
  rw [normal_unit_sample_log_density x t, normal_unit_sample_log_density x (nonnegativeNormalMLE x)]
  linarith [nonnegativeNormalMLE_least_squares hn x ht]

def positiveNormalLaw (v : ℝ≥0) : Measure ℝ := (gaussianReal 0 v).map (fun z => max 0 z)

theorem positiveNormalLaw_isProbabilityMeasure (v : ℝ≥0) : IsProbabilityMeasure (positiveNormalLaw v) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- The point mass at zero equals the entire negative normal tail. -/
theorem positiveNormalLaw_atom (v : ℝ≥0) :
    (positiveNormalLaw v).real {0} = cdf (gaussianReal 0 v) 0 := by
  rw [positiveNormalLaw, map_measureReal_apply (by fun_prop) (measurableSet_singleton _), cdf_eq_real]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Iic]
  exact max_eq_left_iff

theorem positiveNormalLaw_atom_pos {v : ℝ≥0} (hv : 0 < v) :
    0 < (positiveNormalLaw v).real {0} := by
  rw [positiveNormalLaw_atom]
  exact (show 0 ≤ cdf (gaussianReal 0 v) (-1) by rw [cdf_eq_real]; positivity).trans_lt
    (gaussian_cdf_strictMono 0 v hv (by norm_num : (-1 : ℝ) < 0))

theorem positiveNormalLaw_not_nondegenerate_gaussian {v w : ℝ≥0}
    (hv : 0 < v) (hw : 0 < w) (m : ℝ) : positiveNormalLaw v ≠ gaussianReal m w := by
  intro he
  have h := positiveNormalLaw_atom_pos hv
  have : NullSingletonClass (gaussianReal m w) := nullSingletonClass_gaussianReal hw.ne'
  rw [he, measureReal_def, measure_singleton, ENNReal.toReal_zero] at h
  exact (lt_irrefl 0) h

theorem boundary_normal_mle_limit {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P)
    (hind : iIndepFun X P) {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) Q) :
    ConvergesInDistribution P Q
      (fun n ω => Real.sqrt n * nonnegativeNormalMLE (fun i : Fin n => X i ω))
      (fun ω => max 0 (Z ω)) ∧ HasLaw (fun ω => max 0 (Z ω)) (positiveNormalLaw 1) Q := by
  have hmean : (∫ ω, X 0 ω ∂P) = 0 := by simpa using (hX 0).integral_eq
  have hvar : Var[X 0; P] = (1 : ℝ≥0) := by simpa using (hX 0).variance_eq
  have h := iid_zero_mean_score_clt X id measurable_id hind
    (fun i => (hX i).identDistrib (hX 0)) (hX 0).hasGaussianLaw.memLp_two hmean hvar hZ
  have hc := continuous_mapping_distribution (g := fun z => max 0 z) (by fun_prop) h
  refine ⟨?_, HasLaw.comp ⟨by fun_prop, rfl⟩ hZ⟩
  convert! hc using 1
  funext n ω
  simp only [nonnegativeNormalMLE, sampleMean, Fintype.card_fin,
    mul_max_of_nonneg _ _ (Real.sqrt_nonneg (n : ℝ)), mul_zero]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun i => id (X i ω))]
  simp only [id_eq, div_eq_mul_inv]
  ring

end LectureNotes
