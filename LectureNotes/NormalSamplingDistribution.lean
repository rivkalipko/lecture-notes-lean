import LectureNotes.NormalSampling
import LectureNotes.GaussianQuadraticForms

/-! L2 Theorem 1: the chi-square and Student-t sampling laws. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace

/-- The residual subspace consists of vectors orthogonal to the all-ones vector. -/
def residualSpace (n : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  (ℝ ∙ (WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))))ᗮ

theorem residualSpace_finrank {n : ℕ} (hn : 0 < n) :
    Module.finrank ℝ (residualSpace n) = n - 1 := by
  have hne : WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ)) ≠ 0 := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x ⟨0, hn⟩) h
    simp at this
  have h := (ℝ ∙ (WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ)))).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hne, finrank_euclideanSpace] at h
  change Module.finrank ℝ (ℝ ∙ (WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))))ᗮ = _
  simpa using Nat.eq_sub_of_add_eq (by simpa [add_comm] using h)

/-- The familiar centering matrix is the orthogonal projection onto residuals. -/
theorem residualSpace_projection {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (residualSpace n).starProjection x i = x i - sampleMean (fun j => x j) := by
  rw [residualSpace, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_singleton]
  simp [PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq, sampleMean, div_eq_mul_inv, mul_comm]

/-- Standardizing a nondegenerate normal variable gives a standard normal. -/
theorem normal_standardize {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hv : 0 < v)
    (hX : HasLaw X (gaussianReal μ v) P) :
    HasLaw (fun ω => (X ω - μ) / Real.sqrt v) (gaussianReal 0 1) P := by
  have hs : Real.sqrt (v : ℝ) ^ 2 = v := Real.sq_sqrt v.coe_nonneg
  have he : v / NNReal.mk (Real.sqrt (v : ℝ) ^ 2) (sq_nonneg _) = 1 := by
    apply NNReal.coe_injective
    change (v : ℝ) / Real.sqrt (v : ℝ) ^ 2 = 1
    rw [hs, div_self (by exact_mod_cast hv.ne')]
  simpa only [sub_self, zero_div, he] using!
    gaussianReal_div_const (gaussianReal_sub_const hX μ) (Real.sqrt v)

theorem sampleMean_sub_div {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (μ s : ℝ) :
    sampleMean (fun i => (x i - μ) / s) = (sampleMean x - μ) / s := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [sampleMean, Fintype.card_fin]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
  rw [← mul_div_assoc, mul_sub, inv_mul_cancel_left₀ hn']

theorem standard_normal_residual_sum_squares {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} (hn : 0 < n) {Z : Fin n → Ω → ℝ}
    (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P) (hind : iIndepFun Z P) :
    HasLaw (fun ω => ∑ i, (Z i ω - sampleMean (fun j => Z j ω)) ^ 2)
      (chiSquared (n - 1)) P := by
  have hvec : HasLaw (fun ω => WithLp.toLp 2 (fun i => Z i ω))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) P :=
    (show HasLaw (WithLp.toLp 2) (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (Measure.pi fun _ => gaussianReal 0 1) from
        ⟨(WithLp.measurable_toLp _ _).aemeasurable, map_pi_eq_stdGaussian⟩).comp
          (hind.hasLaw_pi hZ)
  have h := (stdGaussian_norm_sq (E := residualSpace n)).comp
    ((stdGaussian_orthogonalProjection (residualSpace n)).comp hvec)
  rw [residualSpace_finrank hn] at h
  convert h using 1
  funext ω
  change _ = ‖(residualSpace n).orthogonalProjectionOnto (WithLp.toLp 2 (fun i => Z i ω))‖ ^ 2
  rw [Submodule.coe_norm, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [Submodule.coe_orthogonalProjectionOnto_apply, residualSpace_projection]

/-- L2 Theorem 1(2), with positive population variance and at least two observations. -/
theorem normal_sampleVariance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (hn : 1 < n) {X : Fin n → Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hv : 0 < v) (hX : ∀ i, HasLaw (X i) (gaussianReal μ v) P)
    (hind : iIndepFun X P) :
    HasLaw (fun ω => ((n : ℝ) - 1) * sampleVariance (fun i => X i ω) / v)
      (chiSquared (n - 1)) P := by
  let Z (i : Fin n) (ω) := (X i ω - μ) / Real.sqrt v
  have hZ (i) : HasLaw (Z i) (gaussianReal 0 1) P := normal_standardize hv (hX i)
  have hi : iIndepFun Z P := hind.comp (fun _ x => (x - μ) / Real.sqrt v) (by fun_prop)
  have h := standard_normal_residual_sum_squares (by omega : 0 < n) hZ hi
  have hn' : (n : ℝ) - 1 ≠ 0 := by exact_mod_cast (show (n : ℤ) - 1 ≠ 0 by omega)
  have hs : Real.sqrt (v : ℝ) ^ 2 = v := Real.sq_sqrt v.coe_nonneg
  convert h using 1
  funext ω
  simp only [Z, sampleMean_sub_div (by omega : 0 < n)]
  have hr (i : Fin n) :
      ((X i ω - μ) / Real.sqrt v - (sampleMean (fun j => X j ω) - μ) / Real.sqrt v) ^ 2 =
      (X i ω - sampleMean (fun j => X j ω)) ^ 2 / v := by
    rw [← sub_div, sub_sub_sub_cancel_right, div_pow, hs]
  simp_rw [hr]
  rw [← Finset.sum_div]
  simp only [sampleVariance]
  rw [mul_div_cancel₀ _ hn']

/-- Thus the denominator in the t statistic is nonzero almost surely. -/
theorem normal_sampleVariance_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (hn : 1 < n) {X : Fin n → Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hv : 0 < v) (hX : ∀ i, HasLaw (X i) (gaussianReal μ v) P)
    (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P, 0 < sampleVariance (fun i => X i ω) := by
  have hQ := normal_sampleVariance hn hv hX hind
  have hp := (hQ.ae_iff (show Measurable (fun x : ℝ => 0 < x) by measurability)).mpr
    (chiSquared_ae_pos (by omega : 0 < n - 1))
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  filter_upwards [hp] with ω hω
  exact (mul_pos_iff_of_pos_left (sub_pos.mpr hnR)).mp ((div_pos_iff_of_pos_right hvR).mp hω)

/-- L2 Theorem 1(4): the Studentized sample mean has `n - 1` degrees of freedom. -/
theorem normal_studentized_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 1 < n) {X : Fin n → Ω → ℝ}
    {μ : ℝ} {v : ℝ≥0} (hv : 0 < v)
    (hX : ∀ i, HasLaw (X i) (gaussianReal μ v) P) (hind : iIndepFun X P) :
    HasLaw (fun ω => (sampleMean (fun i => X i ω) - μ) /
      Real.sqrt (sampleVariance (fun i => X i ω) / n)) (studentT (n - 1)) P := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hW : HasLaw (fun ω => (sampleMean (fun i => X i ω) - μ) / Real.sqrt ((v : ℝ) / n))
      (gaussianReal 0 1) P := by
    have hvn : (0 : ℝ≥0) < v / n := div_pos hv (by exact_mod_cast hn0)
    simpa using! normal_standardize hvn (normal_sampleMean hn0 hX hind)
  have hY := normal_sampleVariance hn hv hX hind
  have hi := (normal_sampleMean_independent_sampleVariance hn0 hX hind).comp
    (show Measurable (fun m : ℝ => (m - μ) / Real.sqrt ((v : ℝ) / n)) by fun_prop)
    (show Measurable (fun s : ℝ => ((n : ℝ) - 1) * s / v) by fun_prop)
  have ht := studentT_ratio (by omega : 0 < n - 1) hW hY hi
  convert ht using 1
  funext ω
  rw [div_div, ← Real.sqrt_mul (le_of_lt (div_pos hvR hnR))]
  congr 2
  rw [hcast]
  field_simp [hn1, hvR.ne', hnR.ne']

end LectureNotes
