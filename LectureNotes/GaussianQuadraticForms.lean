import LectureNotes.Foundations

/-! L1: chi-square, Student-t, F distributions, and Gaussian projections. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace

/-- The law of the sum of squares of `n` independent standard normals. -/
def chiSquared (n : ℕ) : Measure ℝ :=
  (Measure.pi fun _ : Fin n => gaussianReal 0 1).map (fun z => ∑ i, z i ^ 2)

instance (n : ℕ) : IsProbabilityMeasure (chiSquared n) :=
  Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

/-- Positive degrees of freedom give a strictly positive value almost surely. -/
theorem chiSquared_ae_pos {n : ℕ} (hn : 0 < n) : ∀ᵐ x ∂chiSquared n, 0 < x := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  let i : Fin n := ⟨0, hn⟩
  have hne : ∀ᵐ z : Fin n → ℝ ∂Measure.pi (fun _ => gaussianReal 0 1), z i ≠ 0 :=
    (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).quasiMeasurePreserving.ae
      ((gaussianReal 0 1).ae_ne 0)
  rw [chiSquared]
  apply (ae_map_iff (Measurable.aemeasurable (by fun_prop)) (by measurability)).mpr
  filter_upwards [hne] with z hz
  exact (sq_pos_of_ne_zero hz).trans_le
    (Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i))

/-- The normal/independent-chi-square construction of the t distribution.
The statistical interpretation requires a positive number of degrees of freedom. -/
def studentT (n : ℕ) : Measure ℝ :=
  ((gaussianReal 0 1).prod (chiSquared n)).map
    (fun zy => zy.1 / Real.sqrt (zy.2 / n))

instance (n : ℕ) : IsProbabilityMeasure (studentT n) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- The ratio of two independently scaled chi-square variables.
The statistical F distribution requires both degrees of freedom to be positive. -/
def fDistribution (k l : ℕ) : Measure ℝ :=
  ((chiSquared k).prod (chiSquared l)).map (fun xy => (xy.1 / k) / (xy.2 / l))

instance (k l : ℕ) : IsProbabilityMeasure (fDistribution k l) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

theorem chiSquared_sum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {Z : Fin n → Ω → ℝ}
    (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P) (hind : iIndepFun Z P) :
    HasLaw (fun ω => ∑ i, Z i ω ^ 2) (chiSquared n) P :=
  (show HasLaw (fun z : Fin n → ℝ => ∑ i, z i ^ 2) (chiSquared n)
    (Measure.pi fun _ => gaussianReal 0 1) from
      ⟨Measurable.aemeasurable (by fun_prop), rfl⟩).comp
      (hind.hasLaw_pi hZ)

theorem studentT_ratio {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (_hn : 0 < n) {Z Y : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P) (hY : HasLaw Y (chiSquared n) P)
    (hind : IndepFun Z Y P) :
    HasLaw (fun ω => Z ω / Real.sqrt (Y ω / n)) (studentT n) P :=
  (show HasLaw (fun zy : ℝ × ℝ => zy.1 / Real.sqrt (zy.2 / n)) (studentT n)
    ((gaussianReal 0 1).prod (chiSquared n)) from ⟨by fun_prop, rfl⟩).comp
      (hind.hasLaw_prod hZ hY)

theorem fDistribution_ratio {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {k l : ℕ} (_hk : 0 < k) (_hl : 0 < l) {X Y : Ω → ℝ}
    (hX : HasLaw X (chiSquared k) P) (hY : HasLaw Y (chiSquared l) P)
    (hind : IndepFun X Y P) :
    HasLaw (fun ω => (X ω / k) / (Y ω / l)) (fDistribution k l) P :=
  (show HasLaw (fun xy : ℝ × ℝ => (xy.1 / k) / (xy.2 / l)) (fDistribution k l)
    ((chiSquared k).prod (chiSquared l)) from ⟨by fun_prop, rfl⟩).comp
      (hind.hasLaw_prod hX hY)

section Euclidean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The squared norm of a standard Gaussian has degrees of freedom equal to
the dimension; this also covers the zero-dimensional case. -/
theorem stdGaussian_norm_sq :
    HasLaw (fun x : E => ‖x‖ ^ 2) (chiSquared (Module.finrank ℝ E)) (stdGaussian E) := by
  let b := stdOrthonormalBasis ℝ E
  have hrepr : HasLaw b.repr (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
      (stdGaussian E) := ⟨by fun_prop, stdGaussian_map b.repr⟩
  have hnorm : HasLaw (fun x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => ‖x‖ ^ 2)
      (chiSquared (Module.finrank ℝ E))
      (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    refine ⟨by fun_prop, ?_⟩
    rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    simp [EuclideanSpace.real_norm_sq_eq]
  simpa [Function.comp_def] using hnorm.comp hrepr

/-- Orthogonal projection of a standard Gaussian is standard Gaussian on the
subspace. The covariance calculation uses that the adjoint is the inclusion. -/
theorem stdGaussian_orthogonalProjection (K : Submodule ℝ E) :
    HasLaw K.orthogonalProjectionOnto (stdGaussian K) (stdGaussian E) := by
  refine ⟨by fun_prop, IsGaussian.ext ?_ ?_⟩
  · change (∫ x, x ∂((stdGaussian E).map K.orthogonalProjectionOnto)) = _
    rw [K.orthogonalProjectionOnto.integral_id_map IsGaussian.integrable_id]
    simp
  · ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      K.adjoint_orthogonalProjectionOnto, covarianceBilin_stdGaussian,
      covarianceBilin_stdGaussian]
    rfl

/-- L1 §4.2: an orthogonal projection gives a chi-square quadratic form,
with degrees of freedom equal to its rank. -/
theorem gaussian_projection_quadratic_form (K : Submodule ℝ E) :
    HasLaw (fun x : E => ⟪x, K.starProjection x⟫_ℝ)
      (chiSquared (Module.finrank ℝ K)) (stdGaussian E) := by
  have h := (stdGaussian_norm_sq (E := K)).comp (stdGaussian_orthogonalProjection K)
  convert h using 1
  funext x
  change ⟪x, K.starProjection x⟫_ℝ = ‖K.orthogonalProjectionOnto x‖ ^ 2
  rw [real_inner_comm]
  exact K.re_inner_starProjection_eq_normSq x

/-- An idempotent self-adjoint linear operator is the orthogonal projection
onto its range, giving the rank version of the quadratic-form theorem. -/
theorem gaussian_idempotent_quadratic_form (A : E →ₗ[ℝ] E)
    (hA : A.IsSymmetric) (hId : IsIdempotentElem A) :
    HasLaw (fun x : E => ⟪x, A x⟫_ℝ)
      (chiSquared (Module.finrank ℝ (LinearMap.range A))) (stdGaussian E) := by
  obtain ⟨_, he⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp
    (show A.IsSymmetricProjection from ⟨hId, hA⟩)
  have h := gaussian_projection_quadratic_form (LinearMap.range A)
  convert h using 1
  funext x
  exact congrArg (fun y => ⟪x, y⟫_ℝ) (LinearMap.congr_fun he x)

end Euclidean

/-- L1 §4.2 in matrix notation. Symmetry is essential in addition to idempotence. -/
theorem normal_matrix_quadratic_form {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {Z : Fin n → Ω → ℝ} (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P)
    (hind : iIndepFun Z P) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) (hId : M * M = M) :
    HasLaw (fun ω => ∑ i, Z i ω * (∑ j, M i j * Z j ω)) (chiSquared M.rank) P := by
  have hvec : HasLaw (fun ω => WithLp.toLp 2 (fun i => Z i ω))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) P :=
    (show HasLaw (WithLp.toLp 2) (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (Measure.pi fun _ => gaussianReal 0 1) from
        ⟨(WithLp.measurable_toLp _ _).aemeasurable, map_pi_eq_stdGaussian⟩).comp
          (hind.hasLaw_pi hZ)
  have hsym : M.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hM)
  have hid : IsIdempotentElem M.toEuclideanLin := by
    change M.toEuclideanLin * M.toEuclideanLin = M.toEuclideanLin
    ext x i
    change (M.toEuclideanLin (M.toEuclideanLin x)) i = (M.toEuclideanLin x) i
    simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
    rw [Matrix.mulVec_mulVec, hId]
  have hr : M.rank = Module.finrank ℝ (LinearMap.range M.toEuclideanLin) := by
    simpa only [Matrix.toEuclideanLin_eq_toLin_orthonormal] using!
      M.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have h := (gaussian_idempotent_quadratic_form M.toEuclideanLin hsym hid).comp hvec
  rw [← hr] at h
  convert h using 1
  funext ω
  simp [PiLp.inner_apply, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, mul_comm]

end LectureNotes
