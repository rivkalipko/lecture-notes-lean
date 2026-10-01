import LectureNotes.GaussianMahalanobis
import LectureNotes.QuantileIntervals
import LectureNotes.SamplingAtomlessness
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false

/-! L7/L10/L11: consistent inversion of a covariance matrix, the vector Wald
limit, and its asymptotic coverage. The vector Gaussian limit and covariance
consistency are hypotheses, not conclusions about an arbitrary fitted model. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology InnerProductSpace Matrix.Norms.Elementwise

namespace MatrixProbability
scoped instance matrixMeasurableSpace {d : ℕ} : MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))
scoped instance matrixBorelSpace {d : ℕ} : BorelSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))
scoped instance matrixSecondCountable {d : ℕ} : SecondCountableTopology (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
end MatrixProbability
open scoped MatrixProbability

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- Continuous mapping at a deterministic limit, for arbitrary metric spaces. -/
theorem continuous_mapping_probability_const_metric {E F : Type*}
    [PseudoMetricSpace E] [PseudoMetricSpace F] {X : ℕ → Ω → E} {c : E} {g : E → F}
    (hg : ContinuousAt g c) (h : TendstoInMeasure P X atTop (fun _ => c)) :
    TendstoInMeasure P (fun n ω => g (X n ω)) atTop (fun _ => g c) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Metric.continuousAt_iff.mp hg ε hε
  have hb (n) : P.real {ω | ε ≤ dist (g (X n ω)) (g c)} ≤
      P.real {ω | δ ≤ dist (X n ω) c} := by
    refine measureReal_mono ?_ (measure_ne_top P _)
    intro ω hω
    by_contra hn
    exact (not_lt_of_ge hω) (hbound (lt_of_not_ge hn))
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
    (tendstoInMeasure_iff_measureReal_dist.mp h δ hδ)

theorem measurable_matrix_inverse {d : ℕ} :
    Measurable (fun S : Matrix (Fin d) (Fin d) ℝ => S⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable

/-- The approximating matrices need not be invertible at every sample size.
Lean's total matrix inverse is used; continuity is needed only at the nonsingular limit. -/
theorem covariance_inverse_consistency {d : ℕ}
    {S : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ} {V : Matrix (Fin d) (Fin d) ℝ}
    (hV : V.det ≠ 0) (hS : TendstoInMeasure P S atTop (fun _ => V)) :
    TendstoInMeasure P (fun n ω => (S n ω)⁻¹) atTop (fun _ => V⁻¹) := by
  apply continuous_mapping_probability_const_metric (c := V) _ hS
  apply continuousAt_matrix_inv
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hV

theorem probability_product_const {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {X : ℕ → Ω → E} {Y : ℕ → Ω → F} {a : E} {b : F}
    (hX : TendstoInMeasure P X atTop (fun _ => a))
    (hY : TendstoInMeasure P Y atTop (fun _ => b)) :
    TendstoInMeasure P (fun n ω => (X n ω, Y n ω)) atTop (fun _ => (a, b)) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  have hb n : P.real {ω | ε ≤ dist (X n ω, Y n ω) (a, b)} ≤
      P.real {ω | ε ≤ dist (X n ω) a} + P.real {ω | ε ≤ dist (Y n ω) b} := by
    have he : {ω | ε ≤ dist (X n ω, Y n ω) (a, b)} =
        {ω | ε ≤ dist (X n ω) a} ∪ {ω | ε ≤ dist (Y n ω) b} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_union, Prod.dist_eq, le_max_iff]
    rw [he]
    exact measureReal_union_le _ _
  apply squeeze_zero (fun _ => measureReal_nonneg) hb
  simpa only [add_zero] using (tendstoInMeasure_iff_measureReal_dist.mp hX ε hε).add
    (tendstoInMeasure_iff_measureReal_dist.mp hY ε hε)

/-- The plug-in inverse information is consistent if information is continuous
at the true parameter and nonsingular there. -/
theorem plugin_information_inverse_consistency {d k : ℕ}
    {T : ℕ → Ω → EuclideanSpace ℝ (Fin k)} {θ : EuclideanSpace ℝ (Fin k)}
    {I : EuclideanSpace ℝ (Fin k) → Matrix (Fin d) (Fin d) ℝ}
    (hT : TendstoInMeasure P T atTop (fun _ => θ))
    (hI : ContinuousAt I θ) (hdet : (I θ).det ≠ 0) :
    TendstoInMeasure P (fun n ω => (I (T n ω))⁻¹) atTop (fun _ => (I θ)⁻¹) :=
  covariance_inverse_consistency hdet (continuous_mapping_probability_const_metric hI hT)

set_option maxHeartbeats 3000000 in
/-- Consistency of the estimated sandwich covariance. The transpose is needed
for a general estimating equation; for a symmetric Hessian it is redundant. -/
theorem sandwich_covariance_consistency {d : ℕ}
    {A B : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ} {H J : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.det ≠ 0) (hA : TendstoInMeasure P A atTop (fun _ => H))
    (hB : TendstoInMeasure P B atTop (fun _ => J)) :
    TendstoInMeasure P (fun n ω => (A n ω)⁻¹ * B n ω * ((A n ω)⁻¹)ᵀ)
      atTop (fun _ => H⁻¹ * J * (H⁻¹)ᵀ) := by
  have hg : Continuous (fun t : Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ =>
      t.1 * t.2 * t.1ᵀ) := (continuous_fst.mul continuous_snd).mul continuous_fst.matrix_transpose
  have hi := covariance_inverse_consistency hH hA
  have hp : TendstoInMeasure P (fun n ω => ((A n ω)⁻¹, B n ω)) atTop
      (fun _ => (H⁻¹, J)) := probability_product_const hi hB
  simpa only using! continuous_mapping_probability_const_metric
    (c := (H⁻¹, J))
    (g := fun t : Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ =>
      t.1 * t.2 * t.1ᵀ) hg.continuousAt
    hp

def matrixQuadratic {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : ℝ := ⟪z, toEuclideanCLM (𝕜 := ℝ) S z⟫_ℝ

theorem matrixQuadratic_eq_sum {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (z : EuclideanSpace ℝ (Fin d)) :
    matrixQuadratic S z = ∑ i, ∑ j, z i * S i j * z j := by
  simp only [matrixQuadratic, inner_toEuclideanCLM, dotProduct, Matrix.mulVec,
    Finset.mul_sum, mul_assoc]

theorem continuous_matrixQuadratic {d : ℕ} :
    Continuous (fun t : EuclideanSpace ℝ (Fin d) × Matrix (Fin d) (Fin d) ℝ =>
      matrixQuadratic t.2 t.1) := by
  simp only [matrixQuadratic_eq_sum]
  fun_prop

set_option backward.isDefEq.respectTransparency false in
/-- An estimated covariance matrix can be used in the Wald quadratic form.
No independence between the estimator and its estimated covariance is required. -/
theorem vector_wald_limit {d : ℕ}
    {E : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    {S : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ} {V : Matrix (Fin d) (Fin d) ℝ}
    (hV : V.PosDef)
    (hE : TendstoInDistribution E atTop Z (fun _ => P) Q)
    (hZ : HasLaw Z (multivariateGaussian 0 V) Q)
    (hS : TendstoInMeasure P S atTop (fun _ => V))
    (hSm : ∀ n, AEMeasurable (S n) P) :
    ConvergesInDistribution P Q (fun n ω => matrixQuadratic (S n ω)⁻¹ (E n ω))
      (fun ω => matrixQuadratic V⁻¹ (Z ω)) ∧
      HasLaw (fun ω => matrixQuadratic V⁻¹ (Z ω)) (chiSquared d) Q := by
  refine ⟨?_, ?_⟩
  · exact hE.continuous_comp_prodMk_of_tendstoInMeasure_const
      (mE' := MatrixProbability.matrixMeasurableSpace)
      (Y := fun n ω => (S n ω)⁻¹) (c := V⁻¹)
      (g := fun t : EuclideanSpace ℝ (Fin d) × Matrix (Fin d) (Fin d) ℝ =>
        matrixQuadratic t.2 t.1) continuous_matrixQuadratic
      (covariance_inverse_consistency hV.det_pos.ne' hS)
      (fun n => measurable_matrix_inverse.comp_aemeasurable (hSm n))
  · simpa only [sub_zero, matrixQuadratic] using normal_mahalanobis hV hZ

/-- A Wald ellipsoid with the chi-square quantile has the claimed pointwise
asymptotic coverage. Positive dimension rules out the atom of chi-square(0). -/
theorem vector_wald_coverage {d : ℕ} (hd : 0 < d)
    {E : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    {S : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ} {V : Matrix (Fin d) (Fin d) ℝ}
    (hV : V.PosDef)
    (hE : TendstoInDistribution E atTop Z (fun _ => P) Q)
    (hZ : HasLaw Z (multivariateGaussian 0 V) Q)
    (hS : TendstoInMeasure P S atTop (fun _ => V))
    (hSm : ∀ n, AEMeasurable (S n) P) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω | matrixQuadratic (S n ω)⁻¹ (E n ω) ≤
      distributionQuantile (chiSquared d) q}) atTop (𝓝 q) := by
  obtain ⟨hT, hL⟩ := vector_wald_limit hV hE hZ hS hSm
  have := chiSquared_nullSingletonClass hd
  have hb : Q.map (fun ω => matrixQuadratic V⁻¹ (Z ω))
      (frontier (Set.Iic (distributionQuantile (chiSquared d) q))) = 0 := by
    rw [hL.map_eq, frontier_Iic]
    exact measure_singleton _
  have h := asymptotic_rejection_probability hT
    (Set.Iic (distributionQuantile (chiSquared d) q)) measurableSet_Iic hb
  have he := hL.measureReal_eq (p := fun t => t ≤ distributionQuantile (chiSquared d) q)
    measurableSet_Iic
  simp only [Set.mem_Iic] at h
  rw [he] at h
  change Tendsto _ atTop (𝓝 ((chiSquared d).real
    (Set.Iic (distributionQuantile (chiSquared d) q)))) at h
  rw [distributionQuantile_exact (chiSquared d) q hq] at h
  exact h

end LectureNotes
