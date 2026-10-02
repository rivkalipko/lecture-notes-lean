import LectureNotes.LinearContrasts

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Matrix
open scoped Topology MatrixProbability

/-- The law of a weighted difference of independent Gaussian vectors.
The covariance formula allows singular marginal covariances and zero weights. -/
theorem gaussian_independent_contrast {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    {X Y : Ω → EuclideanSpace ℝ (Fin d)}
    {μ ν : EuclideanSpace ℝ (Fin d)} {S T : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef)
    (hX : HasLaw X (multivariateGaussian μ S) P)
    (hY : HasLaw Y (multivariateGaussian ν T) P)
    (hind : IndepFun X Y P) (a b : ℝ) :
    HasLaw (fun ω => a • X ω - b • Y ω)
      (multivariateGaussian (a • μ - b • ν) (a^2 • S + b^2 • T)) P := by
  have hXp := hX.hasGaussianLaw.memLp_two
  have hYp := hY.hasGaussianLaw.memLp_two
  have hg : HasGaussianLaw (fun ω => a • X ω - b • Y ω) P :=
    iIndepFun.hasGaussianLaw_fun_sub (hX.hasGaussianLaw.fun_smul a)
      (hY.hasGaussianLaw.fun_smul b) (hind.comp (by fun_prop) (by fun_prop))
  have hmean : (∫ ω, a • X ω - b • Y ω ∂P) = a • μ - b • ν := by
    rw [integral_sub (show Integrable (fun ω => a • X ω) P from
      (hXp.const_smul a).integrable (by norm_num))
      (show Integrable (fun ω => b • Y ω) P from
      (hYp.const_smul b).integrable (by norm_num)), integral_smul, integral_smul,
      hX.integral_eq, hY.integral_eq, integral_id_multivariateGaussian,
      integral_id_multivariateGaussian]
  have hcov : vectorCovariance P (fun ω => a • X ω - b • Y ω) = a^2 • S + b^2 • T := by
    ext i j
    change cov[fun ω => a * X ω i - b * Y ω i,
      fun ω => a * X ω j - b * Y ω j;P] = a^2 * S i j + b^2 * T i j
    rw [covariance_fun_sub_fun_sub ((hXp.eval_piLp i).const_mul a)
      ((hYp.eval_piLp i).const_mul b) ((hXp.eval_piLp j).const_mul a)
      ((hYp.eval_piLp j).const_mul b)]
    simp only [covariance_const_mul_left, covariance_const_mul_right]
    have hcXY : cov[fun ω => X ω i, fun ω => Y ω j;P] = 0 :=
      (hind.comp (by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin d) => z i))
        (by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin d) => z j))).covariance_eq_zero
        (hXp.eval_piLp i) (hYp.eval_piLp j)
    have hcYX : cov[fun ω => Y ω i, fun ω => X ω j;P] = 0 :=
      (hind.symm.comp (by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin d) => z i))
        (by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin d) => z j))).covariance_eq_zero
        (hYp.eval_piLp i) (hXp.eval_piLp j)
    rw [hcXY, hcYX, hX.covariance_fun_comp (f := fun z => z i) (g := fun z => z j) (by fun_prop) (by fun_prop),
      hY.covariance_fun_comp (f := fun z => z i) (g := fun z => z j) (by fun_prop) (by fun_prop),
      covariance_eval_multivariateGaussian hS, covariance_eval_multivariateGaussian hT]
    ring
  exact ⟨hg.aemeasurable, by rw [gaussian_vector_law P hg, hmean, hcov]⟩

/-- The weighted difference on the product Gaussian probability space. -/
theorem gaussian_product_contrast {d : ℕ} {S T : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) (a b : ℝ) :
    HasLaw (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      a • z.1 - b • z.2) (multivariateGaussian 0 (a^2 • S + b^2 • T))
      ((multivariateGaussian 0 S).prod (multivariateGaussian 0 T)) := by
  simpa only [smul_zero, sub_zero] using gaussian_independent_contrast (μ := 0) (ν := 0) hS hT
    measurePreserving_fst.hasLaw measurePreserving_snd.hasLaw
    (indepFun_prod measurable_id measurable_id) a b

end LectureNotes
