import LectureNotes.MeanVarianceAsymptotics
import LectureNotes.BootstrapMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A nondegenerate population with values −1 and 1, each with probability one half. -/
def symmetricCoinLaw : Measure ℝ := empiricalLaw (![-1, 1] : Fin 2 → ℝ)

instance symmetricCoinLaw_probability : IsProbabilityMeasure symmetricCoinLaw := by
  unfold symmetricCoinLaw
  infer_instance

theorem symmetricCoinLaw_memLp (p : ℝ≥0∞) : MemLp id p symmetricCoinLaw :=
  empiricalLaw_memLp _ p

theorem symmetricCoinLaw_mean : (∫ x : ℝ, x ∂symmetricCoinLaw) = 0 := by
  rw [symmetricCoinLaw, empiricalLaw_mean]
  norm_num [sampleMean, Fin.sum_univ_two]

theorem symmetricCoinLaw_variance : Var[id; symmetricCoinLaw] = 1 := by
  rw [symmetricCoinLaw, empiricalLaw_variance]
  norm_num [empiricalVariance, sampleMean, Fin.sum_univ_two]

theorem symmetricCoinLaw_fourth_moment : (∫ x : ℝ, x ^ 4 ∂symmetricCoinLaw) = 1 := by
  rw [symmetricCoinLaw, empiricalLaw_integral _ (by fun_prop)]
  norm_num [Fin.sum_univ_two]

/-- The gradient of h(mean,variance)=variance is nonzero everywhere. -/
theorem variance_projection_derivative (m v : ℝ) :
    HasFDerivAt (fun z : ℝ × ℝ => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (m, v) ∧
      (ContinuousLinearMap.snd ℝ ℝ ℝ) ≠ 0 := by
  refine ⟨(ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt, ?_⟩
  intro h
  have hh := DFunLike.congr_fun h (0, 1)
  norm_num at hh

/-- The variance-coordinate influence is identically zero on this population,
so finite fourth moments and a nonzero gradient do not ensure positive
asymptotic influence variance. A standard-normal calibration needs that
additional condition. -/
theorem nonzero_gradient_zero_influence_variance :
    (ContinuousLinearMap.snd ℝ ℝ ℝ) ≠ 0 ∧
      MemLp (id : ℝ → ℝ) 4 symmetricCoinLaw ∧
      Var[id; symmetricCoinLaw] = 1 ∧
      Var[fun x : ℝ => (ContinuousLinearMap.snd ℝ ℝ ℝ)
        (x - ∫ y : ℝ, y ∂symmetricCoinLaw,
          (x - ∫ y : ℝ, y ∂symmetricCoinLaw) ^ 2 - Var[id; symmetricCoinLaw]);
        symmetricCoinLaw] = 0 := by
  refine ⟨(variance_projection_derivative 0 1).2, symmetricCoinLaw_memLp 4,
    symmetricCoinLaw_variance, ?_⟩
  simp only [ContinuousLinearMap.coe_snd', Prod.snd]
  simp only [symmetricCoinLaw_mean, symmetricCoinLaw_variance, sub_zero]
  have hm : (∫ x : ℝ, x ^ 2 - 1 ∂symmetricCoinLaw) = 0 := by
    rw [symmetricCoinLaw, empiricalLaw_integral _ (by fun_prop)]
    norm_num [Fin.sum_univ_two]
  rw [variance_eq_integral (by fun_prop), hm]
  simp only [sub_zero]
  rw [symmetricCoinLaw, empiricalLaw_integral _ (by fun_prop)]
  norm_num [Fin.sum_univ_two]

end LectureNotes
