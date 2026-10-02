import LectureNotes.NormalJointSufficiency
import LectureNotes.SufficiencyObstruction
import LectureNotes.NormalSampling

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Every coordinate in the actual joint experiment has the specified normal law. -/
theorem normalJointExperiment_eval_hasLaw (n : ℕ) (θ : NormalLocationScaleParameter)
    (i : Fin n) : HasLaw (fun y : Fin n → ℝ => y i) (gaussianReal θ.1 θ.2.val)
      (normalJointExperiment n θ) :=
  ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _ : Fin n => gaussianReal θ.1 θ.2.val) i).map_eq⟩

/-- All positive-variance normal product models have the same null sets. -/
theorem normalJointExperiment_absolutelyContinuous (n : ℕ)
    (θ η : NormalLocationScaleParameter) :
    normalJointExperiment n θ ≪ normalJointExperiment n η := by
  rw [normalJointExperiment, normalJointExperiment,
    normal_pi_withDensity _ _ θ.2.property.ne', normal_pi_withDensity _ _ η.2.property.ne']
  apply (withDensity_absolutelyContinuous _ _).trans
  apply withDensity_absolutelyContinuous' (show Measurable
    (fun y : Fin n → ℝ => ∏ i, gaussianPDF η.1 η.2.val (y i)) from by fun_prop).aemeasurable
  exact ae_of_all _ (fun y => Finset.prod_ne_zero_iff.mpr
    (fun i _ => (gaussianPDF_pos η.1 η.2.property.ne' (y i)).ne'))

/-- The sample variance carries the unknown variance in its actual expectation. -/
theorem normalJointExperiment_sampleVariance_expectation {n : ℕ} (hn : 1 < n)
    (θ : NormalLocationScaleParameter) :
    (normalJointExperiment n θ)[sampleVariance] = (θ.2.val : ℝ) := by
  have hlaw := normalJointExperiment_eval_hasLaw n θ
  exact sampleVariance_unbiased hn (fun i => (hlaw i).hasGaussianLaw.memLp_two)
    (fun _ _ hij => (iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)).indepFun hij)
    (fun i => by simpa using (hlaw i).integral_eq)
    (fun i => by simpa using (hlaw i).variance_eq)

/-- The sample mean alone is not sufficient when both normal parameters are
unknown and at least two observations are available. The sample-size condition
is necessary: with one observation the mean is the full data. -/
theorem normal_joint_sampleMean_not_sufficient {n : ℕ} (hn : 1 < n) :
    ¬ IsSufficientStatistic (normalJointExperiment n) (sampleMean : (Fin n → ℝ) → ℝ) := by
  intro hs
  let θ₀ : NormalLocationScaleParameter := (0, ⟨1, by norm_num⟩)
  let θ₁ : NormalLocationScaleParameter := (0, ⟨2, by norm_num⟩)
  have hi : IndepFun (sampleMean : (Fin n → ℝ) → ℝ) sampleVariance
      (normalJointExperiment n θ₀) :=
    normal_sampleMean_independent_sampleVariance hn (normalJointExperiment_eval_hasLaw n θ₀)
      (iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable))
  have hm : Measurable (sampleVariance : (Fin n → ℝ) → ℝ) := by
    unfold sampleVariance sampleMean
    fun_prop
  have he := sufficient_independent_statistic_law (normalJointExperiment n) hs θ₀
    (fun θ => normalJointExperiment_absolutelyContinuous n θ θ₀) hm hi θ₁
  have hid : IdentDistrib (sampleVariance : (Fin n → ℝ) → ℝ) sampleVariance
      (normalJointExperiment n θ₁) (normalJointExperiment n θ₀) :=
    ⟨hm.aemeasurable, hm.aemeasurable, he⟩
  have hh := hid.integral_eq
  rw [normalJointExperiment_sampleVariance_expectation hn θ₁,
    normalJointExperiment_sampleVariance_expectation hn θ₀] at hh
  norm_num [θ₀, θ₁] at hh

end LectureNotes
