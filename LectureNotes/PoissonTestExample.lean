import LectureNotes.LikelihoodRatio
import LectureNotes.ChiSquaredMoments
import LectureNotes.Inequalities
import LectureNotes.QuantileMeasurability
import LectureNotes.PValues
import LectureNotes.NormalLikelihoodRatio
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- A rational enclosure certifies the lecture's rounded LR value 17.7.
The bounds come from a finite logarithm series with a proved remainder. -/
theorem poisson_example_lr_bounds :
    (1767 : ℝ) / 100 < poissonLR 100 5 6 ∧ poissonLR 100 5 6 < 1769 / 100 := by
  have hl := Real.sum_range_le_log_div (x := (1 : ℝ) / 11) (by norm_num) (by norm_num) 3
  have hu := Real.log_div_le_sum_range_add (x := (1 : ℝ) / 11) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at hl hu
  have hi : Real.log ((5 : ℝ) / 6) = - Real.log ((6 : ℝ) / 5) := by
    rw [show (5 : ℝ) / 6 = ((6 : ℝ) / 5)⁻¹ by norm_num, Real.log_inv]
  dsimp [poissonLR]
  rw [hi]
  constructor <;> linarith

/-- The three example statistics have the ordering described in L10. -/
theorem poisson_example_statistic_order :
    poissonLM 100 5 6 < poissonLR 100 5 6 ∧
      poissonLR 100 5 6 < poissonWald 100 5 6 := by
  rw [poisson_example_wald, poisson_example_score]
  constructor <;> linarith [poisson_example_lr_bounds.1, poisson_example_lr_bounds.2]

/-- A rigorous coarse upper bound on the chi-square critical value suffices
to certify all three rejection decisions, without a decimal quantile table. -/
theorem chiSquared_one_quantile_95_le_ten :
    distributionQuantile (chiSquared 1) ((95 : ℝ) / 100) ≤ 10 := by
  have hmark := markov_inequality (μ := chiSquared 1)
    (X := fun x : ℝ => x ^ 2) (Filter.Eventually.of_forall (fun x => sq_nonneg x))
    ((chiSquared_memLp 1).integrable_sq) (M := 100) (by norm_num)
  rw [chiSquared_second_moment] at hmark
  have hm := measureReal_mono (μ := chiSquared 1)
    (show Ioi (10 : ℝ) ⊆ {x : ℝ | 100 ≤ x ^ 2} from by
      intro x hx; change 10 < x at hx; change 100 ≤ x ^ 2; nlinarith)
    (measure_ne_top _ _)
  have hc : (chiSquared 1).real (Ioi (10 : ℝ)) = 1 - cdf (chiSquared 1) 10 := by
    rw [show Ioi (10 : ℝ) = (Iic 10)ᶜ by ext x; simp,
      measureReal_compl measurableSet_Iic, probReal_univ, cdf_eq_real]
  rw [hc] at hm
  rw [distributionQuantile_le_iff _ (by constructor <;> norm_num)]
  norm_num at hmark
  linarith

/-- The large-sample LR, Wald and score rules all reject the displayed
Poisson null at significance 0.05. This is a decision about asymptotic rules,
not a claim of exact finite-sample size for the Poisson experiment. -/
theorem poisson_example_all_reject :
    distributionQuantile (chiSquared 1) ((95 : ℝ) / 100) < poissonLR 100 5 6 ∧
    distributionQuantile (chiSquared 1) ((95 : ℝ) / 100) < poissonWald 100 5 6 ∧
    distributionQuantile (chiSquared 1) ((95 : ℝ) / 100) < poissonLM 100 5 6 := by
  rw [poisson_example_wald, poisson_example_score]
  have hq := chiSquared_one_quantile_95_le_ten
  exact ⟨by linarith [poisson_example_lr_bounds.1], by linarith, by linarith⟩

/-- The chi-square law with one degree of freedom has the central-normal CDF. -/
theorem chiSquared_one_cdf {t : ℝ} (ht : 0 ≤ t) :
    cdf (chiSquared 1) t = 2 * cdf (gaussianReal 0 1) (Real.sqrt t) - 1 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hs := chiSquared_one_central_normal (Real.sqrt t) (Real.sqrt_nonneg t)
  rw [Real.sq_sqrt ht] at hs
  rw [cdf_eq_real, hs, ← measureReal_congr Ioc_ae_eq_Icc]
  rw [measureReal_def, ← measure_cdf (gaussianReal 0 1), StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ((monotone_cdf _) (by nlinarith [Real.sqrt_nonneg t])))]
  rw [standardNormal_cdf_neg]
  simp only [measure_cdf]
  ring

theorem chiSquared_one_cdf_strictMonoOn : StrictMonoOn (cdf (chiSquared 1)) (Ici 0) := by
  intro x hx y hy hxy
  rw [chiSquared_one_cdf hx, chiSquared_one_cdf hy]
  have h := gaussian_cdf_strictMono 0 1 (by norm_num)
    (Real.sqrt_lt_sqrt hx hxy)
  linarith

/-- Strict monotonicity of the common reference CDF proves the source's
strict ordering of asymptotic p-values. -/
theorem poisson_example_pvalue_order :
    upperTailPValue (chiSquared 1) id (poissonWald 100 5 6) <
      upperTailPValue (chiSquared 1) id (poissonLR 100 5 6) ∧
    upperTailPValue (chiSquared 1) id (poissonLR 100 5 6) <
      upperTailPValue (chiSquared 1) id (poissonLM 100 5 6) := by
  have hLM : poissonLM 100 5 6 ∈ Ici (0 : ℝ) := by rw [poisson_example_score]; norm_num
  have hLR : poissonLR 100 5 6 ∈ Ici (0 : ℝ) := by
    simp only [mem_Ici]; linarith [poisson_example_lr_bounds.1]
  have hW : poissonWald 100 5 6 ∈ Ici (0 : ℝ) := by rw [poisson_example_wald]; norm_num
  have h₁ := chiSquared_one_cdf_strictMonoOn hLM hLR poisson_example_statistic_order.1
  have h₂ := chiSquared_one_cdf_strictMonoOn hLR hW poisson_example_statistic_order.2
  dsimp [upperTailPValue]
  constructor <;> linarith

end LectureNotes
