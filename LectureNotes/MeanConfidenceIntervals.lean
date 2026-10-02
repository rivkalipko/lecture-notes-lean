import LectureNotes.MeanTests
import LectureNotes.BootstrapStudentizedIntervals
import LectureNotes.NormalHighestDensity

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- Ordinary normal-quantile mean intervals have their nominal asymptotic
coverage under finite second moments. The n−1 sample variance may vanish in
finite samples; that exceptional event has probability tending to zero. -/
theorem iid_mean_normal_interval_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[X 0; P]) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => P.real {ω | P[X 0] ∈ Icc
      (sampleMean (fun i : Fin (n + 1) => X i ω) -
        distributionQuantile (gaussianReal 0 1) b *
          Real.sqrt (sampleVariance (fun i : Fin (n + 1) => X i ω) / ((n : ℝ) + 1)))
      (sampleMean (fun i : Fin (n + 1) => X i ω) -
        distributionQuantile (gaussianReal 0 1) a *
          Real.sqrt (sampleVariance (fun i : Fin (n + 1) => X i ω) / ((n : ℝ) + 1)))})
      atTop (𝓝 (b - a)) := by
  let V n ω := sampleVariance (fun i : Fin (n + 1) => X i ω)
  let S n ω := Real.sqrt (V n ω / ((n : ℝ) + 1))
  have hV : ConvergesInProbability P V (fun _ => Var[X 0; P]) := by
    apply almost_sure_implies_probability
      (fun n => by dsimp only [V]; unfold sampleVariance sampleMean; fun_prop)
    filter_upwards [sampleVariance_strong_consistency hXm hX hind hident] with ω hω
    exact hω.comp (tendsto_add_atTop_nat 1)
  have hbad : Tendsto (fun n => P.real {ω | S n ω ≤ 0}) atTop (𝓝 0) := by
    have hh := tendstoInMeasure_iff_measureReal_norm.mp hV _ hv
    apply squeeze_zero (fun _ => measureReal_nonneg) _ hh
    intro n
    refine measureReal_mono ?_ (measure_ne_top P _)
    intro ω hω
    have hle : V n ω ≤ 0 := by
      by_contra! hpos
      exact (not_le.mpr (Real.sqrt_pos.mpr (div_pos hpos (by positivity)))) hω
    change Var[X 0; P] ≤ ‖V n ω - Var[X 0; P]‖
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have ht : ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => (sampleMean (fun i : Fin (n + 1) => X i ω) - P[X 0]) / S n ω) id := by
    simpa only [oneSampleTStatistic, Nat.cast_add, Nat.cast_one, S, V] using
      iid_oneSampleT_clt hXm hX hind hident hv
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  exact bootstrap_interval_coverage_of_rare_nonpositive_scale
    (fun _ _ => gaussianReal 0 1) (gaussianReal 0 1) hbad
    (fun n => by dsimp only [S, V]; unfold sampleVariance sampleMean; fun_prop)
    ht HasLaw.id (gaussian_cdf_strictMono 0 1 (by norm_num))
    (ae_of_all _ (fun _ _ => tendsto_const_nhds)) ha hb hab
    (fun _ => measurable_const) (fun _ => measurable_const)

/-- The displayed equal-tailed interval with the estimated standard error. -/
theorem iid_mean_equalTailed_interval_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[X 0; P]) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω | P[X 0] ∈ Icc
      (sampleMean (fun i : Fin (n + 1) => X i ω) -
        distributionQuantile (gaussianReal 0 1) (1 - α / 2) *
          Real.sqrt (sampleVariance (fun i : Fin (n + 1) => X i ω) / ((n : ℝ) + 1)))
      (sampleMean (fun i : Fin (n + 1) => X i ω) +
        distributionQuantile (gaussianReal 0 1) (1 - α / 2) *
          Real.sqrt (sampleVariance (fun i : Fin (n + 1) => X i ω) / ((n : ℝ) + 1)))})
      atTop (𝓝 (1 - α)) := by
  have ha : α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hb : 1 - α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hs : distributionQuantile (gaussianReal 0 1) (α / 2) =
      -distributionQuantile (gaussianReal 0 1) (1 - α / 2) := by
    have h := standardNormal_quantile_symmetry ha
    linarith
  have hh := iid_mean_normal_interval_coverage hXm hX hind hident hv ha hb (by linarith [hα.2])
  simp_rw [hs, neg_mul, sub_neg_eq_add] at hh
  convert hh using 1
  congr 1
  ring

end LectureNotes
