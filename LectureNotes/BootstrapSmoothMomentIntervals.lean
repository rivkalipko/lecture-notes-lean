import LectureNotes.BootstrapSmoothMoments
import LectureNotes.MeanVarianceAsymptotics
import LectureNotes.BootstrapIntervals
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- The basic bootstrap interval for a smooth function of the mean and sample
variance has nominal limiting coverage under finite fourth moment, an actual
strict derivative, and positive influence variance. -/
theorem iid_basic_bootstrap_smooth_moment_interval_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (h : C(ℝ × ℝ, ℝ)) (D : (ℝ × ℝ) →L[ℝ] ℝ)
    (hd : HasStrictFDerivAt h D (P[X 0], Var[X 0; P]))
    (hv : 0 < Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P]) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => P.real {ω | h (P[X 0], Var[X 0; P]) ∈ Icc
      (smoothMomentStatistic h (fun i : Fin (n + 1) => X i ω) -
        distributionQuantile (bootstrapSmoothMomentDifferenceLaw h (fun i : Fin (n + 1) => X i ω)) b)
      (smoothMomentStatistic h (fun i : Fin (n + 1) => X i ω) -
        distributionQuantile (bootstrapSmoothMomentDifferenceLaw h (fun i : Fin (n + 1) => X i ω)) a)})
      atTop (𝓝 (b - a)) := by
  let σ := Real.sqrt (Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P])
  have hσ : 0 < σ := Real.sqrt_pos.mpr hv
  have hσsq : Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P] = σ ^ 2 := (Real.sq_sqrt hv.le).symm
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  let E (n : ℕ) (ω : Ω) := smoothMomentStatistic h (fun i : Fin (n + 1) => X i ω)
  let S (n : ℕ) (_ω : Ω) := σ / Real.sqrt ((n : ℝ) + 1)
  let B (n : ℕ) (ω : Ω) := bootstrapSmoothMomentErrorLaw h (fun i : Fin (n + 1) => X i ω) σ
  have hT : ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => (E n ω - h (P[X 0], Var[X 0; P])) / S n ω) id := by
    convert! iid_mean_variance_function_standardized_clt hXm hX hind hident h.continuous D hd.hasFDerivAt σ hσ hσsq using 1
    funext n ω
    dsimp only [E, S, smoothMomentStatistic]
    rw [div_div_eq_mul_div]
    ring
  have hcov := bootstrap_interval_coverage B (gaussianReal 0 1)
    (E := E) (S := S) (θ := h (P[X 0], Var[X 0; P]))
    (fun n => ae_of_all _ (fun _ => div_pos hσ (Real.sqrt_pos.mpr (by positivity))))
    (fun n => by dsimp only [E, S]; unfold smoothMomentStatistic sampleVariance sampleMean; fun_prop)
    hT HasLaw.id (gaussian_cdf_strictMono 0 1 (by norm_num))
    (iid_bootstrap_smooth_moment_cdf hXm hX hind hident h D hd σ hσ hσsq) ha hb hab
    (fun n => measurable_data_bootstrapSmoothMomentErrorLaw_quantile
      (fun i : Fin (n + 1) => X i) (fun i => hXm i) h σ ha)
    (fun n => measurable_data_bootstrapSmoothMomentErrorLaw_quantile
      (fun i : Fin (n + 1) => X i) (fun i => hXm i) h σ hb)
  have hqa n ω : distributionQuantile (B n ω) a * S n ω =
      distributionQuantile (bootstrapSmoothMomentDifferenceLaw h (fun i : Fin (n + 1) => X i ω)) a := by
    simpa only [B, S, Nat.cast_add, Nat.cast_one] using
      bootstrapSmoothMomentErrorLaw_quantile_rescale h (fun i : Fin (n + 1) => X i ω) σ hσ ha
  have hqb n ω : distributionQuantile (B n ω) b * S n ω =
      distributionQuantile (bootstrapSmoothMomentDifferenceLaw h (fun i : Fin (n + 1) => X i ω)) b := by
    simpa only [B, S, Nat.cast_add, Nat.cast_one] using
      bootstrapSmoothMomentErrorLaw_quantile_rescale h (fun i : Fin (n + 1) => X i ω) σ hσ hb
  simpa only [hqa, hqb, E] using! hcov


/-- The two-sided basic bootstrap smooth-moment test has limiting rejection
probability α under its smooth-moment null. Quantiles of the unscaled resampling
error are equivalent to L8's square-root scaled critical values. -/
theorem iid_basic_bootstrap_smooth_moment_test_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (h : C(ℝ × ℝ, ℝ)) (D : (ℝ × ℝ) →L[ℝ] ℝ)
    (hd : HasStrictFDerivAt h D (P[X 0], Var[X 0; P]))
    (hv : 0 < Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P])
    (v₀ : ℝ) (hnull : h (P[X 0], Var[X 0; P]) = v₀) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω |
      smoothMomentStatistic h (fun i : Fin (n + 1) => X i ω) - v₀ ∉ Icc
        (distributionQuantile (bootstrapSmoothMomentDifferenceLaw h
          (fun i : Fin (n + 1) => X i ω)) (α / 2))
        (distributionQuantile (bootstrapSmoothMomentDifferenceLaw h
          (fun i : Fin (n + 1) => X i ω)) (1 - α / 2))}) atTop (𝓝 α) := by
  have ha : α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hb : 1 - α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hab : α / 2 ≤ 1 - α / 2 := by linarith [hα.2]
  let E (n : ℕ) (ω : Ω) := smoothMomentStatistic h (fun i : Fin (n + 1) => X i ω)
  let A (n : ℕ) (ω : Ω) := distributionQuantile (bootstrapSmoothMomentDifferenceLaw h
    (fun i : Fin (n + 1) => X i ω)) (α / 2)
  let B (n : ℕ) (ω : Ω) := distributionQuantile (bootstrapSmoothMomentDifferenceLaw h
    (fun i : Fin (n + 1) => X i ω)) (1 - α / 2)
  have hqm (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) (n : ℕ) : Measurable
      (fun ω => distributionQuantile (bootstrapSmoothMomentDifferenceLaw h
        (fun i : Fin (n + 1) => X i ω)) q) := by
    have hm := (measurable_data_bootstrapSmoothMomentErrorLaw_quantile
      (fun i : Fin (n + 1) => X i) (fun i => hXm i) h 1 hq).mul_const
        (1 / Real.sqrt ((n : ℝ) + 1))
    have he : (fun ω => distributionQuantile (bootstrapSmoothMomentDifferenceLaw h
        (fun i : Fin (n + 1) => X i ω)) q) =
        (fun ω => distributionQuantile (bootstrapSmoothMomentErrorLaw h
          (fun i : Fin (n + 1) => X i ω) 1) q * (1 / Real.sqrt ((n : ℝ) + 1))) := by
      funext ω
      simpa only [Nat.cast_add, Nat.cast_one] using
        (bootstrapSmoothMomentErrorLaw_quantile_rescale h (fun i : Fin (n + 1) => X i ω) 1 (by norm_num) hq).symm
    rw [he]
    exact hm
  have hAm n : Measurable (A n) := hqm _ ha n
  have hBm n : Measurable (B n) := hqm _ hb n
  have hEm n : Measurable (E n) := by dsimp only [E]; unfold smoothMomentStatistic sampleVariance sampleMean; fun_prop
  have hm n : MeasurableSet {ω | v₀ ∈ Icc (E n ω - B n ω) (E n ω - A n ω)} :=
    (measurableSet_le ((hEm n).sub (hBm n)) measurable_const).inter
      (measurableSet_le measurable_const ((hEm n).sub (hAm n)))
  have hc := iid_basic_bootstrap_smooth_moment_interval_coverage hXm hX hind hident h D hd hv ha hb hab
  rw [hnull] at hc
  have he n : {ω | E n ω - v₀ ∉ Icc (A n ω) (B n ω)} =
      {ω | v₀ ∈ Icc (E n ω - B n ω) (E n ω - A n ω)}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_Icc]
    apply not_congr
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub hc
  convert! hh using 1
  · funext n
    change P.real {ω | E n ω - v₀ ∉ Icc (A n ω) (B n ω)} = _
    rw [he, measureReal_compl (hm n), probReal_univ]
  · ring


/-- The lecture's C² formulation, using the actual Fréchet derivative and a
positive influence variance in place of the insufficient nonzero-gradient
condition. -/
theorem iid_C2_bootstrap_moment_test_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (h : C(ℝ × ℝ, ℝ)) (hh : ContDiff ℝ 2 h)
    (hv : 0 < Var[fun ω => (fderiv ℝ h (P[X 0], Var[X 0; P])) (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P])
    (v₀ : ℝ) (hnull : h (P[X 0], Var[X 0; P]) = v₀) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω |
      smoothMomentStatistic h (fun i : Fin (n + 1) => X i ω) - v₀ ∉ Icc
        (distributionQuantile (bootstrapSmoothMomentDifferenceLaw h
          (fun i : Fin (n + 1) => X i ω)) (α / 2))
        (distributionQuantile (bootstrapSmoothMomentDifferenceLaw h
          (fun i : Fin (n + 1) => X i ω)) (1 - α / 2))}) atTop (𝓝 α) := by
  exact iid_basic_bootstrap_smooth_moment_test_size hXm hX hind hident h
    (fderiv ℝ h (P[X 0], Var[X 0; P])) (hh.hasStrictFDerivAt (by norm_num)) hv v₀ hnull hα

end LectureNotes
