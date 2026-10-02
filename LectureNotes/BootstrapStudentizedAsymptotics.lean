import LectureNotes.BootstrapVarianceConsistency
import LectureNotes.BootstrapStudentizedLaw
import LectureNotes.RowStudentization
import LectureNotes.UniformCDFConvergence

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
attribute [local instance] bootstrapLaw_isProbabilityMeasure

/-- The basic bootstrap error approximation is uniform over every CDF
threshold, almost surely, under finite-second-moment IID sampling. -/
theorem iid_bootstrap_mean_cdf_uniform {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (σ : ℝ) (hσ : 0 < σ) (hvar : Var[X 0; P] = σ ^ 2) :
    ∀ᵐ ω ∂P, TendstoUniformly
      (fun n t => cdf (bootstrapMeanErrorLaw (fun i : Fin (n + 1) => X i ω) σ) t)
      (cdf (gaussianReal 0 1)) atTop := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [iid_bootstrap_mean_cdf hXm hX hind hident σ hσ hvar] with ω hω
  exact cdf_tendstoUniformly_of_pointwise _ _ hω

/-- Studentized bootstrap-mean CDF validity under IID sampling with a finite
fourth moment. Zero-variance resamples remain in the actual bootstrap law;
their effect vanishes by conditional variance consistency. -/
theorem iid_bootstrap_studentized_mean_cdf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[X 0; P]) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, Tendsto
      (fun n => cdf (bootstrapStudentizedMeanLaw (fun i : Fin (n + 1) => X i ω)) t)
      atTop (𝓝 (cdf (gaussianReal 0 1) t)) := by
  let σ := Real.sqrt (Var[X 0; P])
  have hσ : 0 < σ := Real.sqrt_pos.mpr hv
  have hvar : Var[X 0; P] = σ ^ 2 := (Real.sq_sqrt hv.le).symm
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have h₂ : MemLp (X 0) 2 P := hX.mono_exponent (by norm_num)
  filter_upwards [iid_bootstrap_mean_cdf hXm h₂ hind hident σ hσ hvar,
    iid_bootstrap_studentization_factor hXm hX hind hident σ hσ hvar] with ω hCDF hS
  let R (n : ℕ) := bootstrapLaw (fun i : Fin (n + 1) => X i ω)
  let Y (n : ℕ) (b : Fin (n + 1) → ℝ) := Real.sqrt ((n : ℝ) + 1) / σ *
    (sampleMean b - sampleMean (fun i : Fin (n + 1) => X i ω))
  let S (n : ℕ) (b : Fin (n + 1) → ℝ) := Real.sqrt (empiricalVariance b) / σ
  have hYm n : Measurable (Y n) := by dsimp only [Y]; unfold sampleMean; fun_prop
  have hSm n : Measurable (S n) := by dsimp only [S]; unfold empiricalVariance sampleMean; fun_prop
  have he n t : cdf (bootstrapMeanErrorLaw (fun i : Fin (n + 1) => X i ω) σ) t =
      (R n).real {b | Y n b ≤ t} := by
    rw [cdf_eq_real, bootstrapMeanErrorLaw, map_measureReal_apply
      (by unfold sampleMean; fun_prop) measurableSet_Iic]
    simp only [R, Y, Nat.cast_add, Nat.cast_one]
    rfl
  have hY : ∀ t, Tendsto (fun n => (R n).real {b | Y n b ≤ t})
      atTop (𝓝 (cdf (gaussianReal 0 1) t)) := by
    intro t
    simpa only [he] using hCDF t
  have hmap n : (R n).map (fun b => Y n b / S n b) =
      bootstrapStudentizedMeanLaw (fun i : Fin (n + 1) => X i ω) := by
    unfold bootstrapStudentizedMeanLaw
    dsimp only [R]
    congr 1
    funext b
    dsimp only [Y, S]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [div_mul_eq_mul_div, div_div_div_cancel_right₀ hσ.ne']
  intro t
  have hh := dependent_rows_studentization_map_cdf R Y S hYm hSm
    (gaussianReal 0 1) hY hS t
  simpa only [hmap] using hh

/-- The studentized bootstrap approximation holds uniformly over the whole
real line, on one almost-sure event for the original data. -/
theorem iid_bootstrap_studentized_mean_cdf_uniform {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[X 0; P]) :
    ∀ᵐ ω ∂P, TendstoUniformly
      (fun n t => cdf (bootstrapStudentizedMeanLaw (fun i : Fin (n + 1) => X i ω)) t)
      (cdf (gaussianReal 0 1)) atTop := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [iid_bootstrap_studentized_mean_cdf hXm hX hind hident hv] with ω hω
  exact cdf_tendstoUniformly_of_pointwise _ _ hω

/-- Interior conditional bootstrap-t quantiles consistently estimate the
standard-normal quantiles. -/
theorem iid_bootstrap_studentized_mean_quantile_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[X 0; P]) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => distributionQuantile
        (bootstrapStudentizedMeanLaw (fun i : Fin (n + 1) => X i ω)) q)
      atTop (𝓝 (distributionQuantile (gaussianReal 0 1) q)) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [iid_bootstrap_studentized_mean_cdf hXm hX hind hident hv] with ω hω
  exact distributionQuantile_tendsto _ _ (gaussian_cdf_strictMono 0 1 (by norm_num)) hω hq

end LectureNotes
