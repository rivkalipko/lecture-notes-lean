import LectureNotes.ParametricNormalBootstrap
import LectureNotes.UniformCDFConvergence

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

/-- The law of the centered/scaled mean refitted to the actual parametric
normal resample. -/
def normalParametricMeanErrorLaw {n : ℕ} (x : Fin n → ℝ) (σ : ℝ) : Measure ℝ :=
  (normalParametricBootstrapLaw x).map (fun b => Real.sqrt n / σ * (sampleMean b - sampleMean x))

instance normalParametricMeanErrorLaw_probability {n : ℕ} (x : Fin n → ℝ) (σ : ℝ) :
    IsProbabilityMeasure (normalParametricMeanErrorLaw x σ) :=
  Measure.isProbabilityMeasure_map (by unfold sampleMean; fun_prop)

theorem normal_parametricBootstrap_mean_error_law {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (σ : ℝ) :
    normalParametricMeanErrorLaw x σ =
      gaussianReal 0 ((empiricalVariance x).toNNReal / NNReal.mk (σ ^ 2) (sq_nonneg σ)) := by
  have hh := gaussianReal_div_const (normal_parametricBootstrap_mean_root_law hn x) σ
  have hf : (fun b : Fin n → ℝ => Real.sqrt n / σ * (sampleMean b - sampleMean x)) =
      (fun b => (Real.sqrt n * (sampleMean b - sampleMean x)) / σ) := by funext b; ring
  simpa only [normalParametricMeanErrorLaw, hf, zero_div] using hh.map_eq

/-- A positive limiting Gaussian variance gives pointwise CDF convergence.
Zero variance at finitely many or rare fitted rows causes no problem. -/
theorem gaussian_zero_cdf_tendsto_of_variance {v : ℕ → ℝ≥0} {v₀ : ℝ≥0}
    (hv : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 (v₀ : ℝ))) (hv₀ : 0 < v₀) (t : ℝ) :
    Tendsto (fun n => cdf (gaussianReal 0 (v n)) t) atTop (𝓝 (cdf (gaussianReal 0 v₀) t)) := by
  have hpos : (0 : ℝ) < v₀ := by exact_mod_cast hv₀
  have hsd : Real.sqrt (v₀ : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hrat : Tendsto (fun n => t / Real.sqrt (v n : ℝ)) atTop
      (𝓝 (t / Real.sqrt (v₀ : ℝ))) :=
    (tendsto_const_nhds (x := t)).div ((Real.continuous_sqrt.tendsto _).comp hv) hsd
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hc := (continuous_cdf_of_atomless (gaussianReal 0 1)).continuousAt.tendsto.comp hrat
  have h₀ : cdf (gaussianReal 0 v₀) t = cdf (gaussianReal 0 1) (t / Real.sqrt v₀) := by
    simpa only [id_eq, sub_zero, cdf_eq_real, mem_Iic] using!
      normal_lower_tail hv₀ (show HasLaw id (gaussianReal 0 v₀) (gaussianReal 0 v₀) from HasLaw.id) t
  rw [h₀]
  apply hc.congr'
  filter_upwards [hv.eventually (lt_mem_nhds hpos)] with n hn
  have hvn : 0 < v n := by exact_mod_cast hn
  have he := normal_lower_tail hvn
    (show HasLaw id (gaussianReal 0 (v n)) (gaussianReal 0 (v n)) from HasLaw.id) t
  simpa only [Function.comp_def, id_eq, sub_zero, cdf_eq_real, mem_Iic] using! he.symm

/-- Parametric normal resampling consistently approximates the mean's
normalized law. This even holds for nonnormal IID data with finite second
moments: only this mean statistic, not an arbitrary fitted MLE, is asserted. -/
theorem iid_normal_parametricBootstrap_mean_cdf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (σ : ℝ) (hσ : 0 < σ) (hvar : Var[X 0; P] = σ ^ 2) :
    ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n =>
      cdf (normalParametricMeanErrorLaw (fun i : Fin (n + 1) => X i ω) σ) t)
      atTop (𝓝 (cdf (gaussianReal 0 1) t)) := by
  filter_upwards [empiricalVariance_strong_consistency hXm hX hind hident] with ω hω
  let v (n : ℕ) : ℝ≥0 := (empiricalVariance (fun i : Fin (n + 1) => X i ω)).toNNReal /
    NNReal.mk (σ ^ 2) (sq_nonneg σ)
  have hv : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 ((1 : ℝ≥0) : ℝ)) := by
    dsimp only [v]
    simp only [NNReal.coe_div, NNReal.coe_mk, empiricalVariance_toNNReal]
    have hh := (hω.comp (tendsto_add_atTop_nat 1)).div_const (σ ^ 2)
    simpa only [Function.comp_def, NNReal.coe_one, hvar, div_self (pow_ne_zero 2 hσ.ne')] using! hh
  intro t
  simp_rw [normal_parametricBootstrap_mean_error_law (Nat.succ_pos _)]
  exact gaussian_zero_cdf_tendsto_of_variance (v := v) (v₀ := 1) hv (by norm_num) t

theorem iid_normal_parametricBootstrap_mean_cdf_uniform {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (σ : ℝ) (hσ : 0 < σ) (hvar : Var[X 0; P] = σ ^ 2) :
    ∀ᵐ ω ∂P, TendstoUniformly
      (fun n => cdf (normalParametricMeanErrorLaw (fun i : Fin (n + 1) => X i ω) σ))
      (cdf (gaussianReal 0 1)) atTop := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [iid_normal_parametricBootstrap_mean_cdf hXm hX hind hident σ hσ hvar] with ω hω
  exact cdf_tendstoUniformly_of_pointwise _ _ hω

theorem iid_normal_parametricBootstrap_mean_quantile {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (σ : ℝ) (hσ : 0 < σ) (hvar : Var[X 0; P] = σ ^ 2)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, Tendsto (fun n => distributionQuantile
      (normalParametricMeanErrorLaw (fun i : Fin (n + 1) => X i ω) σ) q) atTop
      (𝓝 (distributionQuantile (gaussianReal 0 1) q)) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [iid_normal_parametricBootstrap_mean_cdf hXm hX hind hident σ hσ hvar] with ω hω
  exact distributionQuantile_tendsto _ _ (gaussian_cdf_strictMono 0 1 (by norm_num)) hω hq

end LectureNotes
