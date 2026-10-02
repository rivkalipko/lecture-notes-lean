import LectureNotes.NormalUnknownVarianceMLE
import LectureNotes.MonteCarlo
import LectureNotes.NormalTestPower
import LectureNotes.BootstrapMeanIntervals

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

/-- The actual parametric resampling experiment obtained by fitting both
normal parameters by maximum likelihood and drawing a fresh IID sample.
At zero fitted variance the measure is a point mass; positive-variance MLE
claims are made only where the fitted variance is positive. -/
def normalParametricBootstrapLaw {n : ℕ} (x : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal (sampleMean x) (empiricalVariance x).toNNReal)

instance normalParametricBootstrapLaw_probability {n : ℕ} (x : Fin n → ℝ) :
    IsProbabilityMeasure (normalParametricBootstrapLaw x) := by
  unfold normalParametricBootstrapLaw
  infer_instance

theorem empiricalVariance_toNNReal {n : ℕ} (x : Fin n → ℝ) :
    ((empiricalVariance x).toNNReal : ℝ) = empiricalVariance x := by
  apply Real.coe_toNNReal
  unfold empiricalVariance
  positivity

theorem normal_parametricBootstrap_eval_hasLaw {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    HasLaw (fun b : Fin n → ℝ => b i)
      (gaussianReal (sampleMean x) (empiricalVariance x).toNNReal) (normalParametricBootstrapLaw x) :=
  ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩

/-- Refitting the mean to the parametric resample gives its exact Gaussian law. -/
theorem normal_parametricBootstrap_mean_hasLaw {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    HasLaw sampleMean
      (gaussianReal (sampleMean x) ((empiricalVariance x).toNNReal / n))
      (normalParametricBootstrapLaw x) := by
  exact normal_sampleMean hn (normal_parametricBootstrap_eval_hasLaw x)
    (iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable))

theorem normal_parametricBootstrap_mean_expectation {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    (normalParametricBootstrapLaw x)[sampleMean] = sampleMean x := by
  simpa using (normal_parametricBootstrap_mean_hasLaw hn x).integral_eq

/-- The conditional sampling variance uses the fitted MLE variance with
denominator n, just as in the parametric algorithm in L7. -/
theorem normal_parametricBootstrap_mean_variance {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    Var[sampleMean; normalParametricBootstrapLaw x] = empiricalVariance x / n := by
  simpa only [variance_id_gaussianReal, NNReal.coe_div, NNReal.coe_natCast,
    empiricalVariance_toNNReal] using (normal_parametricBootstrap_mean_hasLaw hn x).variance_eq

/-- Positive empirical variance makes the fitted normal parameter an actual
global maximizer of the original likelihood. -/
theorem normal_parametricBootstrap_fit_maximum {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : 0 < empiricalVariance x) (μ : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    (∏ i, gaussianPDFReal μ v (x i)) ≤
      ∏ i, gaussianPDFReal (sampleMean x) (empiricalVariance x).toNNReal (x i) := by
  have he : (empiricalVariance x).toNNReal = ⟨empiricalVariance x, hx.le⟩ := by
    apply NNReal.coe_injective
    exact empiricalVariance_toNNReal x
  rw [he]
  exact normal_mean_variance_maximizes_density hn x hx μ hv

/-- The centered square-root-n resampled mean has the fitted variance as
its exact variance parameter, including degenerate fitted data. -/
theorem normal_parametricBootstrap_mean_root_law {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    HasLaw (fun b => Real.sqrt n * (sampleMean b - sampleMean x))
      (gaussianReal 0 (empiricalVariance x).toNNReal) (normalParametricBootstrapLaw x) := by
  have h := gaussianReal_mul_const
    (gaussianReal_sub_const (normal_parametricBootstrap_mean_hasLaw hn x) (sampleMean x))
    (Real.sqrt n)
  have he : NNReal.mk (Real.sqrt (n : ℝ) ^ 2) (sq_nonneg _) *
      ((empiricalVariance x).toNNReal / (n : ℝ≥0)) = (empiricalVariance x).toNNReal := by
    apply NNReal.coe_injective
    change Real.sqrt (n : ℝ) ^ 2 * (((empiricalVariance x).toNNReal : ℝ) / (n : ℝ)) = _
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    field_simp
  convert! h using 1
  · funext b; ring
  · simp only [sub_self, mul_zero, he]

/-- Monte Carlo variance across independent parametric resamples converges
to the actual conditional variance of the refitted mean, for fixed data. -/
theorem normal_parametricBootstrap_monteCarlo_variance {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    {R : ℕ → Ω → (Fin n → ℝ)} (hRm : ∀ j, Measurable (R j))
    (hR : ∀ j, HasLaw (R j) (normalParametricBootstrapLaw x) Q) (hind : iIndepFun R Q) :
    ConvergesAlmostSurely Q
      (fun B ω => sampleVariance (fun j : Fin B => sampleMean (R j ω)))
      (fun _ => empiricalVariance x / n) := by
  have hm : Measurable (sampleMean : (Fin n → ℝ) → ℝ) := by unfold sampleMean; fun_prop
  have hY j := (normal_parametricBootstrap_mean_hasLaw hn x).comp (hR j)
  have hh := monteCarlo_variance_strong_consistency
    (fun j => hm.comp (hRm j)) (hY 0).hasGaussianLaw.memLp_two
    (hind.comp (fun _ => sampleMean) (fun _ => hm)) (fun j => (hY j).identDistrib (hY 0))
  have hv : Var[fun ω => sampleMean (R 0 ω); Q] = empiricalVariance x / n := by
    simpa only [Function.comp_def, variance_id_gaussianReal, NNReal.coe_div,
      NNReal.coe_natCast, empiricalVariance_toNNReal] using! (hY 0).variance_eq
  simpa only [Function.comp_def, hv] using! hh

/-- The conditional variance estimate is consistent on its natural n scale;
convergence of both unscaled variances to zero would be too weak a claim. -/
theorem iid_normal_parametricBootstrap_scaled_variance_consistency {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ConvergesAlmostSurely P (fun n ω => ((n : ℝ) + 1) *
      Var[sampleMean; normalParametricBootstrapLaw (fun i : Fin (n + 1) => X i ω)])
      (fun _ => Var[X 0; P]) := by
  filter_upwards [empiricalVariance_strong_consistency hXm hX hind hident] with ω hω
  have he (n : ℕ) : ((n : ℝ) + 1) *
      Var[sampleMean; normalParametricBootstrapLaw (fun i : Fin (n + 1) => X i ω)] =
      empiricalVariance (fun i : Fin (n + 1) => X i ω) := by
    rw [normal_parametricBootstrap_mean_variance (Nat.succ_pos n)]
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_succ]
    field_simp
    <;> ring
  simp_rw [he]
  exact hω.comp (tendsto_add_atTop_nat 1)

end LectureNotes
