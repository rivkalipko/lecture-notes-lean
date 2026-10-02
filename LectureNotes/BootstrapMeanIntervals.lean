import LectureNotes.BootstrapMeanQuantiles
import LectureNotes.BootstrapIntervals
import LectureNotes.IIDScoreAsymptotics

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
attribute [local instance] bootstrapLaw_isProbabilityMeasure

/-- The sampling CLT for the standardized sample mean, with n+1 observations,
under exactly the same IID finite-second-moment assumptions as the bootstrap. -/
theorem iid_sampleMean_standardized_clt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : MemLp (X 0) 2 P) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (σ : ℝ) (hσ : 0 < σ) (hvar : Var[X 0; P] = σ ^ 2) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => Real.sqrt ((n : ℝ) + 1) / σ *
        (sampleMean (fun i : Fin (n + 1) => X i ω) - P[X 0])) id := by
  let g : ℝ → ℝ := fun x => (x - P[X 0]) / σ
  have hg : Measurable g := by unfold g; fun_prop
  have h₂ : MemLp (fun ω => g (X 0 ω)) 2 P := by
    simpa only [g, div_eq_mul_inv, Pi.sub_apply] using!
      (hX.sub (memLp_const (P[X 0]))).mul_const σ⁻¹
  have hm : (∫ ω, g (X 0 ω) ∂P) = 0 := by
    dsimp only [g]
    rw [integral_div, integral_sub (hX.integrable (by norm_num)) (integrable_const _)]
    simp
  have hv : Var[fun ω => g (X 0 ω); P] = (1 : ℝ≥0) := by
    simp only [g, div_eq_mul_inv]
    rw [variance_mul_const, variance_sub_const hX.aestronglyMeasurable, hvar]
    simp [hσ.ne']
  have hh := iid_zero_mean_score_clt X g hg hind hident h₂ hm hv
    (show HasLaw id (gaussianReal 0 1) (gaussianReal 0 1) from HasLaw.id)
  have hs : ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => Real.sqrt (n + 1 : ℕ) *
        ((∑ i ∈ Finset.range (n + 1), g (X i ω)) / (n + 1 : ℕ))) id :=
    { forall_aemeasurable := fun n => hh.forall_aemeasurable (n + 1)
      tendsto := hh.tendsto.comp (tendsto_add_atTop_nat 1) }
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl)) hs
  intro n
  apply ae_of_all
  intro ω
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [g, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, sampleMean, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => X i ω) (n + 1)]
  simp only [Nat.cast_add, Nat.cast_one] at *
  field_simp

section FiniteSample
variable {n : ℕ} [NeZero n]

/-- The unnormalized bootstrap error law used by the basic bootstrap interval. -/
def bootstrapMeanDifferenceLaw (x : Fin n → ℝ) : Measure ℝ :=
  (bootstrapLaw x).map (fun b => sampleMean b - sampleMean x)

instance bootstrapMeanDifferenceLaw_isProbabilityMeasure (x : Fin n → ℝ) :
    IsProbabilityMeasure (bootstrapMeanDifferenceLaw x) :=
  Measure.isProbabilityMeasure_map (by unfold sampleMean; fun_prop)

/-- Normalization of a bootstrap error scales every interior quantile by the
same positive factor. The population scale cancels in the basic interval. -/
theorem bootstrapMeanErrorLaw_quantile_rescale (x : Fin n → ℝ)
    (σ : ℝ) (hσ : 0 < σ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    distributionQuantile (bootstrapMeanErrorLaw x σ) q * (σ / Real.sqrt n) =
      distributionQuantile (bootstrapMeanDifferenceLaw x) q := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  let e := OrderIso.mulLeft₀ (Real.sqrt n / σ) (div_pos hs hσ)
  have he : bootstrapMeanErrorLaw x σ = (bootstrapMeanDifferenceLaw x).map e := by
    unfold bootstrapMeanErrorLaw bootstrapMeanDifferenceLaw
    rw [Measure.map_map (by fun_prop) (by unfold sampleMean; fun_prop)]
    rfl
  rw [he, distributionQuantile_orderIso _ e hq]
  change ((Real.sqrt n / σ) * _) * (σ / Real.sqrt n) = _
  field_simp
end FiniteSample

/-- L11's basic nonparametric bootstrap confidence interval for an IID mean.
Both the sampling CLT and the conditional resampling approximation are derived
from a finite second moment and positive population variance. The interval
uses exact conditional quantiles of the unnormalized resampling error, so
it requires no population or estimated standard error. -/
theorem iid_basic_bootstrap_mean_interval_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[X 0; P]) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => P.real {ω | P[X 0] ∈ Icc
      (sampleMean (fun i : Fin (n + 1) => X i ω) -
        distributionQuantile (bootstrapMeanDifferenceLaw (fun i : Fin (n + 1) => X i ω)) b)
      (sampleMean (fun i : Fin (n + 1) => X i ω) -
        distributionQuantile (bootstrapMeanDifferenceLaw (fun i : Fin (n + 1) => X i ω)) a)})
      atTop (𝓝 (b - a)) := by
  let σ := Real.sqrt (Var[X 0; P])
  have hσ : 0 < σ := Real.sqrt_pos.mpr hv
  have hσsq : Var[X 0; P] = σ ^ 2 := (Real.sq_sqrt hv.le).symm
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  let E (n : ℕ) (ω : Ω) := sampleMean (fun i : Fin (n + 1) => X i ω)
  let S (n : ℕ) (_ω : Ω) := σ / Real.sqrt ((n : ℝ) + 1)
  let B (n : ℕ) (ω : Ω) := bootstrapMeanErrorLaw (fun i : Fin (n + 1) => X i ω) σ
  have hT : ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => (E n ω - P[X 0]) / S n ω) id := by
    convert! iid_sampleMean_standardized_clt hX hind hident σ hσ hσsq using 1
    funext n ω
    dsimp only [E, S]
    rw [div_div_eq_mul_div]
    ring
  have h := bootstrap_interval_coverage B (gaussianReal 0 1)
    (E := E) (S := S) (θ := P[X 0])
    (fun n => ae_of_all _ (fun _ => div_pos hσ (Real.sqrt_pos.mpr (by positivity))))
    (fun n => by dsimp only [E, S]; unfold sampleMean; fun_prop)
    hT HasLaw.id (gaussian_cdf_strictMono 0 1 (by norm_num))
    (iid_bootstrap_mean_cdf hXm hX hind hident σ hσ hσsq) ha hb hab
    (fun n => measurable_data_bootstrapMeanErrorLaw_quantile
      (fun i : Fin (n + 1) => X i) (fun i => hXm i) σ ha)
    (fun n => measurable_data_bootstrapMeanErrorLaw_quantile
      (fun i : Fin (n + 1) => X i) (fun i => hXm i) σ hb)
  have hqa n ω : distributionQuantile (B n ω) a * S n ω =
      distributionQuantile (bootstrapMeanDifferenceLaw (fun i : Fin (n + 1) => X i ω)) a := by
    simpa only [B, S, Nat.cast_add, Nat.cast_one] using
      bootstrapMeanErrorLaw_quantile_rescale (fun i : Fin (n + 1) => X i ω) σ hσ ha
  have hqb n ω : distributionQuantile (B n ω) b * S n ω =
      distributionQuantile (bootstrapMeanDifferenceLaw (fun i : Fin (n + 1) => X i ω)) b := by
    simpa only [B, S, Nat.cast_add, Nat.cast_one] using
      bootstrapMeanErrorLaw_quantile_rescale (fun i : Fin (n + 1) => X i ω) σ hσ hb
  simpa only [hqa, hqb, E] using! h

end LectureNotes
