import LectureNotes.BootstrapMeanIntervals
import LectureNotes.VarianceAsymptotics
import LectureNotes.NormalUnbiasedNP

noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

/-- The one-sample t statistic with the n−1 sample variance. -/
def oneSampleTStatistic {n : ℕ} (x : Fin n → ℝ) (μ₀ : ℝ) : ℝ :=
  (sampleMean x - μ₀) / Real.sqrt (sampleVariance x / n)

/-- L8's asymptotic t pivot requires only a finite second moment and positive
population variance; small samples with zero sample variance are included. -/
theorem iid_oneSampleT_clt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[X 0; P]) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => oneSampleTStatistic (fun i : Fin (n + 1) => X i ω) P[X 0]) id := by
  let σ := Real.sqrt Var[X 0; P]
  have hσ : 0 < σ := Real.sqrt_pos.mpr hv
  have hvar : Var[X 0; P] = σ ^ 2 := (Real.sq_sqrt hv.le).symm
  let S (n : ℕ) (ω : Ω) := Real.sqrt (sampleVariance (fun i : Fin (n + 1) => X i ω)) / σ
  have hSm n : Measurable (S n) := by unfold S sampleVariance sampleMean; fun_prop
  have hS : ConvergesInProbability P S (fun _ => 1) := by
    apply almost_sure_implies_probability (fun n => (hSm n).aemeasurable)
    filter_upwards [sampleVariance_strong_consistency hXm hX hind hident] with ω hω
    have h := (Real.continuous_sqrt.continuousAt.tendsto.comp
      (hω.comp (tendsto_add_atTop_nat 1))).div_const σ
    simpa only [Function.comp_def, hvar, Real.sqrt_sq_eq_abs, abs_of_pos hσ, div_self hσ.ne'] using! h
  have hZ := iid_sampleMean_standardized_clt hX hind hident σ hσ hvar
  have h := slutsky_div (by norm_num : (1 : ℝ) ≠ 0) hZ hS (fun n => (hSm n).aemeasurable)
  simp only [div_one] at h
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl)) h
  intro n
  apply ae_of_all
  intro ω
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hs : Real.sqrt ((n + 1 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  dsimp only [S, oneSampleTStatistic]
  rw [Real.sqrt_div' _ hn.le]
  by_cases hz : Real.sqrt (sampleVariance (fun i : Fin (n + 1) => X i ω)) = 0
  · simp [hz]
  · simp only [Nat.cast_add, Nat.cast_one] at *
    field_simp

/-- A standard-normal distributional limit calibrates the symmetric two-tail
test at every interior level. -/
theorem asymptotic_normal_two_tail_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : ℕ → Ω → ℝ}
    (hT : ConvergesInDistribution P (gaussianReal 0 1) T id)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω | distributionQuantile (gaussianReal 0 1) (1 - α / 2) < |T n ω|})
      atTop (𝓝 α) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  let c := distributionQuantile (gaussianReal 0 1) (1 - α / 2)
  let R : Set ℝ := {x | c < |x|}
  have hfront : frontier R ⊆ {-c, c} := by
    intro x hx
    have he : c = |x| := frontier_lt_subset_eq continuous_const continuous_abs hx
    have hx' : x = c ∨ x = -c := (abs_eq (by linarith [abs_nonneg x] : 0 ≤ c)).mp he.symm
    rcases hx' with h | h <;> simp [h]
  have hb : (gaussianReal 0 1).map id (frontier R) = 0 := by
    rw [Measure.map_id]
    apply measure_mono_null hfront
    have hnull := measure_union_null (measure_singleton (-c) (μ := gaussianReal 0 1))
      (measure_singleton c (μ := gaussianReal 0 1))
    simpa only [Set.singleton_union] using hnull
  have hlim := asymptotic_rejection_probability hT R
    (measurableSet_lt measurable_const measurable_id.abs) hb
  have hs := gaussianTwoTail_quantile_size 0 (by norm_num : (0 : ℝ≥0) < 1) hα
  rw [gaussianTwoTail, StatisticalTest.power_ofRejectionSet] at hs
  simp only [NNReal.coe_one, Real.sqrt_one, mul_one, sub_zero] at hs
  simpa only [R, c, mem_ofPred_eq, id_eq, hs] using hlim

/-- The actual one-sample two-sided test has asymptotic size α under its
mean null, without assuming normality of the observations. -/
theorem iid_oneSampleT_null_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[X 0; P]) {μ₀ : ℝ} (hnull : P[X 0] = μ₀)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω | distributionQuantile (gaussianReal 0 1) (1 - α / 2) <
      |oneSampleTStatistic (fun i : Fin (n + 1) => X i ω) μ₀|}) atTop (𝓝 α) := by
  have h := iid_oneSampleT_clt hXm hX hind hident hv
  rw [hnull] at h
  exact asymptotic_normal_two_tail_size h hα

end LectureNotes
