import LectureNotes.BootstrapStudentizedAsymptotics
import LectureNotes.BootstrapMeanIntervals

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- Changing events on a set whose probability tends to zero does not change
the limiting probability. Neither event needs to be independent of that set. -/
theorem probability_limit_of_agree_off_rare_event {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B R : ℕ → Set Ω) {l : ℝ}
    (hB : Tendsto (fun n => P.real (B n)) atTop (𝓝 l))
    (hR : Tendsto (fun n => P.real (R n)) atTop (𝓝 0))
    (he : ∀ n ω, ω ∉ R n → (ω ∈ A n ↔ ω ∈ B n)) :
    Tendsto (fun n => P.real (A n)) atTop (𝓝 l) := by
  have hb n : P.real (B n) - P.real (R n) ≤ P.real (A n) ∧
      P.real (A n) ≤ P.real (B n) + P.real (R n) := by
    have hAB : A n ⊆ B n ∪ R n := by
      intro ω hω
      by_cases hR : ω ∈ R n
      · exact Or.inr hR
      · exact Or.inl ((he n ω hR).mp hω)
    have hBA : B n ⊆ A n ∪ R n := by
      intro ω hω
      by_cases hR : ω ∈ R n
      · exact Or.inr hR
      · exact Or.inl ((he n ω hR).mpr hω)
    have h₁ := (measureReal_mono (μ := P) hAB).trans (measureReal_union_le _ _)
    have h₂ := (measureReal_mono (μ := P) hBA).trans (measureReal_union_le _ _)
    exact ⟨by linarith, h₁⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [sub_zero] using hB.sub hR)
    (by simpa only [add_zero] using hB.add hR) (fun n => (hb n).1) (fun n => (hb n).2)

/-- Bootstrap interval coverage allows nonpositive scale estimates on events
whose probability vanishes. This includes zero empirical variances in small
samples and discrete populations. -/
theorem bootstrap_interval_coverage_of_rare_nonpositive_scale
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : ℕ → Ω → Measure ℝ) (ν : Measure ℝ)
    [∀ n ω, IsProbabilityMeasure (B n ω)] [IsProbabilityMeasure ν] [NullSingletonClass ν]
    {E S : ℕ → Ω → ℝ} {θ : ℝ} {Z : Ω' → ℝ}
    (hbad : Tendsto (fun n => P.real {ω | S n ω ≤ 0}) atTop (𝓝 0))
    (hm : ∀ n, Measurable (fun ω => (E n ω - θ) / S n ω))
    (hT : ConvergesInDistribution P Q (fun n ω => (E n ω - θ) / S n ω) Z)
    (hZ : HasLaw Z ν Q) (hstrict : StrictMono (cdf ν))
    (hconv : ∀ᵐ ω ∂P, ∀ x, Tendsto (fun n => cdf (B n ω) x) atTop (𝓝 (cdf ν x)))
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b)
    (hma : ∀ n, Measurable (fun ω => distributionQuantile (B n ω) a))
    (hmb : ∀ n, Measurable (fun ω => distributionQuantile (B n ω) b)) :
    Tendsto (fun n => P.real {ω | θ ∈ Icc
      (E n ω - distributionQuantile (B n ω) b * S n ω)
      (E n ω - distributionQuantile (B n ω) a * S n ω)}) atTop (𝓝 (b - a)) := by
  have hA := bootstrap_quantile_consistency B ν hstrict hconv ha (fun n => (hma n).aemeasurable)
  have hB := bootstrap_quantile_consistency B ν hstrict hconv hb (fun n => (hmb n).aemeasurable)
  have h := random_interval_probability hT hZ hA hB hm hma hmb
    (fun n ω => distributionQuantile_mono (B n ω) ha hb hab)
  rw [cdf_eq_real, cdf_eq_real, distributionQuantile_exact ν a ha,
    distributionQuantile_exact ν b hb] at h
  apply probability_limit_of_agree_off_rare_event P _ _ _ h hbad
  intro n ω hω
  exact (location_pivot_inversion _ _ _ _ _ (lt_of_not_ge hω)).symm

/-- The observed empirical standard deviation consistently estimates the
population standard deviation, requiring only a finite second moment. -/
theorem iid_sample_std_factor_consistent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (σ : ℝ) (hσ : 0 < σ) (hvar : Var[X 0; P] = σ ^ 2) :
    ConvergesInProbability P
      (fun n ω => Real.sqrt (empiricalVariance (fun i : Fin (n + 1) => X i ω)) / σ)
      (fun _ => 1) := by
  apply almost_sure_implies_probability
    (fun n => by unfold empiricalVariance sampleMean; fun_prop)
  filter_upwards [empiricalVariance_strong_consistency hXm hX hind hident] with ω hω
  have hh := hω.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n => empiricalVariance (fun i : Fin (n + 1) => X i ω))
    atTop (𝓝 (Var[X 0; P])) at hh
  have hs := (Real.continuous_sqrt.continuousAt.tendsto.comp hh).div_const σ
  simpa only [Function.comp_apply, hvar, Real.sqrt_sq_eq_abs, abs_of_pos hσ,
    div_self hσ.ne'] using! hs

/-- L11's bootstrap-t interval for an IID mean has its nominal asymptotic
coverage under a finite fourth moment and positive population variance.
Both original-sample and resampling standard errors are the actual empirical
standard deviations divided by square-root sample size. -/
theorem iid_studentized_bootstrap_mean_interval_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[X 0; P]) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => P.real {ω | P[X 0] ∈ Icc
      (sampleMean (fun i : Fin (n + 1) => X i ω) -
        distributionQuantile (bootstrapStudentizedMeanLaw (fun i : Fin (n + 1) => X i ω)) b *
          (Real.sqrt (empiricalVariance (fun i : Fin (n + 1) => X i ω)) / Real.sqrt ((n : ℝ) + 1)))
      (sampleMean (fun i : Fin (n + 1) => X i ω) -
        distributionQuantile (bootstrapStudentizedMeanLaw (fun i : Fin (n + 1) => X i ω)) a *
          (Real.sqrt (empiricalVariance (fun i : Fin (n + 1) => X i ω)) / Real.sqrt ((n : ℝ) + 1)))})
      atTop (𝓝 (b - a)) := by
  let σ := Real.sqrt (Var[X 0; P])
  have hσ : 0 < σ := Real.sqrt_pos.mpr hv
  have hvar : Var[X 0; P] = σ ^ 2 := (Real.sq_sqrt hv.le).symm
  have h₂ : MemLp (X 0) 2 P := hX.mono_exponent (by norm_num)
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  let E (n : ℕ) (ω : Ω) := sampleMean (fun i : Fin (n + 1) => X i ω)
  let V (n : ℕ) (ω : Ω) := empiricalVariance (fun i : Fin (n + 1) => X i ω)
  let S (n : ℕ) (ω : Ω) := Real.sqrt (V n ω) / Real.sqrt ((n : ℝ) + 1)
  let D (n : ℕ) (ω : Ω) := Real.sqrt (V n ω) / σ
  let B (n : ℕ) (ω : Ω) := bootstrapStudentizedMeanLaw (fun i : Fin (n + 1) => X i ω)
  have hD : ConvergesInProbability P D (fun _ => 1) :=
    iid_sample_std_factor_consistent hXm h₂ hind hident σ hσ hvar
  have hDm n : Measurable (D n) := by dsimp only [D, V]; unfold empiricalVariance sampleMean; fun_prop
  have hT : ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => (E n ω - P[X 0]) / S n ω) id := by
    have ht := slutsky_div (by norm_num : (1 : ℝ) ≠ 0)
      (iid_sampleMean_standardized_clt h₂ hind hident σ hσ hvar) hD
      (fun n => (hDm n).aemeasurable)
    apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => div_one _)) ht
    intro n
    apply ae_of_all
    intro ω
    dsimp only [E, S, D, V]
    rw [div_mul_eq_mul_div, div_div_div_cancel_right₀ hσ.ne', div_div_eq_mul_div]
    ring
  have hbad : Tendsto (fun n => P.real {ω | S n ω ≤ 0}) atTop (𝓝 0) := by
    have hh := tendstoInMeasure_iff_measureReal_norm.mp hD 1 (by norm_num)
    apply squeeze_zero (fun _ => measureReal_nonneg) _ hh
    intro n
    refine measureReal_mono ?_ (measure_ne_top P _)
    intro ω hω
    have hn : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hle : Real.sqrt (V n ω) / Real.sqrt ((n : ℝ) + 1) ≤ 0 := hω
    have hz : Real.sqrt (V n ω) = 0 :=
      le_antisymm (by simpa only [zero_mul] using (div_le_iff₀ hn).mp hle) (Real.sqrt_nonneg _)
    change 1 ≤ ‖Real.sqrt (V n ω) / σ - 1‖
    rw [hz]
    norm_num
  exact bootstrap_interval_coverage_of_rare_nonpositive_scale B (gaussianReal 0 1)
    (E := E) (S := S) (θ := P[X 0]) hbad
    (fun n => by dsimp only [E, S, V]; unfold empiricalVariance sampleMean; fun_prop)
    hT HasLaw.id (gaussian_cdf_strictMono 0 1 (by norm_num))
    (iid_bootstrap_studentized_mean_cdf hXm hX hind hident hv) ha hb hab
    (fun n => measurable_data_bootstrapStudentizedMeanLaw_quantile
      (fun i : Fin (n + 1) => X i) (fun i => hXm i) ha)
    (fun n => measurable_data_bootstrapStudentizedMeanLaw_quantile
      (fun i : Fin (n + 1) => X i) (fun i => hXm i) hb)

end LectureNotes
