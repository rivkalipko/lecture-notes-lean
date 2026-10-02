import LectureNotes.BootstrapLindeberg
import LectureNotes.LindebergRows
import LectureNotes.QuantileConvergence
import LectureNotes.NormalTestPower

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
attribute [local instance] bootstrapLaw_isProbabilityMeasure

section FiniteRow
variable {n : ℕ} [NeZero n]

/-- One centered summand of the normalized bootstrap sample mean. -/
def bootstrapMeanSummand (x : Fin n → ℝ) (σ : ℝ) (i : Fin n) (b : Fin n → ℝ) : ℝ :=
  (b i - sampleMean x) / (Real.sqrt n * σ)

/-- The actual conditional law of the normalized resampling error. -/
def bootstrapMeanErrorLaw (x : Fin n → ℝ) (σ : ℝ) : Measure ℝ :=
  (bootstrapLaw x).map (fun b => Real.sqrt n / σ * (sampleMean b - sampleMean x))

instance bootstrapMeanErrorLaw_isProbabilityMeasure (x : Fin n → ℝ) (σ : ℝ) :
    IsProbabilityMeasure (bootstrapMeanErrorLaw x σ) := by
  letI := bootstrapLaw_isProbabilityMeasure x
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  unfold sampleMean
  fun_prop

/-- Each bootstrap coordinate has precisely the empirical law. -/
theorem bootstrap_eval_hasLaw (x : Fin n → ℝ) (i : Fin n) :
    HasLaw (fun b : Fin n → ℝ => b i) (empiricalLaw x) (bootstrapLaw x) :=
  ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _ : Fin n => empiricalLaw x) i).map_eq⟩

/-- Integration of any measurable function of a bootstrap summand is a
finite empirical average over the observed values. -/
theorem bootstrapMeanSummand_integral (x : Fin n → ℝ) (σ : ℝ) (i : Fin n)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ b, f (bootstrapMeanSummand x σ i b) ∂bootstrapLaw x) =
      sampleMean (fun j => f ((x j - sampleMean x) / (Real.sqrt n * σ))) := by
  have h := (bootstrap_eval_hasLaw x i).integral_comp
    (show AEStronglyMeasurable (fun y => f ((y - sampleMean x) / (Real.sqrt n * σ)))
      (empiricalLaw x) from (by fun_prop : Measurable _).aestronglyMeasurable)
  change (∫ b, f (bootstrapMeanSummand x σ i b) ∂bootstrapLaw x) = _ at h
  rw [h, empiricalLaw_integral x (by fun_prop)]
  simp only [sampleMean, Fintype.card_fin, div_eq_mul_inv, mul_comm]

theorem bootstrapMeanSummand_memLp (x : Fin n → ℝ) (σ : ℝ) (i : Fin n) :
    MemLp (bootstrapMeanSummand x σ i) 2 (bootstrapLaw x) := by
  letI := bootstrapLaw_isProbabilityMeasure x
  have h : MemLp (fun b : Fin n → ℝ => b i) 2 (bootstrapLaw x) :=
    ((bootstrap_eval_hasLaw x i).identDistrib HasLaw.id).memLp_iff.mpr (empiricalLaw_memLp x 2)
  simpa only [bootstrapMeanSummand, div_eq_mul_inv, Pi.sub_apply] using!
    (h.sub (memLp_const (sampleMean x))).mul_const (Real.sqrt n * σ)⁻¹

theorem bootstrapMeanSummand_mean (x : Fin n → ℝ) (σ : ℝ) (i : Fin n) :
    (∫ b, bootstrapMeanSummand x σ i b ∂bootstrapLaw x) = 0 := by
  letI := bootstrapLaw_isProbabilityMeasure x
  have hi : Integrable (fun b : Fin n → ℝ => b i) (bootstrapLaw x) :=
    (((bootstrap_eval_hasLaw x i).identDistrib HasLaw.id).memLp_iff.mpr
      (empiricalLaw_memLp x 2)).integrable (by norm_num)
  change (∫ b, (b i - sampleMean x) / (Real.sqrt n * σ) ∂bootstrapLaw x) = 0
  rw [integral_div, integral_sub hi (integrable_const _),
    (bootstrap_eval_hasLaw x i).integral_eq, empiricalLaw_mean]
  simp

theorem bootstrapMeanSummand_secondMoment (x : Fin n → ℝ) (σ : ℝ) (i : Fin n) :
    (∫ b, bootstrapMeanSummand x σ i b ^ 2 ∂bootstrapLaw x) =
      empiricalVariance x / (Real.sqrt n * σ) ^ 2 := by
  rw [bootstrapMeanSummand_integral x σ i (fun y => y ^ 2) (by fun_prop)]
  change (Fintype.card (Fin n) : ℝ)⁻¹ * (∑ j, ((x j - sampleMean x) / (Real.sqrt n * σ)) ^ 2) =
    ((∑ j, (x j - sampleMean x) ^ 2) / n) / (Real.sqrt n * σ) ^ 2
  simp only [Fintype.card_fin]
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  ring

/-- Exact reduction of the conditional Lindeberg term to the observed
centered empirical squared tail. -/
theorem bootstrapMeanSummand_truncSecondMoment (x : Fin n → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (i : Fin n) (δ : ℝ) :
    truncSecondMoment (bootstrapLaw x) (bootstrapMeanSummand x σ i) δ =
      sampleMean (fun j => if δ * (Real.sqrt n * σ) < |x j - sampleMean x|
        then (x j - sampleMean x) ^ 2 else 0) / (Real.sqrt n * σ) ^ 2 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hr : 0 < Real.sqrt n * σ := mul_pos (Real.sqrt_pos.mpr hn) hσ
  unfold truncSecondMoment
  rw [bootstrapMeanSummand_integral x σ i
    (fun y => if δ < |y| then y ^ 2 else 0)
    ((measurable_id.pow_const 2).indicator (measurableSet_lt measurable_const measurable_id.abs))]
  have he j : (if δ < |(x j - sampleMean x) / (Real.sqrt n * σ)|
      then ((x j - sampleMean x) / (Real.sqrt n * σ)) ^ 2 else 0) =
      (if δ * (Real.sqrt n * σ) < |x j - sampleMean x|
        then (x j - sampleMean x) ^ 2 else 0) / (Real.sqrt n * σ) ^ 2 := by
    simp only [abs_div, abs_of_pos hr, lt_div_iff₀ hr, div_pow]
    split_ifs <;> simp
  simp_rw [he]
  change (Fintype.card (Fin n) : ℝ)⁻¹ * (∑ j, (if δ * (Real.sqrt n * σ) < |x j - sampleMean x|
    then (x j - sampleMean x) ^ 2 else 0) / (Real.sqrt n * σ) ^ 2) = _
  rw [← Finset.sum_div]
  change (Fintype.card (Fin n) : ℝ)⁻¹ * (_ / (Real.sqrt n * σ) ^ 2) =
    ((Fintype.card (Fin n) : ℝ)⁻¹ * _) / (Real.sqrt n * σ) ^ 2
  ring

/-- Summing the row recovers the usual centered bootstrap mean exactly. -/
theorem bootstrapMeanSummand_sum (x : Fin n → ℝ) (σ : ℝ) (hσ : 0 < σ) (b : Fin n → ℝ) :
    (∑ i, bootstrapMeanSummand x σ i b) =
      Real.sqrt n / σ * (sampleMean b - sampleMean x) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hr : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hrsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn.le
  simp only [bootstrapMeanSummand, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sampleMean]
  field_simp [hn.ne', hσ.ne', hr]
  rw [hrsq]
  ring
theorem sum_const_div_sqrt_sq (a σ : ℝ) (hσ : 0 < σ) :
    (∑ _i : Fin n, a / (Real.sqrt n * σ) ^ 2) = a / σ ^ 2 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_pow, Real.sq_sqrt hn.le]
  field_simp
end FiniteRow

/-- A deterministic triangular sequence of empirical laws satisfies the
bootstrap CLT once its variances converge and its centered squared tails
vanish at the CLT scale. The row laws are the actual product resampling laws. -/
theorem bootstrap_mean_clt_of_empirical_lindeberg
    (x : ∀ n : ℕ, Fin (n + 1) → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hvar : Tendsto (fun n => empiricalVariance (x n)) atTop (𝓝 (σ ^ 2)))
    (htail : ∀ δ > 0, Tendsto
      (fun n : ℕ => sampleMean (fun i =>
        if δ * (Real.sqrt ((n : ℝ) + 1) * σ) < |x n i - sampleMean (x n)|
        then (x n i - sampleMean (x n)) ^ 2 else 0)) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n (b : Fin (n + 1) → ℝ) =>
        Real.sqrt ((n : ℝ) + 1) / σ * (sampleMean b - sampleMean (x n)))
      atTop id (fun n => bootstrapLaw (x n)) (gaussianReal 0 1) := by
  have hvar' : Tendsto
      (fun n => ∑ i, ∫ b, bootstrapMeanSummand (x n) σ i b ^ 2 ∂bootstrapLaw (x n))
      atTop (𝓝 1) := by
    simp_rw [bootstrapMeanSummand_secondMoment, sum_const_div_sqrt_sq _ σ hσ]
    convert! hvar.div_const (σ ^ 2) using 1
    congr 1
    exact (div_self (pow_ne_zero 2 hσ.ne')).symm
  have htail' : ∀ δ > 0, Tendsto
      (fun n => ∑ i, truncSecondMoment (bootstrapLaw (x n))
        (bootstrapMeanSummand (x n) σ i) δ) atTop (𝓝 0) := by
    intro δ hδ
    simp_rw [bootstrapMeanSummand_truncSecondMoment _ σ hσ,
      sum_const_div_sqrt_sq _ σ hσ, Nat.cast_add, Nat.cast_one]
    simpa only [zero_div] using (htail δ hδ).div_const (σ ^ 2)
  have h := lindeberg_feller_dependent_rows
    (X := fun n => bootstrapMeanSummand (x n) σ)
    (fun n i => by unfold bootstrapMeanSummand; fun_prop)
    (fun n i => bootstrapMeanSummand_memLp (x n) σ i)
    (fun n i => bootstrapMeanSummand_mean (x n) σ i)
    (fun n => iIndepFun_pi (fun _ : Fin (n + 1) =>
      (show Measurable (fun y : ℝ => (y - sampleMean (x n)) /
        (Real.sqrt (n + 1 : ℕ) * σ)) from by fun_prop).aemeasurable)) hvar' htail'
  convert! h using 1
  funext n b
  simpa only [Nat.cast_add, Nat.cast_one] using (bootstrapMeanSummand_sum (x n) σ hσ b).symm

/-- The nonparametric bootstrap CLT for the sample mean, almost surely in the
original IID data. Its only moment assumption is a finite second moment;
positive population variance supplies the normalization. -/
theorem iid_bootstrap_mean_clt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (σ : ℝ) (hσ : 0 < σ) (hvar : Var[X 0; P] = σ ^ 2) :
    ∀ᵐ ω ∂P, TendstoInDistribution
      (fun n (b : Fin (n + 1) → ℝ) => Real.sqrt ((n : ℝ) + 1) / σ *
        (sampleMean b - sampleMean (fun i : Fin (n + 1) => X i ω)))
      atTop id (fun n => bootstrapLaw (fun i : Fin (n + 1) => X i ω))
      (gaussianReal 0 1) := by
  filter_upwards [empiricalVariance_strong_consistency hXm hX hind hident,
    iid_empirical_bootstrap_lindeberg hXm hX hind hident σ hσ] with ω hv ht
  apply bootstrap_mean_clt_of_empirical_lindeberg (fun n i => X i ω) σ hσ _ ht
  have hv' := hv.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n => empiricalVariance (fun i : Fin (n + 1) => X i ω))
    atTop (𝓝 (Var[X 0; P])) at hv'
  simpa only [hvar] using hv'

/-- The actual conditional bootstrap CDF converges at every real threshold.
The almost-sure quantifier is outside the quantifier over thresholds. -/
theorem iid_bootstrap_mean_cdf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (σ : ℝ) (hσ : 0 < σ) (hvar : Var[X 0; P] = σ ^ 2) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, Tendsto
      (fun n => cdf (bootstrapMeanErrorLaw (fun i : Fin (n + 1) => X i ω) σ) t)
      atTop (𝓝 (cdf (gaussianReal 0 1) t)) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [iid_bootstrap_mean_clt hXm hX hind hident σ hσ hvar] with ω hω
  intro t
  have hb : (gaussianReal 0 1).map id (frontier (Iic t)) = 0 := by simp [frontier_Iic]
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hω.tendsto hb
  have hr := (ENNReal.continuousAt_toReal
    (measure_ne_top ((gaussianReal 0 1).map id) (Iic t))).tendsto.comp ht
  simp only [cdf_eq_real, measureReal_def]
  simpa only [ProbabilityMeasure.coe_mk, Measure.map_id, cdf_eq_real,
    measureReal_def, bootstrapMeanErrorLaw, Nat.cast_add, Nat.cast_one,
    Function.comp_apply] using! hr

/-- Every interior conditional bootstrap quantile converges almost surely to
its standard-normal quantile. Discrete finite-sample bootstrap laws are allowed. -/
theorem iid_bootstrap_mean_quantile_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (σ : ℝ) (hσ : 0 < σ) (hvar : Var[X 0; P] = σ ^ 2)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => distributionQuantile
        (bootstrapMeanErrorLaw (fun i : Fin (n + 1) => X i ω) σ) q)
      atTop (𝓝 (distributionQuantile (gaussianReal 0 1) q)) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [iid_bootstrap_mean_cdf hXm hX hind hident σ hσ hvar] with ω hω
  exact distributionQuantile_tendsto _ _ (gaussian_cdf_strictMono 0 1 (by norm_num)) hω hq

end LectureNotes
