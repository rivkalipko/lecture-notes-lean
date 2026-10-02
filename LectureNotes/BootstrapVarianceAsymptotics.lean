import LectureNotes.RowPerturbation
import LectureNotes.VarianceAsymptotics
import LectureNotes.InstrumentalVariables
import LectureNotes.BootstrapVarianceLaw

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
attribute [local instance] bootstrapLaw_isProbabilityMeasure

/-- Exact resampling decomposition at any population center, before taking
limits. The remainder involves only the error in the resampled mean. -/
theorem bootstrap_empiricalVariance_linear_decomposition {n : ℕ} (hn : 0 < n)
    (x b : Fin n → ℝ) (μ τ : ℝ) :
    Real.sqrt n / τ * (empiricalVariance b - empiricalVariance x) =
      Real.sqrt n / τ *
        (sampleMean (fun i => (b i - μ) ^ 2) - sampleMean (fun i => (x i - μ) ^ 2)) +
      (-2 * (sampleMean x - μ) / τ) * (Real.sqrt n * (sampleMean b - sampleMean x)) +
      (-1 / (τ * Real.sqrt n)) * (Real.sqrt n * (sampleMean b - sampleMean x)) ^ 2 := by
  have hb := empiricalVariance_normalized_decomposition b μ 0
  have hx := empiricalVariance_normalized_decomposition x μ 0
  simp only [sub_zero, sampleMean_sub_const hn] at hb hx
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hbase : Real.sqrt n * (empiricalVariance b - empiricalVariance x) =
      Real.sqrt n *
        (sampleMean (fun i => (b i - μ) ^ 2) - sampleMean (fun i => (x i - μ) ^ 2)) -
      Real.sqrt n * ((sampleMean b - μ) ^ 2 - (sampleMean x - μ) ^ 2) := by nlinarith
  calc
    _ = (Real.sqrt n * (empiricalVariance b - empiricalVariance x)) / τ := by ring
    _ = _ := by rw [hbase]; field_simp; ring

/-- The normalized resampling-mean error has exactly the observed empirical
variance as its second moment. -/
theorem bootstrap_normalized_mean_error_secondMoment {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    (∫ b, (Real.sqrt n * (sampleMean b - sampleMean x)) ^ 2 ∂bootstrapLaw x) =
      empiricalVariance x := by
  simp_rw [mul_pow]
  rw [integral_const_mul, bootstrap_sampleMean_mse,
    Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  exact mul_div_cancel₀ _ hn

/-- For any deterministic data rows whose mean and variance converge, the
nonlinear mean correction is negligible in the conditional resampling law.
Finite resampling support supplies the integrability; no eighth moment is used. -/
theorem bootstrap_variance_remainder_probability
    (x : ∀ n : ℕ, Fin (n + 1) → ℝ) (μ v τ : ℝ)
    (hm : Tendsto (fun n => sampleMean (x n)) atTop (𝓝 μ))
    (hv : Tendsto (fun n => empiricalVariance (x n)) atTop (𝓝 v)) :
    ∀ ε > 0, Tendsto (fun n => (bootstrapLaw (x n)).real {b : Fin (n + 1) → ℝ |
      ε ≤ |(-2 * (sampleMean (x n) - μ) / τ) *
        (Real.sqrt ((n : ℝ) + 1) * (sampleMean b - sampleMean (x n))) +
      (-1 / (τ * Real.sqrt ((n : ℝ) + 1))) *
        (Real.sqrt ((n : ℝ) + 1) * (sampleMean b - sampleMean (x n))) ^ 2|}) atTop (𝓝 0) := by
  let A n (b : Fin (n + 1) → ℝ) :=
    Real.sqrt ((n : ℝ) + 1) * (sampleMean b - sampleMean (x n))
  have hA n : MemLp (A n) 2 (bootstrapLaw (x n)) :=
    ((bootstrap_sampleMean_memLp (x n)).sub (memLp_const _)).const_mul _
  have hM : Tendsto (fun n => ∫ b, A n b ^ 2 ∂bootstrapLaw (x n)) atTop (𝓝 v) := by
    have he n : (∫ b, A n b ^ 2 ∂bootstrapLaw (x n)) = empiricalVariance (x n) := by
      simpa only [A, Nat.cast_add, Nat.cast_one] using bootstrap_normalized_mean_error_secondMoment (x n)
    simp_rw [he]
    exact hv
  have ha : Tendsto (fun n => -2 * (sampleMean (x n) - μ) / τ) atTop (𝓝 0) := by
    simpa using ((hm.sub_const μ).const_mul (-2)).div_const τ
  have hs : Tendsto (fun n : ℕ => (Real.sqrt ((n : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
  have hb : Tendsto (fun n : ℕ => -1 / (τ * Real.sqrt ((n : ℝ) + 1))) atTop (𝓝 0) := by
    convert! hs.const_mul (-1 / τ) using 1
    · funext n
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · simp
  exact row_small_polynomial_probability hA hM ha hb

/-- Resampling a transformed coordinate gives the same actual conditional
CDF whether the transformation precedes or follows drawing the indices. -/
theorem bootstrap_transformed_mean_error_cdf {n : ℕ} [NeZero n]
    (x : Fin n → ℝ) (g : ℝ → ℝ) (hg : Measurable g) (τ t : ℝ) :
    cdf (bootstrapMeanErrorLaw (fun i => g (x i)) τ) t =
      (bootstrapLaw x).real {b : Fin n → ℝ |
        Real.sqrt n / τ * (sampleMean (fun i => g (b i)) - sampleMean (fun i => g (x i))) ≤ t} := by
  rw [cdf_eq_real]
  change ((bootstrapLaw (fun i => g (x i))).map
    (fun b => Real.sqrt n / τ * (sampleMean b - sampleMean (fun i => g (x i))))).real (Iic t) = _
  rw [map_measureReal_apply (by unfold sampleMean; fun_prop) measurableSet_Iic,
    ← bootstrapLaw_map_statistic x hg,
    map_measureReal_apply (by fun_prop)
      (measurableSet_Iic.preimage (by unfold sampleMean; fun_prop))]
  rfl

/-- The conditional bootstrap empirical-variance CDF has the same Gaussian
limit as the original variance estimator, under finite fourth moment and
positive variance of the squared centered observation. -/
theorem iid_bootstrap_empiricalVariance_cdf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (τ : ℝ) (hτ : 0 < τ)
    (hvar : Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P] = τ ^ 2) :
    ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n =>
      (bootstrapLaw (fun i : Fin (n + 1) => X i ω)).real {b : Fin (n + 1) → ℝ |
        Real.sqrt ((n : ℝ) + 1) / τ *
          (empiricalVariance b - empiricalVariance (fun i : Fin (n + 1) => X i ω)) ≤ t})
      atTop (𝓝 (cdf (gaussianReal 0 1) t)) := by
  let μ := P[X 0]
  let g : ℝ → ℝ := fun x => (x - μ) ^ 2
  let Y : ℕ → Ω → ℝ := fun i ω => g (X i ω)
  have hgm : Measurable g := by dsimp [g]; fun_prop
  have hYm i : Measurable (Y i) := hgm.comp (hXm i)
  have hX2 : MemLp (X 0) 2 P := hX.mono_exponent (by norm_num)
  have hY2 : MemLp (Y 0) 2 P := by
    apply (memLp_two_iff_integrable_sq (hYm 0).aestronglyMeasurable).mpr
    have hfour := (hX.sub (memLp_const μ)).integrable_norm_pow' (p := 4)
    simpa only [Y, g, Pi.sub_apply, ← pow_mul, Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by norm_num,
      pow_mul, sq_abs] using hfour
  have hindY : iIndepFun Y P := hind.comp (fun _ => g) (fun _ => hgm)
  have hidentY i : IdentDistrib (Y i) (Y 0) P P := (hident i).comp hgm
  have hYcdf := iid_bootstrap_mean_cdf hYm hY2 hindY hidentY τ hτ hvar
  have hm := iid_sampleMean_succ_ae (hX2.integrable (by norm_num)) hind hident
  have hv := empiricalVariance_strong_consistency hXm hX2 hind hident
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [hYcdf, hm, hv] with ω hYω hmω hvω
  let x n : Fin (n + 1) → ℝ := fun i => X i ω
  have hvs : Tendsto (fun n => empiricalVariance (x n)) atTop (𝓝 (Var[X 0; P])) := by
    exact hvω.comp (tendsto_add_atTop_nat 1)
  let A n (b : Fin (n + 1) → ℝ) := Real.sqrt ((n : ℝ) + 1) / τ *
    (sampleMean (fun i => (b i - μ) ^ 2) - sampleMean (fun i => (x n i - μ) ^ 2))
  let R n (b : Fin (n + 1) → ℝ) :=
    (-2 * (sampleMean (x n) - μ) / τ) * (Real.sqrt ((n : ℝ) + 1) * (sampleMean b - sampleMean (x n))) +
    (-1 / (τ * Real.sqrt ((n : ℝ) + 1))) *
      (Real.sqrt ((n : ℝ) + 1) * (sampleMean b - sampleMean (x n))) ^ 2
  have hAcdf t : Tendsto (fun n => (bootstrapLaw (x n)).real {b | A n b ≤ t})
      atTop (𝓝 (cdf (gaussianReal 0 1) t)) := by
    apply (hYω t).congr
    intro n
    simpa only [Y, g, A, Nat.cast_add, Nat.cast_one] using!
      bootstrap_transformed_mean_error_cdf (x n) g hgm τ t
  have hR := bootstrap_variance_remainder_probability x μ (Var[X 0; P]) τ hmω hvs
  intro t
  have h := dependent_rows_additive_error_cdf (fun n => bootstrapLaw (x n)) A R
    (gaussianReal 0 1) hAcdf hR t
  convert! h using 1
  funext n
  congr 1
  ext b
  have he := bootstrap_empiricalVariance_linear_decomposition (Nat.succ_pos n) (x n) b μ τ
  simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one, A, R, x, Set.mem_ofPred_eq, add_assoc] using (congrArg (fun z : ℝ => z ≤ t) he).to_iff

/-- The exact denominator correction, including the totalized n=1 case. -/
theorem sampleVariance_eq_empiricalVariance_div {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    sampleVariance x = empiricalVariance x / (((n : ℝ) - 1) / n) := by
  unfold sampleVariance empiricalVariance
  exact (div_div_div_cancel_right₀ (Nat.cast_ne_zero.mpr (NeZero.ne n)) _ _).symm

/-- L8's actual denominator-(n-1) conditional bootstrap variance law has the
standard Gaussian limit. Finite fourth moment and a positive squared-deviation
variance suffice; no eighth moment or assumed resampling approximation is used. -/
theorem iid_bootstrap_sampleVariance_cdf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (τ : ℝ) (hτ : 0 < τ)
    (hvar : Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P] = τ ^ 2) :
    ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n =>
      cdf (bootstrapSampleVarianceErrorLaw (fun i : Fin (n + 1) => X i ω) τ) t)
      atTop (𝓝 (cdf (gaussianReal 0 1) t)) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [iid_bootstrap_empiricalVariance_cdf hXm hX hind hident τ hτ hvar] with ω hω
  let x n : Fin (n + 1) → ℝ := fun i => X i ω
  let Y n (b : Fin (n + 1) → ℝ) := Real.sqrt ((n : ℝ) + 1) / τ *
    (empiricalVariance b - empiricalVariance (x n))
  let S n (_b : Fin (n + 1) → ℝ) := (n : ℝ) / (n + 1)
  have hSc : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop 1
  have hS : ∀ ε > 0, Tendsto (fun n => (bootstrapLaw (x n)).real
      {b | ε ≤ |S n b - 1|}) atTop (𝓝 0) := by
    intro ε hε
    have he := ((hSc.sub_const 1).abs).eventually (gt_mem_nhds (by simpa using hε))
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    have hem : {b : Fin (n + 1) → ℝ | ε ≤ |S n b - 1|} = ∅ := by
      ext b
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr hn
    simp [hem]
  intro t
  have hh := dependent_rows_studentization_cdf (fun n => bootstrapLaw (x n)) Y S
    (gaussianReal 0 1) hω hS t
  apply hh.congr
  intro n
  rw [cdf_eq_real]
  unfold bootstrapSampleVarianceErrorLaw
  rw [map_measureReal_apply (by unfold sampleVariance sampleMean; fun_prop) measurableSet_Iic]
  congr 1
  ext b
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic,
    sampleVariance_eq_empiricalVariance_div, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  dsimp only [Y, S, x]
  rw [← sub_div, mul_div_assoc]

/-- Almost surely, the entire conditional CDF converges uniformly. -/
theorem iid_bootstrap_sampleVariance_cdf_uniform {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (τ : ℝ) (hτ : 0 < τ)
    (hvar : Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P] = τ ^ 2) :
    ∀ᵐ ω ∂P, TendstoUniformly
      (fun n => cdf (bootstrapSampleVarianceErrorLaw (fun i : Fin (n + 1) => X i ω) τ))
      (cdf (gaussianReal 0 1)) atTop := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [iid_bootstrap_sampleVariance_cdf hXm hX hind hident τ hτ hvar] with ω hω
  exact cdf_tendstoUniformly_of_pointwise _ _ hω

/-- Interior quantiles of the actual conditional variance law converge almost
surely, despite the discrete finite resampling distribution. -/
theorem iid_bootstrap_sampleVariance_quantile_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (τ : ℝ) (hτ : 0 < τ)
    (hvar : Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P] = τ ^ 2)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, Tendsto (fun n => distributionQuantile
      (bootstrapSampleVarianceErrorLaw (fun i : Fin (n + 1) => X i ω) τ) q)
      atTop (𝓝 (distributionQuantile (gaussianReal 0 1) q)) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [iid_bootstrap_sampleVariance_cdf hXm hX hind hident τ hτ hvar] with ω hω
  exact distributionQuantile_tendsto _ _ (gaussian_cdf_strictMono 0 1 (by norm_num)) hω hq

end LectureNotes
