import LectureNotes.BootstrapMomentRows
import LectureNotes.BootstrapSmoothMomentsLaw
import LectureNotes.RowDeltaMethod

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
attribute [local instance] bootstrapLaw_isProbabilityMeasure

/-- An actual strict derivative gives the conditional delta-method remainder
for the resampled mean and denominator-(n-1) variance. Tightness is derived
from finite transformed second moments and the exact variance linearization. -/
theorem bootstrap_smooth_moment_remainder_probability
    (x : ∀ n : ℕ, Fin (n + 1) → ℝ) (μ v w : ℝ)
    (hxc : Tendsto (fun n => (sampleMean (x n), sampleVariance (x n))) atTop (𝓝 (μ, v)))
    (hv : Tendsto (fun n => empiricalVariance (x n)) atTop (𝓝 v))
    (hw : Tendsto (fun n => empiricalVariance (fun i => (x n i - μ) ^ 2)) atTop (𝓝 w))
    {h : ℝ × ℝ → ℝ} {D : (ℝ × ℝ) →L[ℝ] ℝ}
    (hd : HasStrictFDerivAt h D (μ, v)) :
    ∀ ε > 0, Tendsto (fun n => (bootstrapLaw (x n)).real {b |
      ε ≤ |Real.sqrt ((n : ℝ) + 1) *
        (h (sampleMean b, sampleVariance b) - h (sampleMean (x n), sampleVariance (x n)) -
          D (sampleMean b - sampleMean (x n), sampleVariance b - sampleVariance (x n)))|})
      atTop (𝓝 0) := by
  let r (n : ℕ) := Real.sqrt ((n : ℝ) + 1)
  let A n (b : Fin (n + 1) → ℝ) := r n * (sampleMean b - sampleMean (x n))
  let B n (b : Fin (n + 1) → ℝ) := r n *
    (sampleMean (fun i => (b i - μ) ^ 2) - sampleMean (fun i => (x n i - μ) ^ 2))
  let R n (b : Fin (n + 1) → ℝ) := r n * (sampleVariance b - sampleVariance (x n)) - B n b
  have hA n : MemLp (A n) 2 (bootstrapLaw (x n)) :=
    ((bootstrap_sampleMean_memLp (x n)).sub (memLp_const _)).const_mul _
  have hB n : MemLp (B n) 2 (bootstrapLaw (x n)) :=
    ((bootstrap_transformed_sampleMean_memLp (x n) (by fun_prop : Measurable (fun y : ℝ => (y - μ) ^ 2))).sub
      (memLp_const _)).const_mul _
  have hAM : Tendsto (fun n => ∫ b, ‖A n b‖ ^ 2 ∂bootstrapLaw (x n)) atTop (𝓝 v) := by
    have he n : (∫ b, ‖A n b‖ ^ 2 ∂bootstrapLaw (x n)) = empiricalVariance (x n) := by
      simpa only [A, r, Real.norm_eq_abs, sq_abs, Nat.cast_add, Nat.cast_one] using
        bootstrap_normalized_mean_error_secondMoment (x n)
    simp_rw [he]
    exact hv
  have hBM : Tendsto (fun n => ∫ b, ‖B n b‖ ^ 2 ∂bootstrapLaw (x n)) atTop (𝓝 w) := by
    have he n : (∫ b, ‖B n b‖ ^ 2 ∂bootstrapLaw (x n)) =
        empiricalVariance (fun i => (x n i - μ) ^ 2) := by
      simpa only [B, r, Real.norm_eq_abs, sq_abs, Nat.cast_add, Nat.cast_one] using
        bootstrap_normalized_transformed_mean_secondMoment (x n)
          (by fun_prop : Measurable (fun y : ℝ => (y - μ) ^ 2))
    simp_rw [he]
    exact hw
  have hm : Tendsto (fun n => sampleMean (x n)) atTop (𝓝 μ) :=
    (continuous_fst.tendsto (μ, v)).comp hxc
  have hR : RowProbabilityZero (fun n => bootstrapLaw (x n)) R := by
    simpa only [RowProbabilityZero, R, B, r, Real.norm_eq_abs] using
      bootstrap_sampleVariance_linear_remainder_probability x μ v w hm hv hw
  have ht := (rowTight_of_secondMoment_tendsto hA hAM).prodMk
    ((rowTight_of_secondMoment_tendsto hB hBM).add hR.rowTight)
  have hT : RowTight (fun n => bootstrapLaw (x n))
      (fun n b => r n • ((sampleMean b, sampleVariance b) -
        (sampleMean (x n), sampleVariance (x n)))) := by
    apply ht.congr
    apply Eventually.of_forall
    intro n b
    ext <;> simp [A, R]
  have hr : Tendsto r atTop atTop := Real.tendsto_sqrt_atTop.comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hh := row_strict_delta_remainder_of_tight hd hxc hr hT
  simpa only [RowProbabilityZero, r, smul_eq_mul, Real.norm_eq_abs, Prod.mk_sub_mk] using hh

/-- L8's conditional bootstrap CLT for a smooth function of mean and sample
variance. Strict differentiability supplies the moving-center expansion;
finite fourth moment supplies both leading coordinate limits. -/
theorem iid_bootstrap_smooth_moment_cdf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (h : C(ℝ × ℝ, ℝ)) (D : (ℝ × ℝ) →L[ℝ] ℝ)
    (hd : HasStrictFDerivAt h D (P[X 0], Var[X 0; P]))
    (τ : ℝ) (hτ : 0 < τ)
    (hvar : Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P] = τ ^ 2) :
    ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n =>
      cdf (bootstrapSmoothMomentErrorLaw h (fun i : Fin (n + 1) => X i ω) τ) t)
      atTop (𝓝 (cdf (gaussianReal 0 1) t)) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [iid_bootstrap_meanVariance_linear_conditions hXm hX hind hident,
    iid_bootstrap_meanVariance_influence_cdf hXm hX hind hident D τ hτ hvar] with ω hω hlin
  let x n : Fin (n + 1) → ℝ := fun i => X i ω
  let μ := P[X 0]
  let v := Var[X 0; P]
  let r (n : ℕ) := Real.sqrt ((n : ℝ) + 1)
  let ψ (y : ℝ) := D (y - μ, (y - μ) ^ 2 - v)
  let Y n (b : Fin (n + 1) → ℝ) := r n / τ *
    (sampleMean (fun i => ψ (b i)) - sampleMean (fun i => ψ (x n i)))
  let R₁ n (b : Fin (n + 1) → ℝ) := r n *
    (h (sampleMean b, sampleVariance b) - h (sampleMean (x n), sampleVariance (x n)) -
      D (sampleMean b - sampleMean (x n), sampleVariance b - sampleVariance (x n)))
  let R₂ n (b : Fin (n + 1) → ℝ) := D (0, 1) *
    (r n * (sampleVariance b - sampleVariance (x n)) -
      r n * (sampleMean (fun i => (b i - μ) ^ 2) - sampleMean (fun i => (x n i - μ) ^ 2)))
  have hδbase := bootstrap_smooth_moment_remainder_probability x μ v
    (Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P]) (h := h) (D := D)
  have hδc := hδbase hω.1
  have hδv := hδc hω.2.1
  have hδw := hδv hω.2.2.1
  have hR₁ := hδw hd
  have hR₂ := row_probability_const_mul_zero hω.2.2.2 (D (0, 1))
  have hR := row_probability_const_mul_zero (row_probability_add_zero hR₁ hR₂) (1 / τ)
  intro t
  have hh := dependent_rows_additive_error_cdf (fun n => bootstrapLaw (x n)) Y
    (fun n b => 1 / τ * (R₁ n b + R₂ n b)) (gaussianReal 0 1) hlin hR t
  apply hh.congr
  intro n
  rw [cdf_eq_real]
  unfold bootstrapSmoothMomentErrorLaw
  rw [map_measureReal_apply (by unfold smoothMomentStatistic sampleVariance sampleMean; fun_prop) measurableSet_Iic]
  congr 1
  ext b
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic]
  have he := bootstrap_meanVariance_influence_error (x n) b μ v (r n) D
  change Y n b + 1 / τ * (R₁ n b + R₂ n b) ≤ t ↔
    Real.sqrt (n + 1 : ℕ) / τ *
      (h (sampleMean b, sampleVariance b) - h (sampleMean (x n), sampleVariance (x n))) ≤ t
  simp only [Nat.cast_add, Nat.cast_one]
  change Y n b + 1 / τ * (R₁ n b + R₂ n b) ≤ t ↔
    r n / τ * (h (sampleMean b, sampleVariance b) - h (sampleMean (x n), sampleVariance (x n))) ≤ t
  have heq : Y n b + 1 / τ * (R₁ n b + R₂ n b) =
      r n / τ * (h (sampleMean b, sampleVariance b) - h (sampleMean (x n), sampleVariance (x n))) := by
    dsimp only [Y, R₁, R₂, ψ]
    rw [← he]
    ring
  rw [heq]

/-- Almost surely, the smooth-statistic bootstrap CDF approximation is uniform. -/
theorem iid_bootstrap_smooth_moment_cdf_uniform {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (h : C(ℝ × ℝ, ℝ)) (D : (ℝ × ℝ) →L[ℝ] ℝ)
    (hd : HasStrictFDerivAt h D (P[X 0], Var[X 0; P]))
    (τ : ℝ) (hτ : 0 < τ)
    (hvar : Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P] = τ ^ 2) :
    ∀ᵐ ω ∂P, TendstoUniformly
      (fun n => cdf (bootstrapSmoothMomentErrorLaw h (fun i : Fin (n + 1) => X i ω) τ))
      (cdf (gaussianReal 0 1)) atTop := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [iid_bootstrap_smooth_moment_cdf hXm hX hind hident h D hd τ hτ hvar] with ω hω
  exact cdf_tendstoUniformly_of_pointwise _ _ hω

/-- Every interior bootstrap quantile of the smooth statistic converges almost
surely to its corresponding Gaussian quantile. -/
theorem iid_bootstrap_smooth_moment_quantile_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (h : C(ℝ × ℝ, ℝ)) (D : (ℝ × ℝ) →L[ℝ] ℝ)
    (hd : HasStrictFDerivAt h D (P[X 0], Var[X 0; P]))
    (τ : ℝ) (hτ : 0 < τ)
    (hvar : Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P] = τ ^ 2)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, Tendsto (fun n => distributionQuantile
      (bootstrapSmoothMomentErrorLaw h (fun i : Fin (n + 1) => X i ω) τ) q)
      atTop (𝓝 (distributionQuantile (gaussianReal 0 1) q)) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [iid_bootstrap_smooth_moment_cdf hXm hX hind hident h D hd τ hτ hvar] with ω hω
  exact distributionQuantile_tendsto _ _ (gaussian_cdf_strictMono 0 1 (by norm_num)) hω hq

end LectureNotes
