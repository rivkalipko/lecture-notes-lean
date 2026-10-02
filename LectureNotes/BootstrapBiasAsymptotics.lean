import LectureNotes.BootstrapTaylorBias
import LectureNotes.FourthMomentSums
import LectureNotes.BootstrapConditionalCLT

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

/-- The sample mean's actual fourth moment supplies the expectation-level
second-order bias expansion under finite fourth moments. -/
theorem iid_transformed_mean_bias_limit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : MemLp (X 0) 4 P) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 3 g y| ≤ C) :
    Tendsto (fun n => (n + 1 : ℕ) *
      ((∫ ω, g (sampleMean (fun i : Fin (n + 1) => X i ω)) ∂P) - g (∫ ω, X 0 ω ∂P)))
      atTop (𝓝 (iteratedDeriv 2 g (∫ ω, X 0 ω ∂P) / 2 * Var[X 0; P])) := by
  let μ := ∫ ω, X 0 ω ∂P
  let v := Var[X 0; P]
  let κ := ∫ ω, (X 0 ω - μ) ^ 4 ∂P
  let Y n ω := sampleMean (fun i : Fin (n + 1) => X i ω)
  have hXi i : MemLp (X i) 4 P := (hident i).memLp_iff.mpr hX
  have hYi n : MemLp (Y n) 4 P := by
    unfold Y sampleMean
    exact (memLp_finsetSum (Finset.univ : Finset (Fin (n + 1)))
      (fun i _ => hXi i)).const_mul _
  have hm n : (∫ ω, Y n ω ∂P) = μ :=
    sampleMean_expectation (Nat.succ_pos n) (fun i => (hXi i).integrable (by norm_num))
      (fun i => (hident i).integral_eq)
  have hv n : Var[Y n; P] = v / (n + 1 : ℕ) :=
    sampleMean_variance (Nat.succ_pos n)
      (fun i => (hXi i).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4))
      (fun i j hij => hind.indepFun (Fin.val_ne_of_ne hij)) (fun i => (hident i).variance_eq)
  have hk n : (∫ ω, (Y n ω - μ) ^ 4 ∂P) =
      (κ + 3 * ((n + 1 : ℕ) - 1 : ℝ) * v ^ 2) / (n + 1 : ℕ) ^ 3 := by
    apply sampleMean_fourth_central_moment (Nat.succ_pos n) (fun i => hXi i)
      (hind.precomp Fin.val_injective)
      (fun i => (hident i).integral_eq) (fun i => (hident i).variance_eq)
    intro i
    exact ((hident i).comp (by fun_prop : Measurable (fun y : ℝ => (y - μ) ^ 4))).integral_eq
  have hN : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hiN := tendsto_inv_atTop_zero.comp hN
  have h2 : Tendsto (fun n => (Real.sqrt (n + 1 : ℕ)) ^ 2 * Var[Y n; P]) atTop (𝓝 v) := by
    have he n : (Real.sqrt (n + 1 : ℕ)) ^ 2 * Var[Y n; P] = v := by
      rw [Real.sq_sqrt (by positivity), hv]
      field_simp
    simp only [he]
    exact tendsto_const_nhds
  have h4 : Tendsto (fun n => (Real.sqrt (n + 1 : ℕ)) ^ 4 *
      (∫ ω, (Y n ω - μ) ^ 4 ∂P)) atTop (𝓝 (3 * v ^ 2)) := by
    have hh := (hiN.const_mul κ).add (((tendsto_const_nhds (x := (1 : ℝ))).sub hiN).const_mul (3 * v ^ 2))
    simp only [mul_zero, sub_zero, mul_one, zero_add] at hh
    convert! hh using 1
    ext n
    rw [hk]
    simp only [Function.comp_def]
    rw [show (Real.sqrt (n + 1 : ℕ)) ^ 4 = ((n + 1 : ℕ) : ℝ) ^ 2 from by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]]
    field_simp <;> ring
  have hh := second_order_bias_limit hYi hm hg hC
    (fun n => Real.sqrt_pos.mpr (by positivity)) (Real.tendsto_sqrt_atTop.comp hN) h2 h4
  have hs (n : ℕ) : (Real.sqrt (n + 1 : ℕ)) ^ 2 = (n + 1 : ℕ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  simpa only [hs, Y, μ, v] using! hh

/-- Exact fourth central moment under actual empirical product resampling. -/
theorem bootstrap_sampleMean_fourth_central_moment {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    (∫ b, (sampleMean b - sampleMean x) ^ 4 ∂bootstrapLaw x) =
      (sampleMean (fun i => (x i - sampleMean x) ^ 4) +
        3 * ((n : ℝ) - 1) * empiricalVariance x ^ 2) / (n : ℝ) ^ 3 := by
  letI := bootstrapLaw_isProbabilityMeasure x
  have hL i : HasLaw (fun b : Fin n → ℝ => b i) (empiricalLaw x) (bootstrapLaw x) :=
    (measurePreserving_eval (fun _ : Fin n => empiricalLaw x) i).hasLaw
  apply sampleMean_fourth_central_moment (Nat.pos_of_ne_zero (NeZero.ne n))
    (fun i => ((hL i).identDistrib HasLaw.id).memLp_iff.mpr (empiricalLaw_memLp x 4))
    (iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable))
    (fun i => by rw [(hL i).integral_eq, empiricalLaw_mean])
    (fun i => by rw [(hL i).variance_eq, empiricalLaw_variance])
  intro i
  have he : (∫ b, (b i - sampleMean x) ^ 4 ∂bootstrapLaw x) =
      ∫ y, (y - sampleMean x) ^ 4 ∂empiricalLaw x := by
    simpa only [Function.comp_def] using! (hL i).integral_comp (by fun_prop : AEStronglyMeasurable
      (fun y : ℝ => (y - sampleMean x) ^ 4) (empiricalLaw x))
  rw [he]
  rw [empiricalLaw_integral x (by fun_prop)]
  simp only [sampleMean, Fintype.card_fin, div_eq_mul_inv, mul_comm]

/-- A fourth central sample moment is bounded by raw fourth moments and the
fourth power of its center. -/
theorem sample_fourth_central_le {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    sampleMean (fun i => (x i - sampleMean x) ^ 4) ≤
      8 * (sampleMean (fun i => x i ^ 4) + sampleMean x ^ 4) := by
  have hp (a b : ℝ) : (a - b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
    have hh : 0 ≤ (a + b) ^ 2 * (2 * a ^ 2 + 2 * b ^ 2 + 5 * (a - b) ^ 2) := by positivity
    nlinarith
  have hh := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin n) _ => hp (x i) (sampleMean x)))
    (inv_nonneg.mpr (Nat.cast_nonneg n) : 0 ≤ (n : ℝ)⁻¹)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  simpa only [sampleMean, Fintype.card_fin] using! (show
    (n : ℝ)⁻¹ * ∑ i, (x i - sampleMean x) ^ 4 ≤
      8 * ((n : ℝ)⁻¹ * ∑ i, x i ^ 4 + sampleMean x ^ 4) from by
        convert! hh using 1
        field_simp [Nat.cast_ne_zero.mpr (NeZero.ne n)] <;> ring)

/-- Convergent raw fourth moments and means make the central fourth moment
negligible after division by sample size. -/
theorem sample_fourth_central_div_size_tendsto_zero
    (x : ∀ n : ℕ, Fin (n + 1) → ℝ) {μ k : ℝ}
    (hm : Tendsto (fun n => sampleMean (x n)) atTop (𝓝 μ))
    (hk : Tendsto (fun n => sampleMean (fun i => x n i ^ 4)) atTop (𝓝 k)) :
    Tendsto (fun n => sampleMean (fun i => (x n i - sampleMean (x n)) ^ 4) / (n + 1 : ℕ))
      atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hb := ((hk.add (hm.pow 4)).const_mul 8).mul hi
  simp only [mul_zero] at hb
  apply squeeze_zero (fun n => by unfold sampleMean; positivity) _ hb
  intro n
  have hh := mul_le_mul_of_nonneg_right (sample_fourth_central_le (x n))
    (inv_nonneg.mpr (Nat.cast_nonneg (n + 1)))
  simpa only [div_eq_mul_inv] using hh

/-- The conditional normalized fourth moment is derived from the actual
empirical product law and convergent observed moments. -/
theorem bootstrap_mean_fourth_moment_limit
    (x : ∀ n : ℕ, Fin (n + 1) → ℝ) {μ v k : ℝ}
    (hm : Tendsto (fun n => sampleMean (x n)) atTop (𝓝 μ))
    (hv : Tendsto (fun n => empiricalVariance (x n)) atTop (𝓝 v))
    (hk : Tendsto (fun n => sampleMean (fun i => x n i ^ 4)) atTop (𝓝 k)) :
    Tendsto (fun n => (Real.sqrt (n + 1 : ℕ)) ^ 4 *
      (∫ b, (sampleMean b - sampleMean (x n)) ^ 4 ∂bootstrapLaw (x n)))
      atTop (𝓝 (3 * v ^ 2)) := by
  have hc := sample_fourth_central_div_size_tendsto_zero x hm hk
  have hi : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hh := hc.add ((((tendsto_const_nhds (x := (1 : ℝ))).sub hi).mul (hv.pow 2)).const_mul 3)
  simp only [sub_zero, one_mul, zero_add] at hh
  convert! hh using 1
  ext n
  rw [bootstrap_sampleMean_fourth_central_moment]
  rw [show (Real.sqrt (n + 1 : ℕ)) ^ 4 = ((n + 1 : ℕ) : ℝ) ^ 2 from by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]]
  field_simp <;> ring

/-- Convergence of observed means, variances and raw fourth moments derives
the exact conditional bootstrap bias expansion. -/
theorem bootstrapBias_limit_of_moments
    (x : ∀ n : ℕ, Fin (n + 1) → ℝ) {μ v k : ℝ}
    (hm : Tendsto (fun n => sampleMean (x n)) atTop (𝓝 μ))
    (hv : Tendsto (fun n => empiricalVariance (x n)) atTop (𝓝 v))
    (hk : Tendsto (fun n => sampleMean (fun i => x n i ^ 4)) atTop (𝓝 k))
    {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 3 g y| ≤ C) :
    Tendsto (fun n => (n + 1 : ℕ) * bootstrapBias g (x n))
      atTop (𝓝 (iteratedDeriv 2 g μ / 2 * v)) := by
  letI (n : ℕ) : IsProbabilityMeasure (bootstrapLaw (x n)) := bootstrapLaw_isProbabilityMeasure _
  have hY n : MemLp (fun b : Fin (n + 1) → ℝ => sampleMean b - sampleMean (x n)) 4
      (bootstrapLaw (x n)) := (bootstrap_sampleMean_memLp_any (x n) 4).sub (memLp_const _)
  have h2 : Tendsto (fun n => (Real.sqrt (n + 1 : ℕ)) ^ 2 *
      (∫ b, (sampleMean b - sampleMean (x n)) ^ 2 ∂bootstrapLaw (x n))) atTop (𝓝 v) := by
    convert! hv using 1
    ext n
    rw [Real.sq_sqrt (by positivity), bootstrap_sampleMean_mse]
    field_simp
  have h4 := bootstrap_mean_fourth_moment_limit x hm hv hk
  have hN : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h3 := scaled_absolute_third_moment_tendsto_zero hY
    (fun n => Real.sqrt_pos.mpr (by positivity)) (Real.tendsto_sqrt_atTop.comp hN) h2 h4
  have hs (n : ℕ) : (Real.sqrt (n + 1 : ℕ)) ^ 2 = (n + 1 : ℕ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  simp only [hs] at h3
  have hR : Tendsto (fun n => |(n + 1 : ℕ) * bootstrapBias g (x n) -
      iteratedDeriv 2 g (sampleMean (x n)) / 2 * empiricalVariance (x n)|) atTop (𝓝 0) := by
    have hu : Tendsto (fun n => C / 6 * ((n + 1 : ℕ) *
        (∫ b, |sampleMean b - sampleMean (x n)| ^ 3 ∂bootstrapLaw (x n)))) atTop (𝓝 0) := by
      simpa using h3.const_mul (C / 6)
    apply squeeze_zero (fun n => abs_nonneg _) _ hu
    intro n
    have he : (n + 1 : ℕ) * bootstrapBias g (x n) -
        iteratedDeriv 2 g (sampleMean (x n)) / 2 * empiricalVariance (x n) =
        (n + 1 : ℕ) * (bootstrapBias g (x n) -
          iteratedDeriv 2 g (sampleMean (x n)) / 2 * empiricalVariance (x n) / (n + 1 : ℕ)) := by
      field_simp <;> ring
    rw [he, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℕ))]
    have hh := mul_le_mul_of_nonneg_left (bootstrapBias_second_order_bound (x n) hg hC)
      (Nat.cast_nonneg (n + 1))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hh
  have hR' : Tendsto (fun n => (n + 1 : ℕ) * bootstrapBias g (x n) -
      iteratedDeriv 2 g (sampleMean (x n)) / 2 * empiricalVariance (x n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using hR
  have hd := ((hg.continuous_iteratedDeriv 2 (by norm_num)).tendsto μ).comp hm
  have hh := hR'.add ((hd.div_const 2).mul hv)
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using! hh

/-- IID finite fourth moments supply every observed-moment condition in the
conditional expansion; the conclusion holds almost surely in the data. -/
theorem iid_bootstrapBias_limit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 3 g y| ≤ C) :
    ∀ᵐ ω ∂P, Tendsto (fun n => (n + 1 : ℕ) *
      bootstrapBias g (fun i : Fin (n + 1) => X i ω))
      atTop (𝓝 (iteratedDeriv 2 g (∫ ω, X 0 ω ∂P) / 2 * Var[X 0; P])) := by
  have hm := iid_sampleMean_succ_ae (hX.integrable (by norm_num)) hind hident
  have hv := empiricalVariance_strong_consistency hXm
    (hX.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)) hind hident
  have hk := iid_sampleMean_succ_ae (memLp_four_integrable_pow hX (by norm_num : 4 ≤ 4))
    (hind.comp (fun _ (y : ℝ) => y ^ 4) (fun _ => by fun_prop))
    (fun i => (hident i).comp (by fun_prop : Measurable (fun y : ℝ => y ^ 4)))
  filter_upwards [hm, hv, hk] with ω hmω hvω hkω
  have hh := bootstrapBias_limit_of_moments (fun n i => X i ω) hmω
    (hvω.comp (tendsto_add_atTop_nat 1)) hkω hg hC
  exact hh

/-- The actual exact-bootstrap bias estimates the actual sampling bias to
an error smaller than 1/n, almost surely in the observations. -/
theorem iid_bootstrapBias_minus_samplingBias {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 3 g y| ≤ C) :
    ∀ᵐ ω ∂P, Tendsto (fun n => (n + 1 : ℕ) *
      (bootstrapBias g (fun i : Fin (n + 1) => X i ω) -
        ((∫ ω', g (sampleMean (fun i : Fin (n + 1) => X i ω')) ∂P) - g (∫ ω', X 0 ω' ∂P))))
      atTop (𝓝 0) := by
  have hS := iid_transformed_mean_bias_limit hX hind hident hg hC
  filter_upwards [iid_bootstrapBias_limit hXm hX hind hident hg hC] with ω hω
  have hh := hω.sub hS
  simpa only [sub_self, mul_sub] using hh

end LectureNotes
