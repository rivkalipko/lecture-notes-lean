import LectureNotes.BootstrapVarianceAsymptotics

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
attribute [local instance] bootstrapLaw_isProbabilityMeasure

/-- Addition preserves convergence to zero in varying-row probability. -/
theorem row_probability_add_zero {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {Y Z : ∀ n, Ω n → ℝ}
    (hY : ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ |Y n ω|}) atTop (𝓝 0))
    (hZ : ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ |Z n ω|}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ |Y n ω + Z n ω|}) atTop (𝓝 0) := by
  intro ε hε
  have hh := (hY (ε / 2) (by positivity)).add (hZ (ε / 2) (by positivity))
  simp only [zero_add] at hh
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hh
  intro n
  apply (measureReal_mono (μ := P n) (show {ω | ε ≤ |Y n ω + Z n ω|} ⊆
      {ω | ε / 2 ≤ |Y n ω|} ∪ {ω | ε / 2 ≤ |Z n ω|} from ?_)).trans
    (measureReal_union_le _ _)
  intro ω hω
  by_contra h
  have h₁ : |Y n ω| < ε / 2 := lt_of_not_ge (fun h₁ => h (Or.inl h₁))
  have h₂ : |Z n ω| < ε / 2 := lt_of_not_ge (fun h₂ => h (Or.inr h₂))
  have hb := abs_add_le (Y n ω) (Z n ω)
  change ε ≤ |Y n ω + Z n ω| at hω
  linarith

/-- Fixed scalar multiplication preserves convergence to zero in row probability. -/
theorem row_probability_const_mul_zero {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {Y : ∀ n, Ω n → ℝ}
    (hY : ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ |Y n ω|}) atTop (𝓝 0))
    (c : ℝ) :
    ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ |c * Y n ω|}) atTop (𝓝 0) := by
  have hh := row_probability_continuous_mapping_const (c := 0) (g := fun x : ℝ => c * x)
    (by fun_prop) (by simpa only [sub_zero] using hY)
  simpa only [mul_zero, sub_zero] using hh

/-- Exact second moment of a normalized transformed bootstrap-mean error. -/
theorem bootstrap_normalized_transformed_mean_secondMoment {n : ℕ} [NeZero n]
    (x : Fin n → ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    (∫ b, (Real.sqrt n * (sampleMean (fun i => g (b i)) -
      sampleMean (fun i => g (x i)))) ^ 2 ∂bootstrapLaw x) =
        empiricalVariance (fun i => g (x i)) := by
  simp_rw [mul_pow]
  rw [integral_const_mul, bootstrap_transformed_sampleMean_mse x hg,
    Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne n))

/-- The denominator correction contributes only small coefficients in the
variance linearization. This exact identity also covers one observation. -/
theorem bootstrap_sampleVariance_linear_remainder {n : ℕ}
    (x b : Fin (n + 1) → ℝ) (μ : ℝ) :
    Real.sqrt ((n : ℝ) + 1) * (sampleVariance b - sampleVariance x) -
      Real.sqrt ((n : ℝ) + 1) *
        (sampleMean (fun i => (b i - μ) ^ 2) - sampleMean (fun i => (x i - μ) ^ 2)) =
    (((n : ℝ) / (n + 1))⁻¹ - 1) *
      (Real.sqrt ((n : ℝ) + 1) *
        (sampleMean (fun i => (b i - μ) ^ 2) - sampleMean (fun i => (x i - μ) ^ 2))) +
    ((-2 * (sampleMean x - μ) / ((n : ℝ) / (n + 1))) *
      (Real.sqrt ((n : ℝ) + 1) * (sampleMean b - sampleMean x)) +
    (-1 / (((n : ℝ) / (n + 1)) * Real.sqrt ((n : ℝ) + 1))) *
      (Real.sqrt ((n : ℝ) + 1) * (sampleMean b - sampleMean x)) ^ 2) := by
  have he := bootstrap_empiricalVariance_linear_decomposition (Nat.succ_pos n) x b μ 1
  simp only [div_one, Nat.cast_succ] at he
  simp only [sampleVariance_eq_empiricalVariance_div, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  rw [← sub_div, ← mul_div_assoc, he]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Conditional linearization of the actual sample variance for deterministic
observed rows. Only second moments of the two transformed mean errors are
needed, allowing the squared-deviation variance to be zero. -/
theorem bootstrap_sampleVariance_linear_remainder_probability
    (x : ∀ n : ℕ, Fin (n + 1) → ℝ) (μ v w : ℝ)
    (hm : Tendsto (fun n => sampleMean (x n)) atTop (𝓝 μ))
    (hv : Tendsto (fun n => empiricalVariance (x n)) atTop (𝓝 v))
    (hw : Tendsto (fun n => empiricalVariance (fun i => (x n i - μ) ^ 2)) atTop (𝓝 w)) :
    ∀ ε > 0, Tendsto (fun n => (bootstrapLaw (x n)).real {b |
      ε ≤ |Real.sqrt ((n : ℝ) + 1) * (sampleVariance b - sampleVariance (x n)) -
        Real.sqrt ((n : ℝ) + 1) *
          (sampleMean (fun i => (b i - μ) ^ 2) - sampleMean (fun i => (x n i - μ) ^ 2))|})
      atTop (𝓝 0) := by
  let A n (b : Fin (n + 1) → ℝ) := Real.sqrt ((n : ℝ) + 1) * (sampleMean b - sampleMean (x n))
  let B n (b : Fin (n + 1) → ℝ) := Real.sqrt ((n : ℝ) + 1) *
    (sampleMean (fun i => (b i - μ) ^ 2) - sampleMean (fun i => (x n i - μ) ^ 2))
  have hA n : MemLp (A n) 2 (bootstrapLaw (x n)) :=
    ((bootstrap_sampleMean_memLp (x n)).sub (memLp_const _)).const_mul _
  have hB n : MemLp (B n) 2 (bootstrapLaw (x n)) :=
    ((bootstrap_transformed_sampleMean_memLp (x n) (by fun_prop : Measurable (fun y : ℝ => (y - μ) ^ 2))).sub
      (memLp_const _)).const_mul _
  have hAM : Tendsto (fun n => ∫ b, A n b ^ 2 ∂bootstrapLaw (x n)) atTop (𝓝 v) := by
    have he n : (∫ b, A n b ^ 2 ∂bootstrapLaw (x n)) = empiricalVariance (x n) := by
      simpa only [A, Nat.cast_add, Nat.cast_one] using bootstrap_normalized_mean_error_secondMoment (x n)
    simp_rw [he]
    exact hv
  have hBM : Tendsto (fun n => ∫ b, B n b ^ 2 ∂bootstrapLaw (x n)) atTop (𝓝 w) := by
    have he n : (∫ b, B n b ^ 2 ∂bootstrapLaw (x n)) =
        empiricalVariance (fun i => (x n i - μ) ^ 2) := by
      simpa only [B, Nat.cast_add, Nat.cast_one] using
        bootstrap_normalized_transformed_mean_secondMoment (x n)
          (by fun_prop : Measurable (fun y : ℝ => (y - μ) ^ 2))
    simp_rw [he]
    exact hw
  have hS : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := tendsto_natCast_div_add_atTop 1
  have hSi := hS.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hs : Tendsto (fun n : ℕ => (Real.sqrt ((n : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
  have ha : Tendsto (fun n => -2 * (sampleMean (x n) - μ) / ((n : ℝ) / (n + 1))) atTop (𝓝 0) := by
    simpa using! (((hm.sub_const μ).const_mul (-2)).div hS (by norm_num : (1 : ℝ) ≠ 0))
  have hb : Tendsto (fun n : ℕ => -1 / (((n : ℝ) / (n + 1)) * Real.sqrt ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    convert! (hSi.mul hs).neg using 1
    · funext n
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · simp
  have hc : Tendsto (fun n : ℕ => ((n : ℝ) / (n + 1))⁻¹ - 1) atTop (𝓝 0) := by
    simpa using hSi.sub_const 1
  have h₁ := row_small_polynomial_probability hB hBM hc (tendsto_const_nhds (x := (0 : ℝ)))
  simp only [zero_mul, add_zero] at h₁
  have h₂ := row_small_polynomial_probability hA hAM ha hb
  have hh := row_probability_add_zero h₁ h₂
  simpa only [bootstrap_sampleVariance_linear_remainder, A, B] using hh

/-- A scalar linear functional on a moment pair has its two coordinate coefficients. -/
theorem real_pair_clm_apply (D : (ℝ × ℝ) →L[ℝ] ℝ) (x y : ℝ) :
    D (x, y) = D (1, 0) * x + D (0, 1) * y := by
  have he : (x, y) = x • (1, 0) + y • (0, 1) := by ext <;> simp
  rw [he, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

/-- Averaging commutes with the derivative applied to a moment pair. -/
theorem sampleMean_pair_clm {n : ℕ} (D : (ℝ × ℝ) →L[ℝ] ℝ) (x y : Fin n → ℝ) :
    sampleMean (fun i => D (x i, y i)) = D (sampleMean x, sampleMean y) := by
  have he : (fun i => D (x i, y i)) = (fun i => D (1, 0) * x i + D (0, 1) * y i) :=
    funext (fun i => real_pair_clm_apply D (x i) (y i))
  rw [he, real_pair_clm_apply D (sampleMean x) (sampleMean y)]
  simp only [sampleMean, Fintype.card_fin, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Finite fourth moment gives finite second moment for every linear influence
of the mean and variance, including singular covariance configurations. -/
theorem meanVariance_influence_memLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : MemLp X 4 P) (μ v : ℝ) (D : (ℝ × ℝ) →L[ℝ] ℝ) :
    MemLp (fun ω => D (X ω - μ, (X ω - μ) ^ 2 - v)) 2 P := by
  have hX2 : MemLp X 2 P := hX.mono_exponent (by norm_num)
  have hZ2 : MemLp (fun ω => (X ω - μ) ^ 2) 2 P := by
    apply (memLp_two_iff_integrable_sq ((hX.aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2)).mpr
    simpa only [Pi.pow_apply, Pi.sub_apply, Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by norm_num,
      pow_mul, sq_abs] using (hX.sub (memLp_const μ)).integrable_norm_pow' (p := 4)
  apply MemLp.continuousLinearMap_comp (L := D)
  apply memLp_prod_iff.mpr
  exact ⟨hX2.sub (memLp_const μ), hZ2.sub (memLp_const v)⟩

/-- The linearized resampling statistic differs from the actual derivative
applied to the mean/variance error by just the variance-coordinate remainder. -/
theorem bootstrap_meanVariance_influence_error {n : ℕ}
    (x b : Fin (n + 1) → ℝ) (μ v r : ℝ) (D : (ℝ × ℝ) →L[ℝ] ℝ) :
    r * D (sampleMean b - sampleMean x, sampleVariance b - sampleVariance x) -
      r * (sampleMean (fun i => D (b i - μ, (b i - μ) ^ 2 - v)) -
        sampleMean (fun i => D (x i - μ, (x i - μ) ^ 2 - v))) =
    D (0, 1) * (r * (sampleVariance b - sampleVariance x) -
      r * (sampleMean (fun i => (b i - μ) ^ 2) - sampleMean (fun i => (x i - μ) ^ 2))) := by
  simp only [sampleMean_pair_clm, sampleMean_sub_const (Nat.succ_pos n)]
  rw [real_pair_clm_apply D (sampleMean b - sampleMean x) (sampleVariance b - sampleVariance x),
    real_pair_clm_apply D (sampleMean b - μ) _, real_pair_clm_apply D (sampleMean x - μ) _]
  ring

/-- The actual bootstrap influence CDF follows from the finite-second-moment
bootstrap mean theorem applied to the explicitly constructed influence. -/
theorem iid_bootstrap_meanVariance_influence_cdf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (D : (ℝ × ℝ) →L[ℝ] ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hvar : Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P] = τ ^ 2) :
    ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n =>
      (bootstrapLaw (fun i : Fin (n + 1) => X i ω)).real {b : Fin (n + 1) → ℝ |
        Real.sqrt ((n : ℝ) + 1) / τ *
          (sampleMean (fun i => D (b i - P[X 0], (b i - P[X 0]) ^ 2 - Var[X 0; P])) -
            sampleMean (fun i : Fin (n + 1) =>
              D (X i ω - P[X 0], (X i ω - P[X 0]) ^ 2 - Var[X 0; P]))) ≤ t})
      atTop (𝓝 (cdf (gaussianReal 0 1) t)) := by
  let g : ℝ → ℝ := fun x => D (x - P[X 0], (x - P[X 0]) ^ 2 - Var[X 0; P])
  have hg : Measurable g := by dsimp only [g]; fun_prop
  have h₂ := meanVariance_influence_memLp hX (P[X 0]) (Var[X 0; P]) D
  have hc := iid_bootstrap_mean_cdf (fun i => hg.comp (hXm i)) h₂
    (hind.comp (fun _ => g) (fun _ => hg)) (fun i => (hident i).comp hg) τ hτ hvar
  filter_upwards [hc] with ω hω
  intro t
  apply (hω t).congr
  intro n
  simpa only [g, Nat.cast_add, Nat.cast_one] using!
    bootstrap_transformed_mean_error_cdf (fun i : Fin (n + 1) => X i ω) g hg τ t

end LectureNotes
