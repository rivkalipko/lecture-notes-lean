import LectureNotes.BootstrapBiasAsymptotics
import LectureNotes.MonteCarloBiasJoint

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

/-- A bounded second derivative gives a global quadratic first-order
Taylor remainder. -/
theorem first_order_remainder_bound {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    {C : ℝ} (hC : ∀ y, |iteratedDeriv 2 g y| ≤ C) (μ y : ℝ) :
    |g y - g μ - deriv g μ * (y - μ)| ≤ C / 2 * (y - μ) ^ 2 := by
  by_cases hy : μ = y
  · subst y
    simp
  have hp : taylorWithinEval g 1 (uIcc μ y) μ y = g μ + deriv g μ * (y - μ) := by
    rw [taylorWithinEval_succ g 0, taylor_within_zero_eval]
    norm_num only [Nat.reduceAdd, Nat.factorial_zero, Nat.cast_zero, zero_add, one_mul,
      mul_one, inv_one, pow_one, smul_eq_mul]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hy)
      ((hg.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt) left_mem_uIcc, iteratedDeriv_one]
    ring
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hy hg.contDiffOn
  rw [hp] at he
  have he' : g y - g μ - deriv g μ * (y - μ) = iteratedDeriv 2 g z * (y - μ) ^ 2 / 2 := by
    norm_num at he
    linarith
  rw [he', abs_div, abs_mul, abs_pow, sq_abs]
  norm_num
  have hh := mul_le_mul_of_nonneg_right (hC z) (sq_nonneg (y - μ))
  nlinarith

/-- A bounded second derivative gives an integrable transform and a genuine
expectation-level bound on the first-order remainder. -/
theorem first_order_expectation_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : MemLp Y 2 P) {μ : ℝ} (hm : (∫ ω, Y ω ∂P) = μ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 2 g y| ≤ C) :
    Integrable (fun ω => g (Y ω)) P ∧
      |(∫ ω, g (Y ω) ∂P) - g μ| ≤ C / 2 * Var[Y; P] := by
  have hi := hY.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hZ : MemLp (fun ω => Y ω - μ) 2 P := hY.sub (memLp_const μ)
  have hiZ := hZ.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  let R ω := g (Y ω) - g μ - deriv g μ * (Y ω - μ)
  have hRm : AEStronglyMeasurable R P :=
    ((hg.continuous.comp_aestronglyMeasurable hY.aestronglyMeasurable).sub
      aestronglyMeasurable_const).sub (hZ.aestronglyMeasurable.const_mul _)
  have hdom : Integrable (fun ω => C / 2 * (Y ω - μ) ^ 2) P := hZ.integrable_sq.const_mul _
  have hbound : ∀ ω, ‖R ω‖ ≤ C / 2 * (Y ω - μ) ^ 2 :=
    fun ω => first_order_remainder_bound hg hC μ (Y ω)
  have hR : Integrable R P := hdom.mono' hRm (ae_of_all _ hbound)
  have hgI : Integrable (fun ω => g (Y ω)) P := by
    convert! (hR.add (integrable_const (g μ))).add (hiZ.const_mul (deriv g μ)) using 1
    ext ω
    dsimp [R]
    ring
  refine ⟨hgI, ?_⟩
  have hZmean : (∫ ω, Y ω - μ ∂P) = 0 := by
    rw [integral_sub hi (integrable_const μ), hm]
    simp
  have hZvar : (∫ ω, (Y ω - μ) ^ 2 ∂P) = Var[Y; P] := by
    rw [variance_eq_integral hY.aemeasurable, hm]
  have he : (∫ ω, R ω ∂P) = (∫ ω, g (Y ω) ∂P) - g μ := by
    have hs : Integrable (fun ω => g (Y ω) - g μ) P := hgI.sub (integrable_const _)
    dsimp [R]
    rw [integral_sub hs (hiZ.const_mul _), integral_sub hgI (integrable_const _),
      integral_const_mul, hZmean]
    simp
  have hb := norm_integral_le_of_norm_le hdom (ae_of_all _ hbound)
  rw [he, integral_const_mul, hZvar] at hb
  exact hb

/-- Exact bootstrap bias is bounded by curvature times the conditional
mean variance. -/
theorem bootstrapBias_abs_le {n : ℕ} [NeZero n] (x : Fin n → ℝ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 2 g y| ≤ C) :
    |bootstrapBias g x| ≤ C / 2 * empiricalVariance x / n := by
  letI := bootstrapLaw_isProbabilityMeasure x
  have h := (first_order_expectation_bound (bootstrap_sampleMean_memLp x)
    (bootstrap_sampleMean_expectation x) hg hC).2
  rw [bootstrap_sampleMean_variance] at h
  simpa only [bootstrapBias, mul_div_assoc] using! h

/-- Bounded data bound the empirical variance uniformly, with its actual
n-denominator normalization. -/
theorem empiricalVariance_le_of_abs_le {n : ℕ} [NeZero n] (x : Fin n → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hx : ∀ i, |x i| ≤ M) : empiricalVariance x ≤ M ^ 2 := by
  rw [empiricalVariance_eq_secondMoment_sub_sq]
  apply (sub_le_self _ (sq_nonneg _)).trans
  have hh := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin n) _ =>
      show x i ^ 2 ≤ M ^ 2 from by nlinarith [hx i, sq_abs (x i), abs_nonneg (x i)]))
    (inv_nonneg.mpr (Nat.cast_nonneg n) : 0 ≤ (n : ℝ)⁻¹)
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simpa only [sampleMean, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hnR, one_mul] using hh

/-- Uniform boundedness of the n-scaled conditional bias supplies domination
for the expectation of the corrected estimator. -/
theorem bootstrapBias_scaled_abs_le_of_bounded {n : ℕ} [NeZero n] (x : Fin n → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hx : ∀ i, |x i| ≤ M)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 2 g y| ≤ C) :
    |(n : ℝ) * bootstrapBias g x| ≤ C / 2 * M ^ 2 := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  rw [abs_mul, abs_of_pos hn]
  have hh := mul_le_mul_of_nonneg_left (bootstrapBias_abs_le x hg hC) hn.le
  have he : (n : ℝ) * (C / 2 * empiricalVariance x / n) = C / 2 * empiricalVariance x := by
    field_simp
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (empiricalVariance_le_of_abs_le x hM hx) (by positivity))

/-- For bounded IID observations and globally bounded second and third
derivatives, the actual expected bias of the exact bootstrap-corrected
estimator is smaller than 1/n. Domination is proved, not inferred from
almost-sure convergence of the estimated bias. -/
theorem iid_bootstrapBiasCorrected_bias_limit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ ω ∂P, ∀ i, |X i ω| ≤ M)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) {C₂ C₃ : ℝ}
    (hC₂ : ∀ y, |iteratedDeriv 2 g y| ≤ C₂)
    (hC₃ : ∀ y, |iteratedDeriv 3 g y| ≤ C₃) :
    Tendsto (fun n => (n + 1 : ℕ) *
      ((∫ ω, bootstrapBiasCorrected g (fun i : Fin (n + 1) => X i ω) ∂P) -
        g (∫ ω, X 0 ω ∂P))) atTop (𝓝 0) := by
  have hX : MemLp (X 0) 4 P := by
    apply MemLp.of_bound (hXm 0).aestronglyMeasurable M
    filter_upwards [hbound] with ω hω
    exact hω 0
  let K := C₂ / 2 * M ^ 2
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by norm_num)
  have hBmeas n : Measurable (fun ω => bootstrapBias g (fun i : Fin (n + 1) => X i ω)) :=
    (measurable_bootstrapBias hg.continuous.measurable).comp
      (measurable_pi_lambda _ (fun i => hXm i))
  have hBbound n : ∀ᵐ ω ∂P, |(n + 1 : ℕ) * bootstrapBias g (fun i : Fin (n + 1) => X i ω)| ≤ K := by
    filter_upwards [hbound] with ω hω
    exact bootstrapBias_scaled_abs_le_of_bounded _ hM (fun i => hω i) hg2 hC₂
  have hBI n : Integrable (fun ω => bootstrapBias g (fun i : Fin (n + 1) => X i ω)) P := by
    apply (integrable_const K).mono' (hBmeas n).aestronglyMeasurable
    filter_upwards [hBbound n] with ω hω
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (n + 1))] at hω
    change |bootstrapBias g (fun i : Fin (n + 1) => X i ω)| ≤ K
    have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
    nlinarith [abs_nonneg (bootstrapBias g (fun i : Fin (n + 1) => X i ω))]
  have hc := tendsto_integral_of_dominated_convergence (μ := P) (fun _ => K)
    (fun n => ((hBmeas n).const_mul (n + 1 : ℕ)).aestronglyMeasurable)
    (integrable_const K)
    (fun n => by simpa only [Real.norm_eq_abs] using hBbound n)
    (iid_bootstrapBias_limit hXm hX hind hident hg hC₃)
  simp only [integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul] at hc
  have hs := iid_transformed_mean_bias_limit hX hind hident hg hC₃
  have hgI n : Integrable (fun ω => g (sampleMean (fun i : Fin (n + 1) => X i ω))) P := by
    have hM2 := sampleMean_memLp (fun i : Fin (n + 1) =>
      ((hident i).memLp_iff.mpr hX).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4))
    exact (first_order_expectation_bound hM2 rfl hg2 hC₂).1
  have he n : (n + 1 : ℕ) *
      ((∫ ω, bootstrapBiasCorrected g (fun i : Fin (n + 1) => X i ω) ∂P) - g (∫ ω, X 0 ω ∂P)) =
      (n + 1 : ℕ) * ((∫ ω, g (sampleMean (fun i : Fin (n + 1) => X i ω)) ∂P) - g (∫ ω, X 0 ω ∂P)) -
      (n + 1 : ℕ) * (∫ ω, bootstrapBias g (fun i : Fin (n + 1) => X i ω) ∂P) := by
    simp only [bootstrapBiasCorrected]
    rw [integral_sub (hgI n) (hBI n)]
    ring
  have hh := hs.sub hc
  simpa only [he, sub_self] using! hh

end LectureNotes
