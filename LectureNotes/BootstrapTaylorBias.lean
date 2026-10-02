import LectureNotes.BootstrapBias
import Mathlib.Analysis.Calculus.Taylor

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

/-- A genuine second-order Taylor bound from a globally bounded third derivative. -/
theorem second_order_remainder_bound {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g)
    {C : ℝ} (hC : ∀ y, |iteratedDeriv 3 g y| ≤ C) (μ y : ℝ) :
    |g y - g μ - deriv g μ * (y - μ) - iteratedDeriv 2 g μ / 2 * (y - μ) ^ 2| ≤
      C / 6 * |y - μ| ^ 3 := by
  by_cases hy : μ = y
  · subst y
    simp
  have hu := uniqueDiffOn_uIcc hy
  have h2 := (hg.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).contDiffAt (x := μ)
  have h1 := (hg.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).contDiffAt (x := μ)
  have hp : taylorWithinEval g 2 (uIcc μ y) μ y =
      g μ + deriv g μ * (y - μ) + iteratedDeriv 2 g μ / 2 * (y - μ) ^ 2 := by
    rw [taylorWithinEval_succ g 1, taylorWithinEval_succ g 0, taylor_within_zero_eval]
    norm_num only [Nat.reduceAdd, Nat.factorial_zero, Nat.factorial_one, Nat.cast_zero,
      Nat.cast_one, zero_add, one_mul, mul_one, inv_one, pow_one, smul_eq_mul]
    rw [iteratedDerivWithin_eq_iteratedDeriv hu h1 left_mem_uIcc,
      iteratedDerivWithin_eq_iteratedDeriv hu h2 left_mem_uIcc, iteratedDeriv_one]
    norm_num
    ring
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) hy hg.contDiffOn
  rw [hp] at he
  have he' : g y - g μ - deriv g μ * (y - μ) - iteratedDeriv 2 g μ / 2 * (y - μ) ^ 2 =
      iteratedDeriv 3 g z * (y - μ) ^ 3 / 6 := by
    norm_num at he
    linarith
  rw [he', abs_div, abs_mul, abs_pow]
  norm_num
  have h := mul_le_mul_of_nonneg_right (hC z) (pow_nonneg (abs_nonneg (y - μ)) 3)
  nlinarith

/-- Finite absolute third moment turns the actual Taylor bound into an
expectation bound. No probabilistic remainder is moved through expectation. -/
theorem second_order_expectation_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : MemLp Y 3 P) {μ : ℝ} (hm : (∫ ω, Y ω ∂P) = μ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 3 g y| ≤ C) :
    Integrable (fun ω => g (Y ω)) P ∧
      |(∫ ω, g (Y ω) ∂P) - g μ - iteratedDeriv 2 g μ / 2 * Var[Y; P]| ≤
        C / 6 * (∫ ω, |Y ω - μ| ^ 3 ∂P) := by
  have hY2 : MemLp Y 2 P := hY.mono_exponent (by norm_num)
  have hi := hY2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hZ2 : MemLp (fun ω => Y ω - μ) 2 P := hY2.sub (memLp_const μ)
  have hiZ := hZ2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h3 : Integrable (fun ω => |Y ω - μ| ^ 3) P := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      (hY.sub (memLp_const μ)).integrable_norm_pow' (p := 3)
  let R : Ω → ℝ := fun ω => g (Y ω) - g μ - deriv g μ * (Y ω - μ) -
    iteratedDeriv 2 g μ / 2 * (Y ω - μ) ^ 2
  have hRm : AEStronglyMeasurable R P := by
    exact (((hg.continuous.comp_aestronglyMeasurable hY.aestronglyMeasurable).sub
      aestronglyMeasurable_const).sub (hZ2.aestronglyMeasurable.const_mul _)).sub
      ((hZ2.aestronglyMeasurable.pow 2).const_mul _)
  have hdom : Integrable (fun ω => C / 6 * |Y ω - μ| ^ 3) P := h3.const_mul _
  have hbound : ∀ ω, ‖R ω‖ ≤ C / 6 * |Y ω - μ| ^ 3 := by
    intro ω
    exact second_order_remainder_bound hg hC μ (Y ω)
  have hR : Integrable R P := hdom.mono' hRm (ae_of_all _ hbound)
  have hgI : Integrable (fun ω => g (Y ω)) P := by
    convert! ((hR.add (integrable_const (g μ))).add (hiZ.const_mul (deriv g μ))).add
      (hZ2.integrable_sq.const_mul (iteratedDeriv 2 g μ / 2)) using 1
    ext ω
    dsimp [R]
    ring
  refine ⟨hgI, ?_⟩
  have hZmean : (∫ ω, Y ω - μ ∂P) = 0 := by
    rw [integral_sub hi (integrable_const μ), hm]
    simp
  have hZvar : (∫ ω, (Y ω - μ) ^ 2 ∂P) = Var[Y; P] := by
    rw [variance_eq_integral hY.aestronglyMeasurable.aemeasurable, hm]
  have he : (∫ ω, R ω ∂P) = (∫ ω, g (Y ω) ∂P) - g μ -
      iteratedDeriv 2 g μ / 2 * Var[Y; P] := by
    dsimp [R]
    have hs1 : Integrable (fun ω => g (Y ω) - g μ) P := hgI.sub (integrable_const _)
    have hs2 : Integrable (fun ω => g (Y ω) - g μ - deriv g μ * (Y ω - μ)) P :=
      hs1.sub (hiZ.const_mul _)
    rw [integral_sub hs2 (hZ2.integrable_sq.const_mul _),
      integral_sub hs1 (hiZ.const_mul _),
      integral_sub hgI (integrable_const _), integral_const_mul, integral_const_mul,
      hZmean, hZvar]
    simp
  have hb := norm_integral_le_of_norm_le hdom (ae_of_all _ hbound)
  rw [he, integral_const_mul] at hb
  exact hb

/-- Bootstrap sample means have every finite moment, because resampling has
finite empirical support. -/
theorem bootstrap_sampleMean_memLp_any {n : ℕ} [NeZero n]
    (x : Fin n → ℝ) (p : ℝ≥0∞) : MemLp (sampleMean : (Fin n → ℝ) → ℝ) p (bootstrapLaw x) := by
  have hX (i : Fin n) : MemLp (fun b : Fin n → ℝ => b i) p (bootstrapLaw x) := by
    have hL : HasLaw (fun b : Fin n → ℝ => b i) (empiricalLaw x) (bootstrapLaw x) :=
      (measurePreserving_eval (fun _ : Fin n => empiricalLaw x) i).hasLaw
    exact ((hL.identDistrib HasLaw.id).memLp_iff).mpr (empiricalLaw_memLp x p)
  unfold sampleMean
  exact (memLp_finsetSum _ (fun i _ => hX i)).const_mul _

/-- The exact conditional bootstrap bias has a second-order expansion with
an explicitly controlled expected remainder. -/
theorem bootstrapBias_second_order_bound {n : ℕ} [NeZero n] (x : Fin n → ℝ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 3 g y| ≤ C) :
    |bootstrapBias g x - iteratedDeriv 2 g (sampleMean x) / 2 * empiricalVariance x / n| ≤
      C / 6 * (∫ b, |sampleMean b - sampleMean x| ^ 3 ∂bootstrapLaw x) := by
  letI := bootstrapLaw_isProbabilityMeasure x
  have h := (second_order_expectation_bound (bootstrap_sampleMean_memLp_any x 3)
    (bootstrap_sampleMean_expectation x) hg hC).2
  rw [bootstrap_sampleMean_variance] at h
  simpa only [bootstrapBias, mul_div_assoc] using! h

/-- Young's inequality bounds the absolute third moment using the second
and fourth moments, without a fractional-power integrability argument. -/
theorem absolute_third_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : MemLp Y 4 P)
    {r : ℝ} (hr : 0 < r) :
    (∫ ω, |Y ω| ^ 3 ∂P) ≤
      ((∫ ω, Y ω ^ 2 ∂P) + r ^ 2 * (∫ ω, Y ω ^ 4 ∂P)) / (2 * r) := by
  have h2 := (hY.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).integrable_sq
  have h3 : Integrable (fun ω => |Y ω| ^ 3) P := by
    simpa only [Real.norm_eq_abs] using
      (hY.mono_exponent (by norm_num : (3 : ℝ≥0∞) ≤ 4)).integrable_norm_pow' (p := 3)
  have h4 : Integrable (fun ω => Y ω ^ 4) P := by
    simpa only [Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs] using
      hY.integrable_norm_pow' (p := 4)
  have hb : ∀ ω, 2 * r * |Y ω| ^ 3 ≤ Y ω ^ 2 + r ^ 2 * Y ω ^ 4 := by
    intro ω
    have hh := sq_nonneg (r * Y ω ^ 2 - |Y ω|)
    have ha := sq_abs (Y ω)
    have he : |Y ω| ^ 3 = |Y ω| * Y ω ^ 2 := by
      rw [← sq_abs]
      ring
    rw [he]
    nlinarith [sq_nonneg (Y ω)]
  have hi : Integrable (fun ω => Y ω ^ 2 + r ^ 2 * Y ω ^ 4) P := h2.add (h4.const_mul _)
  have hh := integral_mono (h3.const_mul (2 * r)) hi hb
  rw [integral_const_mul, integral_add h2 (h4.const_mul _), integral_const_mul] at hh
  exact (le_div_iff₀ (by positivity : 0 < 2 * r)).mpr (by simpa only [mul_comm] using hh)

/-- Bounded normalized fourth moments yield the L1 Taylor remainder rate.
The row sample spaces may vary, so the lemma also applies conditionally to
bootstrap resamples. -/
theorem scaled_absolute_third_moment_tendsto_zero {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {Y : ∀ n, Ω n → ℝ}
    (hY : ∀ n, MemLp (Y n) 4 (P n)) {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto r atTop atTop) {v k : ℝ}
    (h2 : Tendsto (fun n => r n ^ 2 * (∫ ω, Y n ω ^ 2 ∂P n)) atTop (𝓝 v))
    (h4 : Tendsto (fun n => r n ^ 4 * (∫ ω, Y n ω ^ 4 ∂P n)) atTop (𝓝 k)) :
    Tendsto (fun n => r n ^ 2 * (∫ ω, |Y n ω| ^ 3 ∂P n)) atTop (𝓝 0) := by
  have hb : Tendsto (fun n =>
      (r n ^ 2 * (∫ ω, Y n ω ^ 2 ∂P n) + r n ^ 4 * (∫ ω, Y n ω ^ 4 ∂P n)) *
        (r n)⁻¹ / 2) atTop (𝓝 0) := by
    simpa using ((h2.add h4).mul (tendsto_inv_atTop_zero.comp hrtop)).div_const 2
  apply squeeze_zero (fun n => mul_nonneg (sq_nonneg _) (integral_nonneg (fun ω => by positivity))) _ hb
  intro n
  have hh := mul_le_mul_of_nonneg_left (absolute_third_moment_bound (hY n) (hr n))
    (sq_nonneg (r n))
  convert! hh using 1
  field_simp <;> ring

/-- A second-order bias limit follows from actual C³ regularity and second
and fourth moment limits of the centered estimator. -/
theorem second_order_bias_limit {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {Y : ∀ n, Ω n → ℝ} (hY : ∀ n, MemLp (Y n) 4 (P n))
    {μ : ℝ} (hm : ∀ n, (∫ ω, Y n ω ∂P n) = μ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 3 g y| ≤ C)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hrtop : Tendsto r atTop atTop)
    {v k : ℝ} (h2 : Tendsto (fun n => r n ^ 2 * Var[Y n; P n]) atTop (𝓝 v))
    (h4 : Tendsto (fun n => r n ^ 4 * (∫ ω, (Y n ω - μ) ^ 4 ∂P n)) atTop (𝓝 k)) :
    Tendsto (fun n => r n ^ 2 * ((∫ ω, g (Y n ω) ∂P n) - g μ))
      atTop (𝓝 (iteratedDeriv 2 g μ / 2 * v)) := by
  have hZ n : MemLp (fun ω => Y n ω - μ) 4 (P n) := (hY n).sub (memLp_const μ)
  have hZ2 : Tendsto (fun n => r n ^ 2 * (∫ ω, (Y n ω - μ) ^ 2 ∂P n)) atTop (𝓝 v) := by
    convert! h2 using 1
    ext n
    rw [variance_eq_integral (hY n).aemeasurable, hm n]
  have h3 := scaled_absolute_third_moment_tendsto_zero hZ hr hrtop hZ2 h4
  have hR : Tendsto (fun n => |r n ^ 2 * ((∫ ω, g (Y n ω) ∂P n) - g μ -
      iteratedDeriv 2 g μ / 2 * Var[Y n; P n])|) atTop (𝓝 0) := by
    have hu : Tendsto (fun n => C / 6 * (r n ^ 2 * (∫ ω, |Y n ω - μ| ^ 3 ∂P n)))
        atTop (𝓝 0) := by simpa using h3.const_mul (C / 6)
    apply squeeze_zero (fun n => abs_nonneg _) _ hu
    intro n
    have hh := mul_le_mul_of_nonneg_left
      (second_order_expectation_bound ((hY n).mono_exponent (by norm_num : (3 : ℝ≥0∞) ≤ 4))
        (hm n) hg hC).2 (sq_nonneg (r n))
    simpa only [abs_mul, abs_pow, sq_abs, mul_assoc, mul_left_comm, mul_comm] using hh
  have hR' : Tendsto (fun n => r n ^ 2 * ((∫ ω, g (Y n ω) ∂P n) - g μ -
      iteratedDeriv 2 g μ / 2 * Var[Y n; P n])) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using hR
  convert! hR'.add (h2.const_mul (iteratedDeriv 2 g μ / 2)) using 1
  · ext n
    ring
  · ring

end LectureNotes
