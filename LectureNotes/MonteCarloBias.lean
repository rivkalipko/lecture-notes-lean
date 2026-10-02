import LectureNotes.BootstrapBias
import LectureNotes.BootstrapVarianceConsistency

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

/-- Averaging independent Monte Carlo draws gives the exact variance/B error. -/
theorem monteCarlo_sampleMean_mse {Γ : Type*} [MeasurableSpace Γ]
    (Q : Measure Γ) [IsProbabilityMeasure Q] {Y : Γ → ℝ} (hY : MemLp Y 2 Q)
    {B : ℕ} [NeZero B] :
    (∫ z, (sampleMean (fun j : Fin B => Y (z j)) - ∫ γ, Y γ ∂Q) ^ 2
      ∂Measure.pi (fun _ : Fin B => Q)) = Var[Y; Q] / B := by
  let R := Measure.pi (fun _ : Fin B => Q)
  have hE (j : Fin B) : HasLaw (fun z : Fin B → Γ => z j) Q R :=
    (measurePreserving_eval (fun _ : Fin B => Q) j).hasLaw
  have hYi (j : Fin B) : MemLp (fun z : Fin B → Γ => Y (z j)) 2 R :=
    hY.comp_measurePreserving (measurePreserving_eval (fun _ : Fin B => Q) j)
  have hm (j : Fin B) : (∫ z, Y (z j) ∂ R) = ∫ γ, Y γ ∂Q :=
    (hE j).integral_comp hY.aestronglyMeasurable
  have hv (j : Fin B) : Var[fun z : Fin B → Γ => Y (z j); R] = Var[Y; Q] := by
    rw [variance_eq_integral (hYi j).aemeasurable, hm j,
      variance_eq_integral hY.aemeasurable]
    exact (hE j).integral_comp ((hY.aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2)
  have hmean := sampleMean_expectation (Nat.pos_of_ne_zero (NeZero.ne B))
    (fun j => (hYi j).integrable (by norm_num)) hm
  have hvar := sampleMean_variance (Nat.pos_of_ne_zero (NeZero.ne B)) hYi
    (fun _ _ hij => (iIndepFun_pi (fun _ : Fin B => hY.aemeasurable)).indepFun hij) hv
  rw [variance_eq_integral (sampleMean_memLp hYi).aemeasurable, hmean] at hvar
  exact hvar

/-- A Lipschitz transform preserves square integrability on a probability space. -/
theorem lipschitz_memLp_two {Γ : Type*} [MeasurableSpace Γ]
    {Q : Measure Γ} [IsProbabilityMeasure Q] {Y : Γ → ℝ} (hY : MemLp Y 2 Q)
    {g : ℝ → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g) : MemLp (fun γ => g (Y γ)) 2 Q := by
  have hL : LipschitzWith L (fun y => g y - g 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hg.dist_le_mul x y
  have hh := hL.comp_memLp (by simp) hY
  convert! hh.add (memLp_const (g 0)) using 1
  ext γ
  simp

/-- The variance of a Lipschitz transform is bounded by the squared Lipschitz
constant times the variance of its input. -/
theorem variance_lipschitz_le {Γ : Type*} [MeasurableSpace Γ]
    {Q : Measure Γ} [IsProbabilityMeasure Q] {Y : Γ → ℝ} (hY : MemLp Y 2 Q)
    {g : ℝ → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g) :
    Var[fun γ => g (Y γ); Q] ≤ (L : ℝ) ^ 2 * Var[Y; Q] := by
  have hgY := lipschitz_memLp_two hY hg
  have hD := hgY.sub (memLp_const (g (∫ γ, Y γ ∂Q)))
  have hZ := hY.sub (memLp_const (∫ γ, Y γ ∂Q))
  rw [← variance_sub_const hgY.aestronglyMeasurable (g (∫ γ, Y γ ∂Q))]
  refine (variance_le_expectation_sq hD.aestronglyMeasurable).trans ?_
  rw [variance_eq_integral hY.aemeasurable, ← integral_const_mul]
  apply integral_mono hD.integrable_sq (hZ.integrable_sq.const_mul _)
  intro γ
  have h := hg.dist_le_mul (Y γ) (∫ γ, Y γ ∂Q)
  simp only [Real.dist_eq] at h
  change (g (Y γ) - g (∫ γ, Y γ ∂Q)) ^ 2 ≤ (L : ℝ) ^ 2 * (Y γ - ∫ γ, Y γ ∂Q) ^ 2
  have hs := mul_self_le_mul_self (abs_nonneg _) h
  simpa only [← pow_two, mul_pow, sq_abs] using hs


/-- Exact Monte Carlo error in the simulated bootstrap bias. -/
theorem simulatedBootstrapBias_mse {n B : ℕ} [NeZero n] [NeZero B]
    (x : Fin n → ℝ) {g : ℝ → ℝ}
    (hg : MemLp (fun b : Fin n → ℝ => g (sampleMean b)) 2 (bootstrapLaw x)) :
    (∫ z, (simulatedBootstrapBias g x z - bootstrapBias g x) ^ 2
      ∂Measure.pi (fun _ : Fin B => bootstrapLaw x)) =
      Var[fun b : Fin n → ℝ => g (sampleMean b); bootstrapLaw x] / B := by
  letI := bootstrapLaw_isProbabilityMeasure x
  simpa only [simulatedBootstrapBias, bootstrapBias, sub_sub_sub_cancel_right] using
    monteCarlo_sampleMean_mse (bootstrapLaw x) hg (B := B)

/-- For a Lipschitz transform the conditional Monte Carlo bias error has
MSE at most L² times empirical variance divided by nB. -/
theorem simulatedBootstrapBias_mse_le {n B : ℕ} [NeZero n] [NeZero B]
    (x : Fin n → ℝ) {g : ℝ → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g) :
    (∫ z, (simulatedBootstrapBias g x z - bootstrapBias g x) ^ 2
      ∂Measure.pi (fun _ : Fin B => bootstrapLaw x)) ≤
      (L : ℝ) ^ 2 * empiricalVariance x / ((n : ℝ) * B) := by
  letI := bootstrapLaw_isProbabilityMeasure x
  rw [simulatedBootstrapBias_mse x (lipschitz_memLp_two (bootstrap_sampleMean_memLp x) hg)]
  have h := div_le_div_of_nonneg_right (variance_lipschitz_le (bootstrap_sampleMean_memLp x) hg)
    (Nat.cast_nonneg B)
  rw [bootstrap_sampleMean_variance] at h
  convert! h using 1
  ring

/-- Simulation error is negligible relative to the order 1/n bias when
B(n)/n tends to infinity. Only a Lipschitz transform and convergent empirical
variances are needed for this conditional statement. -/
theorem simulatedBootstrapBias_scaled_probability
    (x : ∀ n : ℕ, Fin (n + 1) → ℝ) {g : ℝ → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {B : ℕ → ℕ} [∀ n, NeZero (B n)]
    {v : ℝ} (hv : Tendsto (fun n => empiricalVariance (x n)) atTop (𝓝 v))
    (hB : Tendsto (fun n => (n + 1 : ℕ) / (B n : ℝ)) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (Measure.pi (fun _ : Fin (B n) => bootstrapLaw (x n))).real
      {z | ε ≤ |(n + 1 : ℕ) * (simulatedBootstrapBias g (x n) z - bootstrapBias g (x n))|})
      atTop (𝓝 0) := by
  let P n := Measure.pi (fun _ : Fin (B n) => bootstrapLaw (x n))
  letI (n : ℕ) : IsProbabilityMeasure (bootstrapLaw (x n)) := bootstrapLaw_isProbabilityMeasure _
  let Y (n : ℕ) (z : Fin (B n) → (Fin (n + 1) → ℝ)) :=
    (n + 1 : ℕ) * (simulatedBootstrapBias g (x n) z - bootstrapBias g (x n))
  have hY n : MemLp (Y n) 2 (P n) := by
    have hG := lipschitz_memLp_two (bootstrap_sampleMean_memLp (x n)) hg
    have hA : MemLp (fun z : Fin (B n) → (Fin (n + 1) → ℝ) =>
        sampleMean (fun j => g (sampleMean (z j)))) 2 (P n) := by
      apply sampleMean_memLp
      intro j
      exact hG.comp_measurePreserving (measurePreserving_eval (fun _ : Fin (B n) => bootstrapLaw (x n)) j)
    dsimp [Y, simulatedBootstrapBias, bootstrapBias]
    simpa only [sub_sub_sub_cancel_right, Pi.sub_apply] using!
      (hA.sub (memLp_const (∫ b, g (sampleMean b) ∂bootstrapLaw (x n)))).const_mul (n + 1 : ℕ)
  apply row_secondMoment_implies_probability hY
  have hup : Tendsto (fun n => (L : ℝ) ^ 2 * empiricalVariance (x n) *
      ((n + 1 : ℕ) / (B n : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hv).mul hB
  apply squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _)) _ hup
  intro n
  have he : (∫ z, Y n z ^ 2 ∂P n) = (n + 1 : ℕ) ^ 2 *
      (∫ z, (simulatedBootstrapBias g (x n) z - bootstrapBias g (x n)) ^ 2 ∂P n) := by
    simp only [Y, mul_pow, integral_const_mul]
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (simulatedBootstrapBias_mse_le (x n) hg (B := B n))
    (sq_nonneg ((n + 1 : ℕ) : ℝ))
  convert! hh using 1
  field_simp <;> ring

/-- Under IID observations with finite variance, the preceding simulation
bound holds on one event of probability one for the observed samples. -/
theorem iid_simulatedBootstrapBias_scaled_probability {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {g : ℝ → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {B : ℕ → ℕ} [∀ n, NeZero (B n)]
    (hB : Tendsto (fun n => (n + 1 : ℕ) / (B n : ℝ)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ ε > 0, Tendsto (fun n =>
      (Measure.pi (fun _ : Fin (B n) => bootstrapLaw (fun i : Fin (n + 1) => X i ω))).real
      {z | ε ≤ |(n + 1 : ℕ) * (simulatedBootstrapBias g (fun i : Fin (n + 1) => X i ω) z -
        bootstrapBias g (fun i : Fin (n + 1) => X i ω))|}) atTop (𝓝 0) := by
  filter_upwards [empiricalVariance_strong_consistency hXm hX hind hident] with ω hω
  exact simulatedBootstrapBias_scaled_probability (fun n i => X i ω) hg
    (hω.comp (tendsto_add_atTop_nat 1)) hB

end LectureNotes
