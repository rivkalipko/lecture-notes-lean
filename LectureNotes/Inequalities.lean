import LectureNotes.LargeSample

namespace LectureNotes

open MeasureTheory ProbabilityTheory

/-- L3 Theorem 1, including the moment assumptions needed by the real integral. -/
theorem jensen_inequality {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {g : ℝ → ℝ}
    (hg : ConvexOn ℝ Set.univ g) (hgc : Continuous g)
    (hX : Integrable X P) (hgX : Integrable (g ∘ X) P) :
    g (P[X]) ≤ ∫ ω, g (X ω) ∂P :=
  hg.map_integral_le hgc.continuousOn isClosed_univ (by simp) hX hgX

/-!
  The basic inequalities in Lecture 3 are stated for measurable random
  variables.  These versions use Mathlib's `Integrable` and `MemLp`
  hypotheses, so the real-valued integrals appearing in the conclusions are
  well-defined.
-/

theorem markov_inequality {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX_nonneg : 0 ≤ᵐ[μ] X) (hX : Integrable X μ)
    {M : ℝ} (hM : 0 < M) :
    μ.real {ω | M ≤ X ω} ≤ (∫ ω, X ω ∂μ) / M := by
  apply (le_div_iff₀ hM).2
  simpa [mul_comm] using
    (MeasureTheory.mul_meas_ge_le_integral_of_nonneg hX_nonneg hX M)

theorem holder_inequality {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p q : ℝ} (hpq : p.HolderConjugate q) {X Y : Ω → ℝ}
    (hX_nonneg : 0 ≤ᵐ[μ] X) (hY_nonneg : 0 ≤ᵐ[μ] Y)
    (hX : MemLp X (ENNReal.ofReal p) μ)
    (hY : MemLp Y (ENNReal.ofReal q) μ) :
    ∫ ω, X ω * Y ω ∂μ ≤
      (∫ ω, X ω ^ p ∂μ) ^ (1 / p) *
        (∫ ω, Y ω ^ q ∂μ) ^ (1 / q) := by
  exact MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    hpq hX_nonneg hY_nonneg hX hY

/-!
  This is the squared-deviation form of Chebyshev's inequality.  It is the
  form directly supplied by Markov's inequality and avoids hiding the
  positivity argument needed to replace `|X-c| ≥ M` by its square.
-/
theorem chebyshev_inequality {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {c M : ℝ}
    (hX : Integrable (fun ω => (X ω - c) ^ 2) μ) (hM : 0 < M) :
    μ.real {ω | M ^ 2 ≤ (X ω - c) ^ 2} ≤
      (∫ ω, (X ω - c) ^ 2 ∂μ) / M ^ 2 := by
  apply markov_inequality (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hX
  positivity

/-- L3 Theorem 3 in the absolute-deviation form printed in the notes. -/
theorem chebyshev_deviation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |X ω - P[X]|} ≤ ENNReal.ofReal (Var[X; P] / ε ^ 2) :=
  meas_ge_le_variance_div_sq hX hε

/-- L3 Theorem 4 for arbitrary signed random variables. -/
theorem holder_absolute {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {p q : ℝ} (hpq : p.HolderConjugate q) {X Y : Ω → ℝ}
    (hX : MemLp X (ENNReal.ofReal p) P) (hY : MemLp Y (ENNReal.ofReal q) P) :
    (∫ ω, |X ω * Y ω| ∂P) ≤
      (∫ ω, |X ω| ^ p ∂P) ^ (1 / p) * (∫ ω, |Y ω| ^ q ∂P) ^ (1 / q) := by
  simpa only [Pi.abs_apply, abs_mul] using
    integral_mul_le_Lp_mul_Lq_of_nonneg hpq
      (Filter.Eventually.of_forall (fun ω => abs_nonneg (X ω)))
      (Filter.Eventually.of_forall (fun ω => abs_nonneg (Y ω))) hX.abs hY.abs

end LectureNotes
