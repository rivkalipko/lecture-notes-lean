import LectureNotes.LargeSample

namespace LectureNotes

open MeasureTheory

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
    {X : Ω → ℝ} {c M : ℝ} (hX_nonneg : 0 ≤ᵐ[μ] (fun ω => (X ω - c) ^ 2))
    (hX : Integrable (fun ω => (X ω - c) ^ 2) μ) (hM : 0 < M) :
    μ.real {ω | M ^ 2 ≤ (X ω - c) ^ 2} ≤
      (∫ ω, (X ω - c) ^ 2 ∂μ) / M ^ 2 := by
  apply markov_inequality hX_nonneg hX
  positivity

end LectureNotes
