import LectureNotes.BernoulliModel
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- On a finite sample space every real-valued estimator has a uniformly
bounded expectation across all probability laws. This rules out the unbounded
estimand 1/p as p approaches zero (L5 Example 2). -/
theorem finite_sample_no_unbiased_reciprocal {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (P : ℝ → Measure Ω)
    (hP : ∀ p ∈ Ioo (0 : ℝ) 1, IsProbabilityMeasure (P p)) :
    ¬ ∃ T : Ω → ℝ, ∀ p ∈ Ioo (0 : ℝ) 1, (∫ ω, T ω ∂P p) = 1 / p := by
  rintro ⟨T, hT⟩
  let M := ∑ ω, |T ω|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hbound (ω : Ω) : T ω ≤ M := (le_abs_self _).trans
    (Finset.single_le_sum (f := fun ω => |T ω|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ω))
  let p := 1 / (M + 2)
  have hden : 0 < M + 2 := by linarith
  have hp : p ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨one_div_pos.mpr hden, (div_lt_one hden).mpr (by linarith)⟩
  have : IsProbabilityMeasure (P p) := hP p hp
  have hb : (∫ ω, T ω ∂P p) ≤ M := by
    calc
      _ ≤ ∫ _ : Ω, M ∂P p := integral_mono Integrable.of_finite (integrable_const _) hbound
      _ = M := by simp
  rw [hT p hp] at hb
  have he : 1 / p = M + 2 := by dsimp only [p]; field_simp
  rw [he] at hb
  linarith

/-- No real-valued estimator based on a fixed finite Bernoulli sample is
unbiased for the reciprocal success probability over all interior parameters.
This uses the actual product Bernoulli experiment. -/
theorem bernoulli_reciprocal_no_unbiased (n : ℕ) :
    ¬ ∃ T : (Fin n → Fin 2) → ℝ, ∀ p ∈ Ioo (0 : ℝ) 1,
      (∫ x, T x ∂Measure.pi (fun _ : Fin n => bernoulliRegularDensity.model p)) = 1 / p := by
  apply finite_sample_no_unbiased_reciprocal
  intro p hp
  have : IsProbabilityMeasure (bernoulliRegularDensity.model p) :=
    bernoulliRegularDensity.model_isProbabilityMeasure hp
  infer_instance

end LectureNotes
