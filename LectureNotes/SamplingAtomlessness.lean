import LectureNotes.NormalSamplingDistribution

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- A quadratic equation in one atomless real coordinate has probability zero. -/
theorem atomless_square_level (μ : Measure ℝ) [NullSingletonClass μ] (a c : ℝ) :
    μ {x | x ^ 2 + a = c} = 0 := by
  apply measure_mono_null (t := {Real.sqrt (c - a), -Real.sqrt (c - a)})
  · intro x hx
    have hn : 0 ≤ c - a := by have := sq_nonneg x; dsimp at hx; linarith
    have he : x ^ 2 = Real.sqrt (c - a) ^ 2 := by rw [Real.sq_sqrt hn]; dsimp at hx; linarith
    simpa only [mem_insert_iff, mem_singleton_iff] using sq_eq_sq_iff_eq_or_eq_neg.mp he
  · exact ((finite_singleton _).insert _).measure_zero μ

/-- Positive degrees of freedom give an atomless chi-square distribution.
The proof conditions on all but one independent normal coordinate. -/
theorem chiSquared_nullSingletonClass {n : ℕ} (hn : 0 < n) :
    NullSingletonClass (chiSquared n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal 0 1) 0).symm e
  constructor
  intro c
  rw [chiSquared, Measure.map_apply (by fun_prop) (measurableSet_singleton c), ← hp.map_eq,
    Measure.map_apply e.symm.measurable (by measurability)]
  have he : e.symm ⁻¹' ((fun z : Fin (m + 1) → ℝ => ∑ i, z i ^ 2) ⁻¹' {c}) =
      {z : ℝ × (Fin m → ℝ) | z.1 ^ 2 + ∑ i, z.2 i ^ 2 = c} := by
    ext z
    simp [e, Fin.sum_univ_succ]
  rw [he, Measure.prod_apply_symm (by measurability)]
  have hz (z : Fin m → ℝ) :
      (gaussianReal 0 1) ((fun x => (x, z)) ⁻¹'
        {z : ℝ × (Fin m → ℝ) | z.1 ^ 2 + ∑ i, z.2 i ^ 2 = c}) = 0 := by
    simpa only [preimage, mem_setOf_eq] using
      atomless_square_level (gaussianReal 0 1) (∑ i, z i ^ 2) c
  simp_rw [hz]
  simp

/-- The Student distribution has no atoms for positive degrees of freedom. -/
theorem studentT_nullSingletonClass {n : ℕ} (hn : 0 < n) :
    NullSingletonClass (studentT n) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  constructor
  intro c
  rw [studentT, Measure.map_apply (by fun_prop) (measurableSet_singleton c),
    Measure.prod_apply_symm (by measurability)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [chiSquared_ae_pos hn] with y hy
  have hs : Real.sqrt (y / n) ≠ 0 :=
    (Real.sqrt_pos.mpr (div_pos hy (by exact_mod_cast hn))).ne'
  have he : (fun x : ℝ => (x, y)) ⁻¹'
      ((fun z : ℝ × ℝ => z.1 / Real.sqrt (z.2 / n)) ⁻¹' {c}) =
      {c * Real.sqrt (y / n)} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, div_eq_iff hs]
  rw [he, measure_singleton]
  rfl

end LectureNotes
