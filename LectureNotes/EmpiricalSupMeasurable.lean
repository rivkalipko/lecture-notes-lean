import LectureNotes.EmpiricalUniform
import LectureNotes.Bootstrap

set_option autoImplicit false

/-! The uniform empirical-CDF error is a measurable statistic. Right
continuity reduces its uncountable supremum to rational thresholds, even
when either distribution has atoms. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem sup_right_continuous_eq_rat {f : ℝ → ℝ}
    (hf : ∀ x, ContinuousWithinAt f (Ici x) x) (hb : BddAbove (range f)) :
    sSup (range f) = ⨆ q : ℚ, f (q : ℝ) := by
  have hbq : BddAbove (range (fun q : ℚ => f (q : ℝ))) := by
    apply hb.mono
    rintro _ ⟨q, rfl⟩
    exact mem_range_self (q : ℝ)
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    rintro _ ⟨x, rfl⟩
    obtain ⟨u, _, hux, hu⟩ := Rat.denseRange_cast.exists_seq_strictAnti_tendsto
      (show Monotone (fun q : ℚ => (q : ℝ)) from fun _ _ h => by dsimp only; exact_mod_cast h) x
    have hu' : Tendsto (fun n => (u n : ℝ)) atTop (𝓝[Ici x] x) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hu, .of_forall (fun n => ?_)⟩
      change x ≤ (u n : ℝ)
      exact (hux n).le
    exact le_of_tendsto ((hf x).tendsto.comp hu')
      (.of_forall (fun n => le_ciSup hbq (u n)))
  · apply ciSup_le
    intro q
    exact le_csSup hb (mem_range_self (q : ℝ))

theorem empiricalCDF_right_continuous {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    ContinuousWithinAt (empiricalCDF x) (Ici t) t := by
  by_cases hn : n = 0
  · subst n
    have he : empiricalCDF x = (fun _ => (0 : ℝ)) := by funext s; simp [empiricalCDF]
    rw [he]
    exact continuousWithinAt_const
  · letI : NeZero n := ⟨hn⟩
    convert! (cdf (empiricalLaw x)).right_continuous t using 1
    funext s
    exact (empiricalLaw_cdf x s).symm

theorem empiricalCDFSupError_eq_rat (μ : Measure ℝ) {n : ℕ} (x : Fin n → ℝ) :
    empiricalCDFSupError μ x = ⨆ q : ℚ, |empiricalCDF x (q : ℝ) - cdf μ (q : ℝ)| := by
  apply sup_right_continuous_eq_rat
  · intro t
    exact ((empiricalCDF_right_continuous x t).sub ((cdf μ).right_continuous t)).abs
  · exact empiricalCDF_error_bddAbove μ x

theorem measurable_empiricalCDFSupError {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure ℝ) {n : ℕ} (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) :
    Measurable (fun ω => empiricalCDFSupError μ (fun i => X i ω)) := by
  simp_rw [empiricalCDFSupError_eq_rat]
  exact Measurable.iSup (fun q : ℚ => ((measurable_empiricalCDF X hX q).sub_const _).abs)

end LectureNotes
