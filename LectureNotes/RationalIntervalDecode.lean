import LectureNotes.LikelihoodRatioSupport

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Measurable recovery of the endpoints of a nondegenerate interval from the
positive coordinates of a rationally indexed likelihood-ratio vector. -/
def rationalIntervalDecode (r : ℚ → ℝ≥0∞) : ℝ × ℝ :=
  ((⨅ q : ℚ, if r q ≠ 0 then ((q : ℝ) : EReal) else ⊤).toReal,
    (⨆ q : ℚ, if r q ≠ 0 then ((q : ℝ) : EReal) else ⊥).toReal)

theorem rationalIntervalDecode_measurable : Measurable rationalIntervalDecode := by
  unfold rationalIntervalDecode
  apply Measurable.prodMk
  · apply measurable_ereal_toReal.comp
    apply Measurable.iInf
    intro q
    exact Measurable.ite ((measurable_pi_apply q) (measurableSet_singleton 0)).compl
      measurable_const measurable_const
  · apply measurable_ereal_toReal.comp
    apply Measurable.iSup
    intro q
    exact Measurable.ite ((measurable_pi_apply q) (measurableSet_singleton 0)).compl
      measurable_const measurable_const

/-- Rational points determine both endpoints when the interval has positive
length. This excludes the empty-rational-support case for a singleton interval. -/
theorem rationalIntervalDecode_recover {a b : ℝ} (hab : a < b) (r : ℚ → ℝ≥0∞)
    (hr : ∀ q, r q ≠ 0 ↔ a ≤ (q : ℝ) ∧ (q : ℝ) ≤ b) :
    rationalIntervalDecode r = (a, b) := by
  have habE : (a : EReal) < (b : EReal) := by exact_mod_cast hab
  have hlow : (⨅ q : ℚ, if r q ≠ 0 then ((q : ℝ) : EReal) else ⊤) = (a : EReal) := by
    apply le_antisymm
    · by_contra hh
      obtain ⟨q, haq, hq⟩ := EReal.exists_rat_btwn_of_lt (lt_min habE (lt_of_not_ge hh))
      have haqR : a < (q : ℝ) := by exact_mod_cast haq
      have hqbR : (q : ℝ) < b := by exact_mod_cast (lt_min_iff.mp hq).1
      have hcut : r q ≠ 0 := (hr q).mpr ⟨haqR.le, hqbR.le⟩
      have hle := iInf_le (fun q : ℚ => if r q ≠ 0 then ((q : ℝ) : EReal) else ⊤) q
      change (⨅ q : ℚ, if r q ≠ 0 then ((q : ℝ) : EReal) else ⊤) ≤
        (if r q ≠ 0 then ((q : ℝ) : EReal) else ⊤) at hle
      rw [if_pos hcut] at hle
      exact (not_lt_of_ge hle) (lt_min_iff.mp hq).2
    · apply le_iInf
      intro q
      split_ifs with hq
      · exact_mod_cast ((hr q).mp hq).1
      · exact le_top
  have hupp : (⨆ q : ℚ, if r q ≠ 0 then ((q : ℝ) : EReal) else ⊥) = (b : EReal) := by
    apply le_antisymm
    · apply iSup_le
      intro q
      split_ifs with hq
      · exact_mod_cast ((hr q).mp hq).2
      · exact bot_le
    · by_contra hh
      obtain ⟨q, hq, hqb⟩ := EReal.exists_rat_btwn_of_lt (max_lt habE (lt_of_not_ge hh))
      have haqR : a < (q : ℝ) := by exact_mod_cast (max_lt_iff.mp hq).1
      have hqbR : (q : ℝ) < b := by exact_mod_cast hqb
      have hcut : r q ≠ 0 := (hr q).mpr ⟨haqR.le, hqbR.le⟩
      have hle := le_iSup (fun q : ℚ => if r q ≠ 0 then ((q : ℝ) : EReal) else ⊥) q
      change (if r q ≠ 0 then ((q : ℝ) : EReal) else ⊥) ≤
        (⨆ q : ℚ, if r q ≠ 0 then ((q : ℝ) : EReal) else ⊥) at hle
      rw [if_pos hcut] at hle
      exact (not_lt_of_ge hle) (max_lt_iff.mp hq).2
  unfold rationalIntervalDecode
  rw [hlow, hupp, EReal.toReal_coe, EReal.toReal_coe]

end LectureNotes
