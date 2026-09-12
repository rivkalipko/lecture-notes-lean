import LectureNotes.Convergence

/-! L3 Theorem 6: Cramér–Wold, derived from Lévy's continuity theorem. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem cramer_wold {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : ℕ → Ω → E} {Y : Ω' → E}
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y Q) :
    TendstoInDistribution X atTop Y (fun _ => P) Q ↔
      ∀ L : E →L[ℝ] ℝ, TendstoInDistribution (fun n ω => L (X n ω)) atTop
        (fun ω => L (Y ω)) (fun _ => P) Q := by
  constructor
  · intro h L
    exact h.continuous_comp L.continuous
  · intro h
    refine ⟨hX, hY, ?_⟩
    apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro t
    let L := InnerProductSpace.toDualMap ℝ E t
    have ht := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp (h L).tendsto 1
    simp only [ProbabilityMeasure.coe_mk] at ht ⊢
    have he (ν : Measure E) : charFun ν t = charFun (ν.map L) 1 := by
      rw [charFun_eq_charFunDual_toDualMap, charFunDual_eq_charFun_map_one]
    simp_rw [he]
    simp only [AEMeasurable.map_map_of_aemeasurable L.measurable.aemeasurable (hX _),
      AEMeasurable.map_map_of_aemeasurable L.measurable.aemeasurable hY]
    exact ht
end LectureNotes
