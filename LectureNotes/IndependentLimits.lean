import LectureNotes.VectorScoreCLT
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology

/-- Independent coordinates with converging marginal laws converge jointly
to the product of those laws. Independence is required separately in each row. -/
theorem independent_joint_limit {Ω E F : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    [PseudoMetrizableSpace E] [PseudoMetrizableSpace F]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Q : Measure E} {R : Measure F} [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    {X : ℕ → Ω → E} {Y : ℕ → Ω → F}
    (hX : TendstoInDistribution X atTop id (fun _ => P) Q)
    (hY : TendstoInDistribution Y atTop id (fun _ => P) R)
    (hind : ∀ n, IndepFun (X n) (Y n) P) :
    TendstoInDistribution (fun n ω => (X n ω, Y n ω)) atTop id
      (fun _ => P) (Q.prod R) where
  forall_aemeasurable n := (hX.forall_aemeasurable n).prodMk (hY.forall_aemeasurable n)
  tendsto := by
    have h := ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
      (hX.tendsto.prodMk_nhds hY.tendsto)
    have he (n : ℕ) : (⟨P.map (fun ω => (X n ω, Y n ω)),
        Measure.isProbabilityMeasure_map ((hX.forall_aemeasurable n).prodMk
          (hY.forall_aemeasurable n))⟩ : ProbabilityMeasure (E × F)) =
        ProbabilityMeasure.prod (⟨P.map (X n), Measure.isProbabilityMeasure_map (hX.forall_aemeasurable n)⟩ :
          ProbabilityMeasure E)
        (⟨P.map (Y n), Measure.isProbabilityMeasure_map (hY.forall_aemeasurable n)⟩ :
          ProbabilityMeasure F) := by
      apply Subtype.ext
      exact (hind n).map_prod_eq_prod_map_map
        (hX.forall_aemeasurable n) (hY.forall_aemeasurable n)
    have he' : ProbabilityMeasure.prod (⟨Q.map id, Measure.isProbabilityMeasure_map aemeasurable_id⟩ :
        ProbabilityMeasure E)
        (⟨R.map id, Measure.isProbabilityMeasure_map aemeasurable_id⟩ : ProbabilityMeasure F) =
        (⟨(Q.prod R).map id, Measure.isProbabilityMeasure_map aemeasurable_id⟩ :
          ProbabilityMeasure (E × F)) := by
      apply Subtype.ext
      change (Q.map id).prod (R.map id) = (Q.prod R).map id
      simp only [Measure.map_id]
    simpa only [Function.comp_def, ← he, he'] using h

/-- Reindexing a distributional limit by sample sizes tending to infinity. -/
theorem distribution_limit_subsequence {Ω E Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : ℕ → Ω → E} {Z : Ω' → E}
    (hX : TendstoInDistribution X atTop Z (fun _ => P) Q)
    {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) :
    TendstoInDistribution (fun n => X (m n)) atTop Z (fun _ => P) Q :=
  ⟨fun n => hX.forall_aemeasurable (m n), hX.aemeasurable_limit, hX.tendsto.comp hm⟩

end LectureNotes
