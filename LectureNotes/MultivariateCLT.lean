import LectureNotes.CramerWold

/-! L3 Theorem 12 in finite-dimensional real inner-product spaces.
The limit is specified by its centered Gaussian projection laws, equivalently
the multivariate centered Gaussian with the covariance of one observation. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

set_option maxHeartbeats 800000 in
theorem multivariate_central_limit_theorem {Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : ℕ → Ω → E} {Z : Ω' → E}
    (hX : MemLp (X 0) 2 P) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hZ : AEMeasurable Z Q)
    (hLaw : ∀ L : E →L[ℝ] ℝ,
      HasLaw (fun ω => L (Z ω)) (gaussianReal 0 Var[fun ω => L (X 0 ω); P].toNNReal) Q) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ •
        ((∑ i ∈ Finset.range n, X i ω) - (n : ℝ) • P[X 0]))
      atTop Z (fun _ => P) Q := by
  refine (cramer_wold ?_ hZ).mpr ?_
  · intro n
    apply AEMeasurable.const_smul
    apply AEMeasurable.sub
    · convert! (Finset.aemeasurable_sum (Finset.range n)
        (fun i _ => (hident i).aemeasurable_fst)) using 1
      funext ω
      simp
    · exact aemeasurable_const
  · intro L
    have hi := hind.comp (fun _ => L) (fun _ => L.measurable)
    have hid := fun i => (hident i).comp L.measurable
    have hLp : MemLp (fun ω => L (X 0 ω)) 2 P := hX.continuousLinearMap_comp L
    have hc := central_limit_theorem (P := P) (P' := Q)
      (X := fun i ω => L (X i ω)) (Y := fun ω => L (Z ω)) (hLaw L) hLp hi hid
    have he : P[fun ω => L (X 0 ω)] = L (P[X 0]) :=
      L.integral_comp_comm (hX.integrable (by norm_num))
    simpa only [map_smul, map_sub, map_sum, smul_eq_mul, he, Function.comp_def] using! hc
end LectureNotes
