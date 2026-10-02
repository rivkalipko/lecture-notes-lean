import LectureNotes.VectorDeltaMethod

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- A local derivative and global measurability suffice for the delta method.
This permits transformations with singularities away from the true parameter. -/
theorem normed_delta_method_of_measurable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [SecondCountableTopology F]
    [MeasurableSpace F] [BorelSpace F]
    {X : ℕ → Ω → E} {Z : Ω' → E} {μ : E}
    {r : ℕ → ℝ} (hXm : ∀ n, AEMeasurable (X n) P)
    (hX : TendstoInMeasure P X atTop (fun _ => μ))
    (hCLT : TendstoInDistribution (fun n ω => r n • (X n ω - μ)) atTop Z (fun _ => P) Q)
    {g : E → F}
    (hg : Measurable g) {D : E →L[ℝ] F}
    (hd : HasFDerivAt g D μ) :
    TendstoInDistribution (fun n ω => r n • (g (X n ω) - g μ))
      atTop (fun ω => D (Z ω)) (fun _ => P) Q := by
  let R x := ‖g x - g μ - D (x - μ)‖ / ‖x - μ‖
  have hR : Measurable R := by dsimp [R]; fun_prop
  have hRlim : ConvergesInProbability P (fun n ω => R (X n ω)) (fun _ => 0) := by
    simpa only [ConvergesInProbability, R, sub_self, map_zero, sub_zero, norm_zero, div_zero]
      using continuous_mapping_probability_const_metric (normed_fderiv_remainder_ratio_continuousAt hd) hX
  have hnorm := hCLT.continuous_comp (g := fun x => ‖x‖) (by fun_prop)
  have hprod := slutsky_mul_zero hnorm hRlim (fun n => hR.comp_aemeasurable (hXm n))
  have he (n : ℕ) (ω : Ω) :
      ‖r n • (g (X n ω) - g μ) - D (r n • (X n ω - μ))‖ =
        ‖r n • (X n ω - μ)‖ * R (X n ω) := by
    rw [map_smul, ← smul_sub, norm_smul, norm_smul]
    by_cases hx : X n ω = μ
    · simp [hx, R]
    · have hn : ‖X n ω - μ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
      dsimp only [R]
      field_simp
  have herr : TendstoInMeasure P
      (fun n ω => r n • (g (X n ω) - g μ) - D (r n • (X n ω - μ))) atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_measureReal_norm]
    intro ε hε
    have hh := tendstoInMeasure_iff_measureReal_norm.mp hprod ε hε
    simpa only [Function.comp_apply, sub_zero, ← he, Real.norm_eq_abs, abs_norm] using hh
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ _
    (hCLT.continuous_comp D.continuous) herr
    (fun n => ((hg.comp_aemeasurable (hXm n)).sub_const (g μ)).const_smul (r n))

end LectureNotes
