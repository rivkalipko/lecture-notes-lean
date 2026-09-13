import LectureNotes.Convergence

/-! L3 delta method using the continuous divided difference (dslope).
This avoids choosing potentially nonmeasurable mean-value witnesses. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

theorem deterministic_convergence_probability {a : ℕ → ℝ} {c : ℝ}
    (h : Tendsto a atTop (𝓝 c)) :
    ConvergesInProbability P (fun n _ => a n) (fun _ => c) :=
  almost_sure_implies_probability (fun _ => aemeasurable_const) (ae_of_all _ (fun _ => h))

theorem distribution_to_constant_implies_probability {X : ℕ → Ω → ℝ} {c : ℝ}
    (h : ConvergesInDistribution P Q X (fun _ => c)) :
    ConvergesInProbability P X (fun _ => c) := by
  rw [ConvergesInProbability, tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  let s : Set ℝ := {x | ε ≤ ‖x - c‖}
  have hclosed : IsClosed s := isClosed_le continuous_const (by fun_prop)
  have hcs : c ∉ s := by simp [s, hε.not_ge]
  have hfront : c ∉ frontier s := fun hc => hcs (hclosed.frontier_subset hc)
  have hmap : Q.map (fun _ : Ω' => c) = Measure.dirac c := by simp
  have hboundary : Q.map (fun _ : Ω' => c) (frontier s) = 0 := by
    rw [hmap]
    simp [hfront]
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h.tendsto hboundary
  simp only [ProbabilityMeasure.coe_mk, hmap] at ht
  simp only [Measure.dirac_apply, Set.indicator_of_notMem hcs] at ht
  have hreal := (ENNReal.continuousAt_toReal (by simp : (0 : ENNReal) ≠ ⊤)).tendsto.comp ht
  simpa only [Function.comp_def, ENNReal.toReal_zero, Measure.map_apply_of_aemeasurable
    (h.forall_aemeasurable _) hclosed.measurableSet, measureReal_def, s, preimage_setOf_eq] using hreal

theorem convergence_distribution_congr_eventually {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : ConvergesInDistribution P Q X Z) (hY : ∀ n, AEMeasurable (Y n) P)
    (he : ∀ᶠ n in atTop, X n = Y n) : ConvergesInDistribution P Q Y Z where
  forall_aemeasurable := hY
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.congr' (he.mono (fun n hn => by
    apply Subtype.ext
    exact congrArg (Measure.map · P) hn))

/-- The zero-limit probability conclusion printed after L3 Theorem 8. -/
theorem slutsky_mul_zero {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : ConvergesInDistribution P Q X Z)
    (hY : ConvergesInProbability P Y (fun _ => 0))
    (hYm : ∀ n, AEMeasurable (Y n) P) :
    ConvergesInProbability P (fun n ω => X n ω * Y n ω) (fun _ => 0) := by
  apply distribution_to_constant_implies_probability (Q := Q)
  simpa only [mul_zero] using slutsky_mul hX hY hYm

/-- General scalar delta method. Rates are eventually nonzero and their
inverses tend to zero; this includes the notes' square-root rate exactly. -/
theorem delta_method {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {μ : ℝ} {r : ℕ → ℝ}
    (hX : ∀ n, AEMeasurable (X n) P) (hr : ∀ᶠ n in atTop, r n ≠ 0)
    (hrlim : Tendsto (fun n => (r n)⁻¹) atTop (𝓝 0))
    (h : ConvergesInDistribution P Q (fun n ω => r n * (X n ω - μ)) Z)
    {g : ℝ → ℝ} (hg : Continuous g) (hgd : DifferentiableAt ℝ g μ) :
    ConvergesInDistribution P Q (fun n ω => r n * (g (X n ω) - g μ))
      (fun ω => Z ω * deriv g μ) := by
  have hz := slutsky_mul h (deterministic_convergence_probability (P := P) hrlim)
    (fun _ => aemeasurable_const)
  have hcancel : ∀ᶠ n in atTop,
      (fun ω => r n * (X n ω - μ) * (r n)⁻¹) = (fun ω => X n ω - μ) := by
    filter_upwards [hr] with n hn
    funext ω
    field_simp [hn]
  have hd : ConvergesInDistribution P Q (fun n ω => X n ω - μ) (fun _ => 0) := by
    simpa only [mul_zero] using convergence_distribution_congr_eventually hz
      (fun n => (hX n).sub_const μ) hcancel
  have hp : ConvergesInProbability P X (fun _ => μ) := by
    have hp0 := distribution_to_constant_implies_probability hd
    simpa only [ConvergesInProbability, tendstoInMeasure_iff_norm, sub_zero] using hp0
  have hs : Continuous (dslope g μ) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = μ
    · subst x
      exact continuousAt_dslope_same.mpr hgd
    · exact (continuousAt_dslope_of_ne hx).mpr hg.continuousAt
  have hsp := continuous_mapping_probability_const (continuousAt_dslope_same.mpr hgd) hp
  have hsm := fun n => hs.measurable.comp_aemeasurable (hX n)
  have hprod := slutsky_mul h hsp hsm
  have he (n ω) : (r n * (X n ω - μ)) * dslope g μ (X n ω) =
      r n * (g (X n ω) - g μ) := by
    rw [mul_assoc]
    congr 1
    exact sub_smul_dslope g μ (X n ω)
  simpa only [he, dslope_same] using hprod

set_option backward.isDefEq.respectTransparency.types false in
/-- L3 Theorem 14 with the exact square-root normalization and the Gaussian
limit law, including its transformed variance. -/
theorem delta_method_normal {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {μ σ : ℝ}
    (hX : ∀ n, AEMeasurable (X n) P)
    (hZ : HasLaw Z (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) Q)
    (h : ConvergesInDistribution P Q (fun n ω => Real.sqrt n * (X n ω - μ)) Z)
    {g : ℝ → ℝ} (hg : Continuous g) (hgd : DifferentiableAt ℝ g μ) :
    ConvergesInDistribution P Q (fun n ω => Real.sqrt n * (g (X n ω) - g μ))
      (fun ω => Z ω * deriv g μ) ∧
    HasLaw (fun ω => Z ω * deriv g μ)
      (gaussianReal 0 ⟨σ ^ 2 * (deriv g μ) ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _)⟩) Q := by
  constructor
  · apply delta_method hX _ _ h hg hgd
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
      exact (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
    · exact tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  · have hv : (⟨σ ^ 2 * (deriv g μ) ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _)⟩ : NNReal) =
        (⟨(deriv g μ) ^ 2, sq_nonneg _⟩ : NNReal) * ⟨σ ^ 2, sq_nonneg σ⟩ := by
      apply Subtype.ext
      change σ ^ 2 * (deriv g μ) ^ 2 = (deriv g μ) ^ 2 * σ ^ 2
      ring
    rw [hv]
    simpa only [mul_zero, NNReal.mk] using! ProbabilityTheory.gaussianReal_mul_const hZ (deriv g μ)
end LectureNotes
