import LectureNotes.BootstrapMoments
import LectureNotes.LindebergBounds

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- Finite second moments make the squared tails vanish as the truncation
threshold increases through the natural numbers. -/
theorem truncSecondMoment_nat_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hXm : Measurable X) (hX : MemLp X 2 P) :
    Tendsto (fun M : ℕ => truncSecondMoment P X M) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun ω => X ω ^ 2)
    (fun M : ℕ => (integrable_truncSecondMoment hXm hX M).aestronglyMeasurable)
    hX.integrable_sq
    (fun M => ae_of_all _ (fun ω => by split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X ω)), sq_nonneg]))
    (ae_of_all _ (fun ω => by
      apply tendsto_const_nhds.congr'
      filter_upwards [tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop (|X ω| : ℝ))] with M hM
      simp [not_lt.mpr hM]))
  simpa only [truncSecondMoment, integral_zero] using h

/-- A centered tail above twice a bound for the center is controlled by four
times the uncentered squared tail. -/
theorem centered_tail_sq_le_raw_tail (x c r M : ℝ) (hc : |c| ≤ M) (hr : 2 * M ≤ r) :
    (if r < |x - c| then (x - c) ^ 2 else 0) ≤
      4 * (if M < |x| then x ^ 2 else 0) := by
  split_ifs with htail hx hx
  · have hxc : |x - c| ≤ 2 * |x| := by
      have ht := abs_sub x c
      linarith
    have hsq := pow_le_pow_left₀ (abs_nonneg (x - c)) hxc 2
    norm_num only [mul_pow, sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] at hsq
    exact hsq
  · have ht := abs_sub x c
    have hx' := le_of_not_gt hx
    exfalso
    linarith
  · positivity
  · norm_num

/-- Fixed-threshold empirical tail convergence implies that tails at any
threshold tending to infinity vanish, even after a convergent centering. -/
theorem empirical_centered_tail_tendsto_zero
    (x : ∀ n : ℕ, Fin (n + 1) → ℝ) (c r : ℕ → ℝ) (μ : ℝ) (a : ℕ → ℝ)
    (hc : Tendsto c atTop (𝓝 μ)) (hr : Tendsto r atTop atTop)
    (ha : Tendsto a atTop (𝓝 0))
    (ht : ∀ M : ℕ, Tendsto
      (fun n => sampleMean (fun i => if (M : ℝ) < |x n i| then x n i ^ 2 else 0))
      atTop (𝓝 (a M))) :
    Tendsto (fun n => sampleMean (fun i =>
      if r n < |x n i - c n| then (x n i - c n) ^ 2 else 0)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlarge : ∀ᶠ M : ℕ in atTop, |μ| < (M : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop |μ|)
  obtain ⟨M, hMa, hM⟩ := ((ha.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 8))).and hlarge).exists
  have hca : ∀ᶠ n in atTop, |c n| ≤ (M : ℝ) :=
    ((hc.abs).eventually (gt_mem_nhds hM)).mono (fun _ h => h.le)
  have hra : ∀ᶠ n in atTop, 2 * (M : ℝ) ≤ r n := hr.eventually (eventually_ge_atTop _)
  have hraw : ∀ᶠ n in atTop,
      sampleMean (fun i => if (M : ℝ) < |x n i| then x n i ^ 2 else 0) < ε / 4 :=
    (ht M).eventually (gt_mem_nhds (by linarith))
  filter_upwards [hca, hra, hraw] with n hcn hrn htn
  have hb : sampleMean (fun i => if r n < |x n i - c n| then (x n i - c n) ^ 2 else 0) ≤
      4 * sampleMean (fun i => if (M : ℝ) < |x n i| then x n i ^ 2 else 0) := by
    unfold sampleMean
    calc
      _ ≤ (Fintype.card (Fin (n + 1)) : ℝ)⁻¹ *
          ∑ i, 4 * (if (M : ℝ) < |x n i| then x n i ^ 2 else 0) := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
          centered_tail_sq_le_raw_tail (x n i) (c n) (r n) M hcn hrn)) (by positivity)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hn : 0 ≤ sampleMean (fun i => if r n < |x n i - c n| then (x n i - c n) ^ 2 else 0) := by
    unfold sampleMean
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
  linarith

/-- Strong consistency of the ordinary sample mean with n+1 observations. -/
theorem iid_sampleMean_succ_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hint : Integrable (X 0) P) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => sampleMean (fun i : Fin (n + 1) => X i ω))
      atTop (𝓝 (P[X 0])) := by
  have h := strong_law_of_large_numbers hint (fun _ _ hij => hind.indepFun hij) hident
  filter_upwards [h] with ω hω
  convert! hω.comp (tendsto_add_atTop_nat 1) using 1
  funext n
  simp only [Function.comp_apply, sampleMean, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => X i ω) (n + 1)]
  ring

set_option maxHeartbeats 1200000 in
/-- Every fixed empirical squared tail converges almost surely to its
population counterpart. Only a second moment is needed. -/
theorem iid_empirical_truncated_secondMoment_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (M : ℕ) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => sampleMean (fun i : Fin (n + 1) =>
        if (M : ℝ) < |X i ω| then X i ω ^ 2 else 0))
      atTop (𝓝 (truncSecondMoment P (X 0) M)) := by
  have hm : Measurable (fun x : ℝ => if (M : ℝ) < |x| then x ^ 2 else 0) :=
    (measurable_id.pow_const 2).indicator (measurableSet_lt measurable_const measurable_id.abs)
  exact iid_sampleMean_succ_ae
    (X := fun i ω => if (M : ℝ) < |X i ω| then X i ω ^ 2 else 0)
    (integrable_truncSecondMoment (hXm 0) hX M)
    (hind.comp (fun _ x => if (M : ℝ) < |x| then x ^ 2 else 0) (fun _ => hm))
    (fun i => (hident i).comp hm)

/-- The Lindeberg tail condition for the empirical distribution, almost surely
under IID finite-second-moment sampling. The threshold is the bootstrap CLT
threshold δ*σ*√(n+1), and centering is by the actual observed sample mean. -/
theorem iid_empirical_bootstrap_lindeberg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (σ : ℝ) (hσ : 0 < σ) :
    ∀ᵐ ω ∂P, ∀ δ > 0, Tendsto
      (fun n => sampleMean (fun i : Fin (n + 1) =>
        if δ * (Real.sqrt ((n : ℝ) + 1) * σ) <
            |X i ω - sampleMean (fun j : Fin (n + 1) => X j ω)|
        then (X i ω - sampleMean (fun j : Fin (n + 1) => X j ω)) ^ 2 else 0))
      atTop (𝓝 0) := by
  have ht : ∀ᵐ ω ∂P, ∀ M : ℕ, Tendsto
      (fun n => sampleMean (fun i : Fin (n + 1) =>
        if (M : ℝ) < |X i ω| then X i ω ^ 2 else 0))
      atTop (𝓝 (truncSecondMoment P (X 0) M)) :=
    ae_all_iff.mpr (fun M => iid_empirical_truncated_secondMoment_ae hXm hX hind hident M)
  filter_upwards [ht, iid_sampleMean_succ_ae (hX.integrable (by norm_num)) hind hident] with ω hω hm
  intro δ hδ
  have hr : Tendsto (fun n : ℕ => δ * (Real.sqrt ((n : ℝ) + 1) * σ)) atTop atTop := by
    have hs := Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    convert! hs.const_mul_atTop (mul_pos hδ hσ) using 1
    funext n
    simp only [Function.comp_apply]
    ring
  exact empirical_centered_tail_tendsto_zero (fun n i => X i ω)
    (fun n => sampleMean (fun i : Fin (n + 1) => X i ω))
    (fun n => δ * (Real.sqrt ((n : ℝ) + 1) * σ)) (P[X 0])
    (fun M => truncSecondMoment P (X 0) M) hm hr
    (truncSecondMoment_nat_tendsto_zero (hXm 0) hX) hω

end LectureNotes
