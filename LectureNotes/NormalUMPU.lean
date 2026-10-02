import LectureNotes.NormalUnbiasedNP
import LectureNotes.NormalPowerDerivative
import LectureNotes.NormalFullSampleUMP

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- L9: the symmetric two-tail normal test is uniformly most powerful
among all unbiased measurable randomized tests of level α. -/
theorem normal_observation_two_tail_umpu (θ₀ : ℝ) {v : ℝ≥0} (hv : 0 < v)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    (gaussianTwoTail θ₀ (distributionQuantile (gaussianReal 0 1) (1 - α / 2) *
      Real.sqrt v)).IsUMPU (fun θ => gaussianReal θ v) {θ₀} {θ | θ ≠ θ₀} α := by
  let c := distributionQuantile (gaussianReal 0 1) (1 - α / 2) * Real.sqrt v
  have hc : 0 < c := mul_pos
    (standardNormal_quantile_pos ⟨by linarith [hα.2], by linarith [hα.1]⟩)
    (Real.sqrt_pos.mpr (by exact_mod_cast hv))
  have hcal : (gaussianTwoTail θ₀ c).power (gaussianReal θ₀ v) = α :=
    gaussianTwoTail_quantile_size θ₀ hv hα
  refine ⟨?_, gaussianTwoTail_unbiased θ₀ hv hc, ?_⟩
  · intro θ hθ
    rcases mem_singleton_iff.mp hθ with rfl
    exact hcal.le
  · intro ψ hψ hψu θ _
    rcases hψu with ⟨β, _, hbnull, hbalt⟩
    have hs := normal_unbiased_score_integral_zero ψ θ₀ β hv
      (hbnull θ₀ (by simp)) (fun t ht => hbalt t ht)
    have he : (fun x : ℝ => ψ.reject x * ((x - θ₀) / v)) =
        fun x => (ψ.reject x * (x - θ₀)) / v := by funext x; ring
    rw [he, integral_div] at hs
    have hm : (∫ x, ψ.reject x * (x - θ₀) ∂gaussianReal θ₀ v) = 0 :=
      (div_eq_zero_iff).mp hs |>.resolve_right (by exact_mod_cast hv.ne')
    apply gaussianTwoTail_most_powerful_zero_moment θ₀ θ hv hc ψ _ hm
    rw [hcal]
    exact hψ θ₀ (by simp)

/-- Sufficient-statistic averaging preserves level and unbiasedness together,
so an optimal unbiased statistic-based rule is optimal for the full data. -/
theorem isUMPU_pullback_of_sufficient {Θ Ω S : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace S]
    {P : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (P θ)] {T : Ω → S}
    (hT : IsSufficientStatistic P T) (ψ : StatisticalTest S)
    {null alternative : Set Θ} {α : ℝ}
    (hψ : ψ.IsUMPU (fun θ => (P θ).map T) null alternative α) :
    (ψ.pullback T hT.1).IsUMPU P null alternative α := by
  refine ⟨?_, ?_, ?_⟩
  · intro θ hθ
    rw [StatisticalTest.pullback_power]
    exact hψ.1 θ hθ
  · rcases hψ.2.1 with ⟨β, hb, hnull, halt⟩
    refine ⟨β, hb, ?_, ?_⟩
    · intro θ hθ
      rw [StatisticalTest.pullback_power]
      exact hnull θ hθ
    · intro θ hθ
      rw [StatisticalTest.pullback_power]
      exact halt θ hθ
  · intro φ hφ hφu θ hθ
    obtain ⟨η, hη⟩ := sufficient_statistic_preserves_test_power hT φ
    have hηlevel : η.HasLevel (fun θ => (P θ).map T) null α := by
      intro ξ hξ
      rw [hη]
      exact hφ ξ hξ
    have hηu : η.IsUnbiased (fun θ => (P θ).map T) null alternative := by
      rcases hφu with ⟨β, hb, hnull, halt⟩
      refine ⟨β, hb, ?_, ?_⟩
      · intro ξ hξ
        rw [hη]
        exact hnull ξ hξ
      · intro ξ hξ
        rw [hη]
        exact halt ξ hξ
    rw [StatisticalTest.pullback_power, ← hη]
    exact hψ.2.2 η hηlevel hηu θ hθ

/-- The actual IID normal full-sample test rejects when the sample mean is
more than z_(1−α/2)√(v/n) from the null mean. It is UMP among all unbiased
randomized full-sample tests, including those using more than the mean. -/
theorem normal_full_sample_two_tail_umpu {n : ℕ} (hn : 0 < n)
    (θ₀ : ℝ) {v : ℝ≥0} (hv : 0 < v) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    ((gaussianTwoTail θ₀ (distributionQuantile (gaussianReal 0 1) (1 - α / 2) *
      Real.sqrt (v / n : ℝ≥0))).pullback (sampleMean : (Fin n → ℝ) → ℝ)
        (by unfold sampleMean; fun_prop)).IsUMPU
      (normalLocationExperiment n v) {θ₀} {θ | θ ≠ θ₀} α := by
  have hvn : 0 < v / (n : ℝ≥0) := div_pos hv (by exact_mod_cast hn)
  have hm : (fun θ => (normalLocationExperiment n v θ).map
      (sampleMean : (Fin n → ℝ) → ℝ)) = (fun θ => gaussianReal θ (v / n)) :=
    funext (fun θ => (normalLocationExperiment_sampleMean_hasLaw hn θ v).map_eq)
  apply isUMPU_pullback_of_sufficient (normal_sampleMean_sufficient hn hv)
  rw [hm]
  exact normal_observation_two_tail_umpu θ₀ hvn hα

end LectureNotes
