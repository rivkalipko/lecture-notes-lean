import LectureNotes.SufficientTests
import LectureNotes.NormalSufficiency
import LectureNotes.NormalSampling

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- The sample mean under the actual full IID normal experiment has variance
v/n. This identifies the sufficient-statistic experiment exactly. -/
theorem normalLocationExperiment_sampleMean_hasLaw {n : ℕ} (hn : 0 < n)
    (μ : ℝ) (v : ℝ≥0) :
    HasLaw (sampleMean : (Fin n → ℝ) → ℝ) (gaussianReal μ (v / n))
      (normalLocationExperiment n v μ) := by
  have hX i : HasLaw (fun x : Fin n → ℝ => x i) (gaussianReal μ v)
      (normalLocationExperiment n v μ) :=
    ⟨(measurable_pi_apply i).aemeasurable,
      (measurePreserving_eval (fun _ : Fin n => gaussianReal μ v) i).map_eq⟩
  exact normal_sampleMean hn hX (iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable))

/-- L9's simple normal alternative: a lower sample-mean cutoff maximizes
power among every measurable randomized full-data test of no larger null size. -/
theorem normal_full_sample_lower_tail_most_powerful {n : ℕ} (hn : 0 < n)
    {v : ℝ≥0} (hv : 0 < v) {θ₀ θ₁ : ℝ} (hθ : θ₁ < θ₀)
    (c : ℝ) (φ : StatisticalTest (Fin n → ℝ))
    (hsize : φ.power (normalLocationExperiment n v θ₀) ≤
      ((gaussianLowerTail c).pullback (sampleMean : (Fin n → ℝ) → ℝ)
        (by unfold sampleMean; fun_prop)).power (normalLocationExperiment n v θ₀)) :
    φ.power (normalLocationExperiment n v θ₁) ≤
      ((gaussianLowerTail c).pullback (sampleMean : (Fin n → ℝ) → ℝ)
        (by unfold sampleMean; fun_prop)).power (normalLocationExperiment n v θ₁) := by
  obtain ⟨ψ, hψ⟩ := sufficient_statistic_preserves_test_power (normal_sampleMean_sufficient hn hv) φ
  have he θ : ψ.power (gaussianReal θ (v / n)) = φ.power (normalLocationExperiment n v θ) := by
    rw [← (normalLocationExperiment_sampleMean_hasLaw hn θ v).map_eq]
    exact hψ θ
  simp only [StatisticalTest.pullback_power,
    (normalLocationExperiment_sampleMean_hasLaw hn _ v).map_eq] at hsize ⊢
  rw [← he] at hsize ⊢
  exact gaussianLowerTail_most_powerful (div_pos hv (by exact_mod_cast hn)) hθ c ψ hsize

/-- The power of the full-sample lower-tail test is strictly decreasing in
the mean, as in the normal example of L9. -/
theorem normal_full_sample_lower_tail_power_strictAnti {n : ℕ} (hn : 0 < n)
    {v : ℝ≥0} (hv : 0 < v) (c : ℝ) :
    StrictAnti (fun θ => ((gaussianLowerTail c).pullback
      (sampleMean : (Fin n → ℝ) → ℝ) (by unfold sampleMean; fun_prop)).power
        (normalLocationExperiment n v θ)) := by
  have he : (fun θ => ((gaussianLowerTail c).pullback
      (sampleMean : (Fin n → ℝ) → ℝ) (by unfold sampleMean; fun_prop)).power
        (normalLocationExperiment n v θ)) =
      (fun θ => (gaussianLowerTail c).power (gaussianReal θ (v / n))) := by
    funext θ
    rw [StatisticalTest.pullback_power, (normalLocationExperiment_sampleMean_hasLaw hn θ v).map_eq]
  rw [he]
  exact gaussianLowerTail_power_strictAnti (div_pos hv (by exact_mod_cast hn)) c

/-- L9's one-sided normal-mean test is UMP among all measurable randomized
full-sample tests, by actual sufficient-statistic reduction. -/
theorem normal_full_sample_lower_tail_ump {n : ℕ} (hn : 0 < n)
    (θ₀ : ℝ) {v : ℝ≥0} (hv : 0 < v) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    ((gaussianLowerTail (distributionQuantile (gaussianReal θ₀ (v / n)) α)).pullback
      (sampleMean : (Fin n → ℝ) → ℝ) (by unfold sampleMean; fun_prop)).IsUMP
      (normalLocationExperiment n v) (Ici θ₀) (Iio θ₀) α := by
  have hvn : 0 < v / (n : ℝ≥0) := div_pos hv (by exact_mod_cast hn)
  have hm : (fun θ => (normalLocationExperiment n v θ).map
      (sampleMean : (Fin n → ℝ) → ℝ)) = (fun θ => gaussianReal θ (v / n)) :=
    funext (fun θ => (normalLocationExperiment_sampleMean_hasLaw hn θ v).map_eq)
  apply isUMP_pullback_of_sufficient (normal_sampleMean_sufficient hn hv)
  rw [hm]
  exact gaussianLowerTail_one_sided_ump θ₀ hvn hα

/-- L9's two-sided counterexample for the full IID normal sample. Every
measurable [0,1]-valued randomized test is covered, including tests that use
more than the sample mean. -/
theorem normal_full_sample_no_two_sided_ump {n : ℕ} (hn : 0 < n)
    (θ₀ : ℝ) {v : ℝ≥0} (hv : 0 < v) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    ¬ ∃ φ : StatisticalTest (Fin n → ℝ),
      φ.IsUMP (normalLocationExperiment n v) {θ₀} {θ | θ ≠ θ₀} α := by
  rw [exists_ump_iff_of_sufficient (normal_sampleMean_sufficient hn hv)]
  have hm : (fun θ => (normalLocationExperiment n v θ).map
      (sampleMean : (Fin n → ℝ) → ℝ)) = (fun θ => gaussianReal θ (v / n)) :=
    funext (fun θ => (normalLocationExperiment_sampleMean_hasLaw hn θ v).map_eq)
  rw [hm]
  exact normal_observation_no_two_sided_ump θ₀ (div_pos hv (by exact_mod_cast hn)) hα

end LectureNotes
