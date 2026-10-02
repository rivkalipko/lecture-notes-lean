import LectureNotes.FinitePopulation
import LectureNotes.Estimation

noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Finset

/-- Fixed potential outcomes determine the finite-population treatment effect. -/
def finitePopulationATE {N : ℕ} (y₁ y₀ : Fin N → ℝ) : ℝ :=
  sampleMean (fun i => y₁ i - y₀ i)

/-- Treatment is precisely membership in the randomly selected subset. -/
def observedOutcome {N : ℕ} (y₁ y₀ : Fin N → ℝ) (s : Finset (Fin N))
    (i : Fin N) : ℝ := if i ∈ s then y₁ i else y₀ i

def randomizedDifferenceInMeans {N : ℕ} (n : ℕ) (y₁ y₀ : Fin N → ℝ)
    (s : Finset (Fin N)) : ℝ :=
  designMean n y₁ selectionIndicator s -
    designMean (N - n) y₀ (fun i t => 1 - selectionIndicator i t) s

/-- Both averages use observed outcomes; missing potential outcomes cancel
because their treatment/control indicators vanish. -/
theorem randomizedDifferenceInMeans_observed {N : ℕ} (n : ℕ)
    (y₁ y₀ : Fin N → ℝ) (s : Finset (Fin N)) :
    randomizedDifferenceInMeans n y₁ y₀ s =
      (n : ℝ)⁻¹ * ∑ i, (if i ∈ s then observedOutcome y₁ y₀ s i else 0) -
      ((N - n : ℕ) : ℝ)⁻¹ * ∑ i, (if i ∉ s then observedOutcome y₁ y₀ s i else 0) := by
  unfold randomizedDifferenceInMeans designMean
  congr 2
  · apply sum_congr rfl
    intro i _
    by_cases h : i ∈ s <;> simp [selectionIndicator, observedOutcome, h]
  · apply sum_congr rfl
    intro i _
    by_cases h : i ∈ s <;> simp [selectionIndicator, observedOutcome, h]

/-- The controls are the complement of the same assignment. No independence
between treated and control averages is asserted or needed. -/
theorem randomized_control_mean_expectation {N n : ℕ} (hn : 0 < n)
    (hN : n < N) (y₀ : Fin N → ℝ) :
    (simpleRandomSampling hN.le)[designMean (N - n) y₀
      (fun i t => 1 - selectionIndicator i t)] = sampleMean y₀ := by
  apply designMean_expectation (by omega) y₀
  · intro i
    exact (integrable_const _).sub ((selectionIndicator_memLp i _).integrable (by norm_num))
  · intro i
    rw [integral_sub (integrable_const _)
      ((selectionIndicator_memLp i _).integrable (by norm_num)),
      integral_const, probReal_univ, one_smul,
      selectionIndicator_expectation, simpleRandomSampling_inclusion hn hN.le]
    rw [Nat.cast_sub hN.le]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (hn.trans hN).ne'
    field_simp

/-- L5 Example 4: exact design-unbiasedness in a completely randomized
experiment with positive treated and control group sizes. -/
theorem randomizedDifferenceInMeans_unbiased {N n : ℕ} (hn : 0 < n)
    (hN : n < N) (y₁ y₀ : Fin N → ℝ) :
    Unbiased (simpleRandomSampling hN.le) (randomizedDifferenceInMeans n y₁ y₀)
      (finitePopulationATE y₁ y₀) := by
  refine ⟨Integrable.of_finite, ?_⟩
  rw [show randomizedDifferenceInMeans n y₁ y₀ =
    fun s => designMean n y₁ selectionIndicator s -
      designMean (N - n) y₀ (fun i t => 1 - selectionIndicator i t) s from rfl,
    integral_sub Integrable.of_finite Integrable.of_finite,
    simpleRandomSampling_mean hn hN.le, randomized_control_mean_expectation hn hN]
  simp only [finitePopulationATE, sampleMean, sum_sub_distrib, mul_sub]

end LectureNotes
