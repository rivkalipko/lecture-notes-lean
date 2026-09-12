import LectureNotes.SamplingMoments
import LectureNotes.Convergence

/-! L3 Theorem 10: Chebyshev's weak law for uncorrelated observations. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem expectation_sampleMean {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Integrable (X i) P) :
    P[fun ω => sampleMean (fun i => X i ω)] = sampleMean (fun i => P[X i]) := by
  unfold sampleMean
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hX i)]

theorem uncorrelated_sampleMean_variance {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; P] = 0) :
    Var[fun ω => sampleMean (fun i => X i ω); P] =
      (n : ℝ)⁻¹ ^ 2 * ∑ i, Var[X i; P] := by
  unfold sampleMean
  rw [variance_const_mul, variance_fun_sum hX]
  simp only [Fintype.card_fin]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [sum_eq_single i]
  · exact covariance_self (hX i).aemeasurable
  · intro j _ hji
    exact hcov i j hji.symm
  · simp

theorem weak_law_uncorrelated {X : ℕ → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; P] = 0)
    (hvar : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ ^ 2 * ∑ i : Fin n, Var[X i; P])
      atTop (𝓝 0)) :
    ConvergesInProbability P
      (fun n ω => sampleMean (fun i : Fin n => X i ω) -
        sampleMean (fun i : Fin n => P[X i])) (fun _ => 0) := by
  apply mean_square_implies_probability
  have hM (n) := sampleMean_memLp (fun i : Fin n => hX i)
  have hmean (n) := expectation_sampleMean
    (fun i : Fin n => (hX i).integrable (by norm_num))
  refine ⟨fun n => ((hM n).sub (memLp_const _)).sub (memLp_const 0), ?_⟩
  have heq (n) :
      (∫ ω, |sampleMean (fun i : Fin n => X i ω) -
          sampleMean (fun i : Fin n => P[X i]) - 0| ^ 2 ∂P) =
        (n : ℝ)⁻¹ ^ 2 * ∑ i : Fin n, Var[X i; P] := by
    simp only [sub_zero, sq_abs]
    rw [← hmean n, ← variance_eq_integral (hM n).aemeasurable,
      uncorrelated_sampleMean_variance (fun i : Fin n => hX i)
        (fun i j hij => hcov i j (fun h => hij (Fin.ext h)))]
  simpa only [heq] using hvar
end LectureNotes
