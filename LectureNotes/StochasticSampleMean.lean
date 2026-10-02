import LectureNotes.StochasticPowers

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory

/-- The sample-mean stochastic rate needs only common first and second
moments and pairwise independence within each row. Degenerate variance is
allowed, and no independence between different sample sizes is assumed. -/
theorem sampleMean_stochasticBigO {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : (n : ℕ) → Fin (n+1) → Ω → ℝ}
    (hX : ∀ n i, MemLp (X n i) 2 P)
    (hind : ∀ n, Pairwise (fun i j => IndepFun (X n i) (X n j) P))
    {μ v : ℝ} (hμ : ∀ n i, P[X n i] = μ) (hv : ∀ n i, Var[X n i; P] = v) :
    StochasticBigO (P := P)
      (fun n ω => sampleMean (fun i => X n i ω) - μ)
      (fun n => 1 / Real.sqrt ((n : ℝ)+1)) := by
  have hv0 : 0 ≤ v := by rw [← hv 0 0]; exact variance_nonneg _ _
  have hmean (n) : P[fun ω => sampleMean (fun i => X n i ω)] = μ :=
    sampleMean_expectation (Nat.succ_pos n) (fun i => (hX n i).integrable (by norm_num)) (hμ n)
  have hvar (n) : Var[fun ω => sampleMean (fun i => X n i ω); P] = v/((n:ℝ)+1) := by
    simpa using sampleMean_variance (Nat.succ_pos n) (hX n) (hind n) (hv n)
  refine ⟨fun _ => by positivity, fun ε hε => ?_⟩
  let C := Real.sqrt (2*(v+1)/ε)
  have hC : 0 < C := Real.sqrt_pos.2 (by positivity)
  have hCsq : C^2 = 2*(v+1)/ε := Real.sq_sqrt (by positivity)
  refine ⟨C, hC, fun n => ?_⟩
  have hN : 0 < (n:ℝ)+1 := by positivity
  have hS : 0 < Real.sqrt ((n:ℝ)+1) := Real.sqrt_pos.2 hN
  have ht : 0 < C * |1/Real.sqrt ((n:ℝ)+1)| := by positivity
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (chebyshev_deviation (sampleMean_memLp (hX n)) ht)
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _)), hmean, hvar] at hb
  have hm := measureReal_mono (μ := P)
    (show {ω | C * |1/Real.sqrt ((n:ℝ)+1)| < |sampleMean (fun i => X n i ω) - μ|} ⊆
      {ω | C * |1/Real.sqrt ((n:ℝ)+1)| ≤ |sampleMean (fun i => X n i ω) - μ|} from
      fun ω h => show C * |1/Real.sqrt ((n:ℝ)+1)| ≤ |sampleMean (fun i => X n i ω) - μ| from h.le)
    (measure_ne_top P _)
  have he : (v/((n:ℝ)+1)) / (C * |1/Real.sqrt ((n:ℝ)+1)|)^2 =
      v * ε / (2*(v+1)) := by
    rw [abs_of_pos (by positivity), mul_pow, div_pow, Real.sq_sqrt hN.le, hCsq]
    field_simp
  rw [he] at hb
  apply (hm.trans hb).trans_lt
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

end LectureNotes
