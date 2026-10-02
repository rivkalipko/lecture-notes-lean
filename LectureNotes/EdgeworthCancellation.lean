import LectureNotes.StochasticPowers

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem stochasticBigO_deterministic_scale {a : ℕ → ℝ} (ha : ∀ n, a n ≠ 0) :
    StochasticBigO (P := P) (fun n (_ : Ω) => a n) a := by
  refine ⟨ha, fun ε hε => ⟨2, by norm_num, fun n => ?_⟩⟩
  have he : {ω : Ω | 2 * |a n| < |a n|} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    nlinarith [abs_nonneg (a n)]
  rw [he, measureReal_empty]
  exact hε

theorem stochasticBigO_neg {X : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (hX : StochasticBigO (P := P) X a) :
    StochasticBigO (P := P) (fun n ω => -X n ω) a := by
  simpa only [StochasticBigO, abs_neg] using hX

theorem stochasticBigO_add_same_power {X Y : ℕ → Ω → ℝ} {a : ℝ}
    (hX : StochasticBigO (P := P) X (powerScale a))
    (hY : StochasticBigO (P := P) Y (powerScale a)) :
    StochasticBigO (P := P) (fun n ω => X n ω + Y n ω) (powerScale a) := by
  simpa only [max_self] using stochasticBigO_add_power hX hY

/-- The algebraic refinement argument in L8: when actual sampling and
conditional bootstrap CDFs have the displayed expansions, the shared Gaussian
term cancels and the coefficient estimation rate gives an order 1/n difference.
The two expansions and coefficient rate are explicit hypotheses, not conclusions
claimed under finite moments alone. This is pointwise in the evaluation point x. -/
theorem edgeworth_bootstrap_cancellation
    (F : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (F n)]
    (B : ℕ → Ω → Measure ℝ) [∀ n ω, IsProbabilityMeasure (B n ω)]
    (x c : ℝ) (D S : ℕ → Ω → ℝ) (R : ℕ → ℝ)
    (hF : ∀ n, cdf (F n) x = cdf (gaussianReal 0 1) x +
      powerScale (-(1 / 2)) n * c + R n)
    (hB : ∀ n ω, cdf (B n ω) x = cdf (gaussianReal 0 1) x +
      powerScale (-(1 / 2)) n * D n ω + S n ω)
    (hD : StochasticBigO (P := P) (fun n ω => D n ω - c) (powerScale (-(1 / 2))))
    (hR : StochasticBigO (P := P) (fun n (_ : Ω) => R n) (powerScale (-1)))
    (hS : StochasticBigO (P := P) S (powerScale (-1))) :
    StochasticBigO (P := P) (fun n ω => cdf (F n) x - cdf (B n ω) x)
      (powerScale (-1)) := by
  have ha : StochasticBigO (P := P) (fun n (_ : Ω) => powerScale (-(1 / 2)) n)
      (powerScale (-(1 / 2))) := stochasticBigO_deterministic_scale
        (fun n => (powerScale_pos _ n).ne')
  have hm : StochasticBigO (P := P)
      (fun n ω => powerScale (-(1 / 2)) n * (D n ω - c)) (powerScale (-1)) := by
    convert stochasticBigO_mul_power ha hD using 1 <;> norm_num
  have hh := stochasticBigO_add_same_power
    (stochasticBigO_add_same_power (stochasticBigO_neg hm) hR) (stochasticBigO_neg hS)
  convert! hh using 1
  funext n ω
  rw [hF, hB]
  ring

end LectureNotes
