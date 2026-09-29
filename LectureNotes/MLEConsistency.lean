import LectureNotes.EstimationTheory
import LectureNotes.Convergence

set_option autoImplicit false

/-! L7 Theorem 1: a precise argmax consistency theorem.
The three conditions printed in the notes alone are insufficient. The actual
proof uses a separated population maximum and a uniform law of large numbers.
The error envelope below states that uniform convergence without requiring a
potentially nonmeasurable supremum over the parameter space. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- Deterministic comparison behind the argmax theorem. -/
theorem argmax_population_gap_le {Θ : Type*} {M m : Θ → ℝ} {t θ₀ : Θ} {e : ℝ}
    (he : ∀ θ, |m θ - M θ| ≤ e) (hmax : m θ₀ ≤ m t) :
    M θ₀ - M t ≤ 2 * e := by
  have h₀ := abs_le.mp (he θ₀)
  have ht := abs_le.mp (he t)
  linarith

/-- Uniform criterion convergence and a well-separated maximum imply
consistency of any measurable maximizer. Only comparison with θ₀ is needed;
there is no assumption of the desired convergence of the maximizers. -/
theorem argmax_consistency {Ω Θ : Type*} [MeasurableSpace Ω] [MetricSpace Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (M : Θ → ℝ) (m : ℕ → Ω → Θ → ℝ) (T : ℕ → Ω → Θ) (θ₀ : Θ)
    (_hT : ∀ n, AEMeasurable (T n) P)
    (E : ℕ → Ω → ℝ)
    (hsep : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ θ, ε ≤ dist θ θ₀ → δ ≤ M θ₀ - M θ)
    (huniform : ∀ n ω θ, |m n ω θ - M θ| ≤ E n ω)
    (hmax : ∀ n ω, m n ω θ₀ ≤ m n ω (T n ω))
    (hE : TendstoInMeasure P E atTop (fun _ => 0)) :
    TendstoInMeasure P T atTop (fun _ => θ₀) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  obtain ⟨δ, hδ, hgap⟩ := hsep ε hε
  have hb (n) : P.real {ω | ε ≤ dist (T n ω) θ₀} ≤
      P.real {ω | δ / 2 ≤ dist (E n ω) 0} := by
    refine measureReal_mono ?_ (measure_ne_top P _)
    intro ω hω
    have hg := (hgap (T n ω) hω).trans
      (argmax_population_gap_le (huniform n ω) (hmax n ω))
    simp only [mem_setOf_eq, Real.dist_eq, sub_zero]
    have := le_abs_self (E n ω)
    linarith
  exact squeeze_zero (fun _ => measureReal_nonneg) hb
    (tendstoInMeasure_iff_measureReal_dist.mp hE (δ / 2) (by positivity))

/-- A maximizer of the likelihood is also a maximizer of every positive
rescaling of its logarithm. This connects the argmax criterion to MLEs. -/
theorem mle_maximizes_average_log {Θ Ω : Type*} (L : Ω → Θ → ℝ)
    (x : Ω) (t : Θ) (r : ℝ) (hr : 0 < r) (hL : ∀ θ, 0 < L x θ)
    (h : IsMLE L x t) : ∀ θ, Real.log (L x θ) / r ≤ Real.log (L x t) / r := by
  intro θ
  exact div_le_div_of_nonneg_right
    ((log_likelihood_preserves_mle hL).mp h θ) hr.le

end LectureNotes
