import LectureNotes.PoissonLikelihood

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

theorem poissonSampleLikelihood_continuous {n : ℕ} (x : Fin n → ℕ) :
    Continuous (poissonSampleLikelihood x) := by
  have he : poissonSampleLikelihood x = fun r : ℝ≥0 =>
      (r : ℝ) ^ (∑ i, x i) * Real.exp (-n * r) / (∏ i, (x i).factorial : ℝ) :=
    funext (poissonSampleLikelihood_formula x)
  rw [he]
  fun_prop

/-- Restricting to positive rates gives the same likelihood supremum,
although the supremum is unattained when all observed counts are zero. -/
theorem poisson_positive_likelihood_sup {n : ℕ} (hn : 0 < n) (x : Fin n → ℕ) :
    sSup (poissonSampleLikelihood x '' Ioi (0 : ℝ≥0)) =
      poissonSampleLikelihood x (poissonSampleMLE x) := by
  have hne : (poissonSampleLikelihood x '' Ioi (0 : ℝ≥0)).Nonempty :=
    ⟨_, mem_image_of_mem _ (show (1 : ℝ≥0) ∈ Ioi 0 by norm_num)⟩
  have hb : BddAbove (poissonSampleLikelihood x '' Ioi (0 : ℝ≥0)) :=
    ⟨_, by rintro _ ⟨r, hr, rfl⟩; exact poissonSampleMLE_isMLE hn x r⟩
  apply le_antisymm
  · apply csSup_le hne
    rintro _ ⟨r, hr, rfl⟩
    exact poissonSampleMLE_isMLE hn x r
  · have hc : IsClosed {r : ℝ≥0 | poissonSampleLikelihood x r ≤
        sSup (poissonSampleLikelihood x '' Ioi (0 : ℝ≥0))} :=
      isClosed_le (poissonSampleLikelihood_continuous x) continuous_const
    have hh := closure_minimal (fun r (hr : r ∈ Ioi (0 : ℝ≥0)) =>
      le_csSup hb (mem_image_of_mem _ hr)) hc
    rw [closure_Ioi] at hh
    exact hh (show poissonSampleMLE x ∈ Ici (0 : ℝ≥0) by
      change (0 : ℝ≥0) ≤ poissonSampleMLE x
      positivity)

/-- The positive-parameter and nonnegative-parameter experiments have exactly
identical likelihood-ratio statistics at every positive null rate. -/
theorem poisson_positive_likelihoodRatio_eq {n : ℕ} (hn : 0 < n) (x : Fin n → ℕ)
    (r₀ : Ioi (0 : ℝ≥0)) :
    likelihoodRatio (fun (y : Fin n → ℕ) (r : Ioi (0 : ℝ≥0)) => poissonSampleLikelihood y r)
      {r₀} x = likelihoodRatio poissonSampleLikelihood {(r₀ : ℝ≥0)} x := by
  rw [poisson_likelihoodRatio_eq hn]
  unfold likelihoodRatio
  rw [Set.image_singleton, csSup_singleton]
  have he : Set.range (fun r : Ioi (0 : ℝ≥0) => poissonSampleLikelihood x r) =
      poissonSampleLikelihood x '' Ioi (0 : ℝ≥0) := by
    ext y
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r, r.property, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  rw [he, poisson_positive_likelihood_sup hn]

/-- The source formula holds for the actual positive-domain likelihood
supremum, including the sample with zero total count. -/
theorem poisson_positive_minus_two_log_likelihoodRatio {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℕ) (r₀ : Ioi (0 : ℝ≥0)) :
    -2 * Real.log (likelihoodRatio
      (fun (y : Fin n → ℕ) (r : Ioi (0 : ℝ≥0)) => poissonSampleLikelihood y r) {r₀} x) =
      poissonLR n (poissonSampleMLE x) (r₀ : ℝ≥0) := by
  rw [poisson_positive_likelihoodRatio_eq hn]
  exact poisson_minus_two_log_likelihoodRatio hn x r₀.property

end LectureNotes
