import LectureNotes.LargeSample

namespace LectureNotes

/-! Formal definitions for the estimation language in Lectures 5 and 6. -/

noncomputable def Likelihood {Θ α : Type*} (f : α → Θ → ℝ) (x : α) : Θ → ℝ := f x

noncomputable def LogLikelihood {Θ α : Type*} (f : α → Θ → ℝ) (x : α) (θ : Θ) : ℝ :=
  Real.log (Likelihood f x θ)

noncomputable def Score {Θ α : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    (ℓ : Θ → α → ℝ) (x : α) (θ : Θ) : Θ →L[ℝ] ℝ :=
  fderiv ℝ (fun p => ℓ p x) θ

noncomputable def FisherInformation {α : Type*} [MeasurableSpace α]
    (P : MeasureTheory.Measure α) (score : α → ℝ) : ℝ :=
  ∫ x, score x ^ 2 ∂P

def IsMLE {Θ α : Type*} (L : Θ → α → ℝ) (x : α) (θhat : Θ) : Prop :=
  ∀ θ, L θhat x ≥ L θ x

def MomentEquation {Θ : Type*} (m : Θ → ℝ) (observed : ℝ) (θhat : Θ) : Prop :=
  observed = m θhat

theorem score_eq_deriv_log_likelihood {f : ℝ → ℝ}
    {θ₀ d : ℝ} (hf : 0 < f θ₀) (hderiv : HasDerivAt f d θ₀) :
    HasDerivAt (fun θ => Real.log (f θ)) (d / f θ₀) θ₀ := by
  simpa using hderiv.log (ne_of_gt hf)

theorem score_zero_at_interior_mle {L : ℝ → ℝ} {θhat d : ℝ}
    (hmax : IsLocalMax L θhat) (hderiv : HasDerivAt L d θhat) : d = 0 := by
  calc
    d = deriv L θhat := hderiv.deriv.symm
    _ = 0 := hmax.deriv_eq_zero

theorem log_likelihood_preserves_mle {Θ α : Type*} {L : Θ → α → ℝ} {x : α}
    {θhat : Θ} (hpos : ∀ θ, 0 < L θ x) :
    IsMLE L x θhat ↔ ∀ θ, Real.log (L θhat x) ≥ Real.log (L θ x) := by
  constructor
  · intro h θ
    exact (Real.strictMonoOn_log.monotoneOn (hpos θ) (hpos θhat) (h θ))
  · intro h θ
    exact (Real.strictMonoOn_log.le_iff_le (hpos θ) (hpos θhat)).mp (h θ)

theorem moment_equation_is_definition {Θ : Type*} (m : Θ → ℝ)
    (observed : ℝ) (θhat : Θ) :
    MomentEquation m observed θhat ↔ observed = m θhat := Iff.rfl

end LectureNotes
