import LectureNotes.BetaConjugacy

set_option autoImplicit false

/-! L12's conjugate-family recipe in logarithmic coordinates. Every assertion
of a proper prior or posterior requires finite positive normalization. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
variable {Θ X : Type*} [MeasurableSpace Θ]

/-- A class of probability priors is conjugate if every well-defined update
by a model likelihood belongs to that same class. -/
def IsConjugateClass (priors : Set (Measure Θ)) (L : X → Θ → ℝ) : Prop :=
  (∀ π ∈ priors, IsProbabilityMeasure π) ∧
    ∀ π ∈ priors, ∀ x, Integrable (L x) π → (∀ᵐ θ ∂π, 0 ≤ L x θ) →
      0 < evidence π (L x) → bayesUpdate π (L x) ∈ priors

theorem bayesUpdate_sequential (ν : Measure Θ) (p L : Θ → ℝ)
    (hp : Measurable p) (hL : Measurable L) (hp0 : ∀ θ, 0 ≤ p θ)
    (he : 0 < evidence ν p) :
    bayesUpdate (bayesUpdate ν p) L = bayesUpdate ν (fun θ => p θ * L θ) := by
  change bayesUpdate (ν.withDensity (fun θ => ENNReal.ofReal (p θ / evidence ν p))) L = _
  rw [bayesUpdate_withDensity ν _ _ (hp.div_const _) hL
    (fun θ => div_nonneg (hp0 θ) he.le)]
  have hfun : (fun θ => (p θ / evidence ν p) * L θ) =
      fun θ => (evidence ν p)⁻¹ * (p θ * L θ) := by
    funext θ
    ring
  rw [hfun, bayesUpdate_scale _ _ (inv_ne_zero he.ne')]

/-- The source's c(θ)^a exp(Σⱼ wⱼ(θ)bⱼ), with logc = log c. Logarithmic
coordinates express the family on a domain where c is strictly positive. -/
def exponentialConjugateKernel {k : ℕ} (logc : Θ → ℝ) (w : Fin k → Θ → ℝ)
    (a : ℝ) (b : Fin k → ℝ) (θ : Θ) : ℝ :=
  Real.exp (a * logc θ + ∑ j, w j θ * b j)

theorem exponential_conjugate_kernel_mul {k : ℕ}
    (logc : Θ → ℝ) (w : Fin k → Θ → ℝ) (a n : ℝ) (b t : Fin k → ℝ) (θ : Θ) :
    exponentialConjugateKernel logc w a b θ * exponentialConjugateKernel logc w n t θ =
      exponentialConjugateKernel logc w (a + n) (fun j => b j + t j) θ := by
  unfold exponentialConjugateKernel
  rw [← Real.exp_add]
  congr 1
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring

theorem exponentialConjugateKernel_measurable {k : ℕ}
    {logc : Θ → ℝ} {w : Fin k → Θ → ℝ}
    (hc : Measurable logc) (hw : ∀ j, Measurable (w j)) (a : ℝ) (b : Fin k → ℝ) :
    Measurable (exponentialConjugateKernel logc w a b) := by
  unfold exponentialConjugateKernel
  fun_prop

/-- The IID sample kernel has hyperparameters n and the sums of the sufficient
statistics, as in the source's conjugacy recipe. -/
theorem exponential_kernel_sample_product {k n : ℕ}
    (logc : Θ → ℝ) (w : Fin k → Θ → ℝ) (T : Fin n → Fin k → ℝ) (θ : Θ) :
    (∏ i, exponentialConjugateKernel logc w 1 (T i) θ) =
      exponentialConjugateKernel logc w n (fun j => ∑ i, T i j) θ := by
  unfold exponentialConjugateKernel
  rw [← Real.exp_sum]
  congr 1
  simp only [one_mul, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

/-- Updating a proper conjugate prior by an exponential-family likelihood
kernel adds the sample size and sufficient statistics to its hyperparameters.
The result includes posterior normalization, not only an exponent identity. -/
theorem exponential_family_conjugacy {k : ℕ}
    (ν : Measure Θ) (logc : Θ → ℝ) (w : Fin k → Θ → ℝ)
    (hc : Measurable logc) (hw : ∀ j, Measurable (w j))
    (a : ℝ) (b : Fin k → ℝ) (n : ℕ) (t : Fin k → ℝ)
    (hiprior : Integrable (exponentialConjugateKernel logc w a b) ν)
    (heprior : 0 < evidence ν (exponentialConjugateKernel logc w a b))
    (hipost : Integrable (exponentialConjugateKernel logc w (a + n) (fun j => b j + t j)) ν)
    (hepost : 0 < evidence ν (exponentialConjugateKernel logc w (a + n) (fun j => b j + t j))) :
    IsProbabilityMeasure (bayesUpdate ν (exponentialConjugateKernel logc w a b)) ∧
    bayesUpdate (bayesUpdate ν (exponentialConjugateKernel logc w a b))
      (exponentialConjugateKernel logc w n t) =
        bayesUpdate ν (exponentialConjugateKernel logc w (a + n) (fun j => b j + t j)) ∧
    IsProbabilityMeasure (bayesUpdate ν
      (exponentialConjugateKernel logc w (a + n) (fun j => b j + t j))) := by
  have hpos (u : ℝ) (v : Fin k → ℝ) (θ : Θ) :
      0 ≤ exponentialConjugateKernel logc w u v θ := (Real.exp_pos _).le
  refine ⟨bayesUpdate_isProbabilityMeasure ν _ hiprior (ae_of_all _ (hpos a b)) heprior,
    ?_, bayesUpdate_isProbabilityMeasure ν _ hipost (ae_of_all _ (hpos _ _)) hepost⟩
  rw [bayesUpdate_sequential ν _ _ (exponentialConjugateKernel_measurable hc hw a b)
    (exponentialConjugateKernel_measurable hc hw n t) (hpos a b) heprior]
  simp_rw [exponential_conjugate_kernel_mul]

end LectureNotes
