import LectureNotes.Sampling

namespace LectureNotes

open Finset

/-! Definitions used in Lectures 2, 5, and 6. -/

def Statistic (Ω α : Type*) [MeasurableSpace Ω] [MeasurableSpace α] :=
  {T : Ω → α // Measurable T}

abbrev Estimator (Ω Θ : Type*) [MeasurableSpace Ω] [MeasurableSpace Θ] := Statistic Ω Θ

def Unbiased {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (T : Ω → ℝ) (θ : ℝ) : Prop :=
  MeasureTheory.Integrable T P ∧ (∫ ω, T ω ∂P) = θ

def factorizesThrough {α θ τ : Type*} (f : α → θ → ℝ) (T : α → τ) : Prop :=
  ∃ g : τ → θ → ℝ, ∃ h : α → ℝ, ∀ x p, f x p = g (T x) p * h x

/-- Purely algebraic exponential form. This alone does not say that `f` is
a family of probability densities; use `ExponentialFamily` for that assertion. -/
def HasExponentialForm {α θ : Type*} (f : α → θ → ℝ) (k : ℕ) : Prop :=
  ∃ h : α → ℝ, ∃ c : θ → ℝ, ∃ w : Fin k → θ → ℝ, ∃ t : Fin k → α → ℝ,
    ∀ x p, f x p = h x * c p * Real.exp (∑ j, w j p * t j x)

/-- L5 Definition 2: normalized densities with respect to one reference
measure, with measurable data factors and parameter-independent support.
Counting measure gives the PMF case; Lebesgue measure gives the PDF case. -/
structure ExponentialFamily {α θ : Type*} [MeasurableSpace α]
    (ν : MeasureTheory.Measure α) (f : α → θ → ℝ) (k : ℕ) : Prop where
  integrable : ∀ p, MeasureTheory.Integrable (fun x => f x p) ν
  nonneg : ∀ x p, 0 ≤ f x p
  normalized : ∀ p, (∫ x, f x p ∂ν) = 1
  representation : ∃ h : α → ℝ, ∃ c : θ → ℝ, ∃ w : Fin k → θ → ℝ,
    ∃ t : Fin k → α → ℝ, Measurable h ∧ (∀ j, Measurable (t j)) ∧
      (∀ x, 0 ≤ h x) ∧ (∀ p, 0 < c p) ∧
      ∀ x p, f x p = h x * c p * Real.exp (∑ j, w j p * t j x)

theorem ExponentialFamily.hasExponentialForm {α θ : Type*} [MeasurableSpace α]
    {ν : MeasureTheory.Measure α} {f : α → θ → ℝ} {k : ℕ}
    (hf : ExponentialFamily ν f k) : HasExponentialForm f k := by
  obtain ⟨h, c, w, t, _, _, _, _, he⟩ := hf.representation
  exact ⟨h, c, w, t, he⟩

theorem ExponentialFamily.isProbabilityMeasure {α θ : Type*} [MeasurableSpace α]
    {ν : MeasureTheory.Measure α} {f : α → θ → ℝ} {k : ℕ}
    (hf : ExponentialFamily ν f k) (p : θ) :
    MeasureTheory.IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (f x p))) := by
  constructor
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, MeasureTheory.Measure.restrict_univ,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hf.integrable p)
      (MeasureTheory.ae_of_all _ (fun x => hf.nonneg x p)), hf.normalized p]
  simp

theorem exponential_family_factorizes_sum {α θ : Type*} {k n : ℕ}
    {f : α → θ → ℝ} (h : α → ℝ) (c : θ → ℝ)
    (w : Fin k → θ → ℝ) (t : Fin k → α → ℝ)
    (hf : ∀ x p, f x p = h x * c p * Real.exp (∑ j, w j p * t j x)) :
    factorizesThrough (fun (y : Fin n → α) p => ∏ i, f (y i) p)
      (fun (y : Fin n → α) j => ∑ i, t j (y i)) := by
  let T : (Fin n → α) → (Fin k → ℝ) := fun y j => ∑ i, t j (y i)
  refine ⟨fun s p => (c p) ^ n * Real.exp (∑ j, w j p * s j),
    (fun y => ∏ i, h (y i)), ?_⟩
  intro y p
  calc
    ∏ i, f (y i) p = ∏ i, (h (y i) * c p * Real.exp (∑ j, w j p * t j (y i))) := by
      simp_rw [hf]
    _ = (∏ i, h (y i)) * (∏ _ : Fin n, c p) *
        (∏ i, Real.exp (∑ j, w j p * t j (y i))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = (c p) ^ n * Real.exp (∑ j, w j p * T y j) * ∏ i, h (y i) := by
      simp only [Finset.prod_const, Finset.card_fin]
      rw [← Real.exp_sum]
      dsimp [T]
      simp_rw [Finset.mul_sum]
      have hs : (∑ i : Fin n, ∑ j : Fin k, w j p * t j (y i)) =
          ∑ j : Fin k, ∑ i : Fin n, w j p * t j (y i) := by
        exact Finset.sum_comm
      rw [hs]
      ring

theorem exponential_form_sample_factorization {α θ : Type*} {k n : ℕ}
    {f : α → θ → ℝ} (hf : HasExponentialForm f k) :
    ∃ T : (Fin n → α) → (Fin k → ℝ),
      factorizesThrough (fun y p => ∏ i, f (y i) p) T := by
  obtain ⟨h, c, w, t, hf⟩ := hf
  exact ⟨fun y j => ∑ i, t j (y i), exponential_family_factorizes_sum h c w t hf⟩

theorem exponential_family_sample_factorization {α θ : Type*} [MeasurableSpace α]
    {ν : MeasureTheory.Measure α} {k n : ℕ} {f : α → θ → ℝ}
    (hf : ExponentialFamily ν f k) :
    ∃ T : (Fin n → α) → (Fin k → ℝ),
      factorizesThrough (fun y p => ∏ i, f (y i) p) T :=
  exponential_form_sample_factorization hf.hasExponentialForm

open MeasureTheory ProbabilityTheory

theorem mse_bias_variance_decomposition {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : Ω → ℝ}
    (hT : MemLp T 2 P) (θ : ℝ) :
    mse P T θ = Var[T; P] + bias P T θ ^ 2 :=
  mse_eq_variance_add_bias_sq P hT θ

/-- L5 shrinkage risk; unbiasedness and square integrability are the only
probabilistic assumptions. -/
theorem shrinkage_mse {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {T : Ω → ℝ} (hT : MemLp T 2 P)
    (θ θstar c : ℝ) (hunbiased : P[T] = θ) :
    mse P (fun ω => (1 - c) * T ω + c * θstar) θ =
      c ^ 2 * (θstar - θ) ^ 2 + (1 - c) ^ 2 * Var[T; P] := by
  have ht : MemLp (fun ω => (1 - c) * T ω + c * θstar) 2 P :=
    (hT.const_mul (1 - c)).add (memLp_const (c * θstar))
  rw [mse_eq_variance_add_bias_sq P ht θ]
  rw [variance_add_const (hT.aestronglyMeasurable.const_mul _) _,
    variance_const_mul]
  have hm : P[fun ω => (1 - c) * T ω + c * θstar] =
      (1 - c) * θ + c * θstar := by
    rw [integral_add ((hT.integrable (by norm_num)).const_mul _)
      (integrable_const _), integral_const_mul, hunbiased]
    simp
  unfold bias
  rw [hm]
  ring

end LectureNotes
