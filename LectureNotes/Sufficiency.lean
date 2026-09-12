import LectureNotes.Estimation

/-! L5 sufficiency and factorization on a finite, positive common support.
This is a restricted theorem: the continuous dominated-model theorem needs
disintegration and common-null-set conditions and is not asserted here. -/
noncomputable section
namespace LectureNotes
open Finset
universe u v w
variable {α : Type u} {Θ : Type v} {τ : Type w} [Fintype α]

def fiberMass (f : α → Θ → ℝ) (T : α → τ) (t : τ) (θ : Θ) : ℝ :=
  by classical exact ∑ x, if T x = t then f x θ else 0
def conditionalMass (f : α → Θ → ℝ) (T : α → τ) (θ : Θ) (x : α) : ℝ :=
  f x θ / fiberMass f T (T x) θ

/-- For each observed statistic, the conditional probability of every point
in its fiber is independent of the parameter. -/
def IsSufficientFinite (f : α → Θ → ℝ) (T : α → τ) : Prop :=
  ∀ θ φ x, conditionalMass f T θ x = conditionalMass f T φ x

theorem fiberMass_pos {f : α → Θ → ℝ} (hf : ∀ x θ, 0 < f x θ)
    (T : α → τ) (x : α) (θ : Θ) : 0 < fiberMass f T (T x) θ := by
  classical
  have hl : f x θ ≤ fiberMass f T (T x) θ := by
    unfold fiberMass
    calc
      f x θ = (if T x = T x then f x θ else 0) := by simp
      _ ≤ ∑ y, if T y = T x then f y θ else 0 := by
        apply single_le_sum (f := fun y => if T y = T x then f y θ else 0)
        · intro y _
          split
          · exact (hf y θ).le
          · exact le_rfl
        · exact mem_univ x
  exact (hf x θ).trans_le hl

theorem finite_factorization_iff [Nonempty Θ] {f : α → Θ → ℝ}
    (hf : ∀ x θ, 0 < f x θ) (T : α → τ) :
    IsSufficientFinite f T ↔ factorizesThrough f T := by
  classical
  constructor
  · intro hs
    let θ₀ : Θ := Classical.choice inferInstance
    refine ⟨fun t θ => fiberMass f T t θ, fun x => conditionalMass f T θ₀ x, ?_⟩
    intro x θ
    change f x θ = fiberMass f T (T x) θ * conditionalMass f T θ₀ x
    rw [← hs θ θ₀ x]
    unfold conditionalMass
    field_simp [(fiberMass_pos hf T x θ).ne']
  · rintro ⟨g, h, hfact⟩ θ φ x
    have hg (p : Θ) : g (T x) p ≠ 0 := by
      intro hz
      have hp := hf x p
      rw [hfact x p, hz, zero_mul] at hp
      exact lt_irrefl _ hp
    have hsum (p : Θ) :
        fiberMass f T (T x) p = g (T x) p * (∑ y, if T y = T x then h y else 0) := by
      unfold fiberMass
      rw [mul_sum]
      apply sum_congr rfl
      intro y _
      by_cases hy : T y = T x
      · simp [hy, hfact]
      · simp [hy]
    unfold conditionalMass
    rw [hfact x θ, hfact x φ, hsum θ, hsum φ,
      mul_div_mul_left _ _ (hg θ), mul_div_mul_left _ _ (hg φ)]

/-- Minimal sufficiency means every sufficient statistic separates at least
the same data fibers. On finite supports this is the usual reduction criterion. -/
def IsMinimalSufficientFinite (f : α → Θ → ℝ) (T : α → τ) : Prop :=
  IsSufficientFinite f T ∧ ∀ (β : Type u) (U : α → β), IsSufficientFinite f U →
    ∀ x y, U x = U y → T x = T y

/-- Same-statistic data have parameter-independent likelihood ratios. -/
theorem sufficient_likelihood_ratio [Nonempty Θ] {f : α → Θ → ℝ}
    (hf : ∀ x θ, 0 < f x θ) {T : α → τ} (hs : IsSufficientFinite f T)
    {x y : α} (hxy : T x = T y) (θ φ : Θ) :
    f x θ / f y θ = f x φ / f y φ := by
  obtain ⟨g, h, hfact⟩ := (finite_factorization_iff hf T).mp hs
  have hg (p : Θ) : g (T y) p ≠ 0 := by
    intro hz
    have hp := hf y p
    rw [hfact y p, hz, zero_mul] at hp
    exact lt_irrefl _ hp
  rw [hfact x θ, hfact y θ, hfact x φ, hfact y φ, hxy,
    mul_div_mul_left _ _ (hg θ), mul_div_mul_left _ _ (hg φ)]

/-- L5 Theorem 4, positive-common-support version. -/
theorem minimal_sufficiency_ratio_criterion [Nonempty Θ] {f : α → Θ → ℝ}
    (hf : ∀ x θ, 0 < f x θ) {T : α → τ} (hs : IsSufficientFinite f T)
    (hcriterion : ∀ x y, (∀ θ φ, f x θ / f y θ = f x φ / f y φ) → T x = T y) :
    IsMinimalSufficientFinite f T := by
  refine ⟨hs, ?_⟩
  intro β U hU x y hxy
  exact hcriterion x y (fun θ φ => sufficient_likelihood_ratio hf hU hxy θ φ)

/-- Parameter-independent likelihood ratios on a fiber imply sufficiency. -/
theorem sufficient_of_likelihood_ratios {f : α → Θ → ℝ}
    (hf : ∀ x θ, 0 < f x θ) (T : α → τ)
    (hr : ∀ x y, T x = T y → ∀ θ φ, f x θ / f y θ = f x φ / f y φ) :
    IsSufficientFinite f T := by
  classical
  intro θ φ x
  unfold conditionalMass
  apply (div_eq_div_iff (fiberMass_pos hf T x θ).ne'
    (fiberMass_pos hf T x φ).ne').2
  unfold fiberMass
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro y _
  by_cases hy : T y = T x
  · simp only [if_pos hy]
    have he := (div_eq_div_iff (hf x θ).ne' (hf x φ).ne').1 (hr y x hy θ φ)
    linarith
  · simp [hy]

theorem finite_minimal_sufficiency [Nonempty Θ] {f : α → Θ → ℝ}
    (hf : ∀ x θ, 0 < f x θ) (T : α → τ)
    (hr : ∀ x y, T x = T y ↔ ∀ θ φ, f x θ / f y θ = f x φ / f y φ) :
    IsMinimalSufficientFinite f T :=
  minimal_sufficiency_ratio_criterion hf
    (sufficient_of_likelihood_ratios hf T (fun x y h => (hr x y).mp h))
    (fun x y h => (hr x y).mpr h)
/-- Finite positive-support instance of L5 Theorem 3. -/
theorem finite_exponential_family_sufficient [Nonempty Θ] {f : α → Θ → ℝ}
    (hf : ∀ x θ, 0 < f x θ) {k n : ℕ} (he : ExponentialFamily f k) :
    ∃ T : (Fin n → α) → (Fin k → ℝ),
      IsSufficientFinite (fun y θ => ∏ i, f (y i) θ) T := by
  obtain ⟨T, hT⟩ := exponential_family_sample_factorization (n := n) he
  exact ⟨T, (finite_factorization_iff (fun y θ => prod_pos (fun i _ => hf (y i) θ)) T).mpr hT⟩
/-- The specific summed statistic printed in L5 Theorem 3, for finite
positive-support data, with the family's representation explicitly given. -/
theorem finite_exponential_family_sum_sufficient [Nonempty Θ] {f : α → Θ → ℝ}
    (hf : ∀ x θ, 0 < f x θ) {k n : ℕ} (h : α → ℝ) (c : Θ → ℝ)
    (w : Fin k → Θ → ℝ) (t : Fin k → α → ℝ)
    (he : ∀ x θ, f x θ = h x * c θ * Real.exp (∑ j, w j θ * t j x)) :
    IsSufficientFinite (fun (y : Fin n → α) θ => ∏ i, f (y i) θ)
      (fun (y : Fin n → α) j => ∑ i, t j (y i)) :=
  (finite_factorization_iff (fun y θ => prod_pos (fun i _ => hf (y i) θ)) _).mpr
    (exponential_family_factorizes_sum h c w t he)
end LectureNotes
