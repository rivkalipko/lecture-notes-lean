import LectureNotes.Sampling

namespace LectureNotes

open Finset

/-! Definitions used in Lectures 2, 5, and 6. -/

def Statistic (Ω α : Type*) := (Ω → α)

def Estimator (Ω Θ : Type*) := Ω → Θ

def Unbiased {Ω Θ : Type*} [AddGroup Θ] (E : (Ω → Θ) → Θ)
    (T : Ω → Θ) (θ : Θ) : Prop := E T = θ

def factorizesThrough {α θ τ : Type*} (f : α → θ → ℝ) (T : α → τ) : Prop :=
  ∃ g : τ → θ → ℝ, ∃ h : α → ℝ, ∀ x p, f x p = g (T x) p * h x

def ExponentialFamily {α θ : Type*} (f : α → θ → ℝ) (k : ℕ) : Prop :=
  ∃ h : α → ℝ, ∃ c : θ → ℝ, ∃ w : Fin k → θ → ℝ, ∃ t : Fin k → α → ℝ,
    ∀ x p, f x p = h x * c p * Real.exp (∑ j, w j p * t j x)

theorem exponential_family_sample_factorization {α θ : Type*} {k n : ℕ}
    {f : α → θ → ℝ} (hf : ExponentialFamily f k) :
    ∃ T : (Fin n → α) → (Fin k → ℝ),
      factorizesThrough (fun y p => ∏ i, f (y i) p) T := by
  rcases hf with ⟨h, c, w, t, hf⟩
  let T : (Fin n → α) → (Fin k → ℝ) := fun y j => ∑ i, t j (y i)
  refine ⟨T, ?_⟩
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

theorem mse_bias_variance_decomposition {Ω : Type*} (𝔼 : Expectation Ω)
    (T : Ω → ℝ) (θ : ℝ) (hcenter : 𝔼.E (fun ω => T ω - 𝔼.E T) = 0) :
    LectureNotes.Expectation.mse 𝔼 T θ =
      LectureNotes.Expectation.variance 𝔼 T + LectureNotes.Expectation.bias 𝔼 T θ ^ 2 :=
  LectureNotes.Expectation.mse_eq_variance_add_bias_sq 𝔼 T θ hcenter

theorem shrinkage_mse {Ω : Type*} (𝔼 : Expectation Ω) (T : Ω → ℝ)
    (θ θstar c : ℝ) (hcenter : 𝔼.E (fun ω => T ω - 𝔼.E T) = 0)
    (hunbiased : 𝔼.E T = θ)
    (hvar : LectureNotes.Expectation.variance 𝔼 T =
      𝔼.E (fun ω => (T ω - θ) ^ 2)) :
    LectureNotes.Expectation.mse 𝔼 (fun ω => (1 - c) * T ω + c * θstar) θ =
      c ^ 2 * (θstar - θ) ^ 2 +
        (1 - c) ^ 2 * LectureNotes.Expectation.variance 𝔼 T := by
  unfold LectureNotes.Expectation.mse at *
  rw [hunbiased] at hcenter
  have hvar2 : 𝔼.E (fun ω => (T ω - θ) ^ 2) =
      𝔼.E (fun ω => (T ω - 𝔼.E T) ^ 2) := by
    simpa only [LectureNotes.Expectation.variance] using hvar.symm
  have hEsub : 𝔼.E (fun ω => T ω - θ) = 0 := by
    simpa [sub_eq_add_neg, ← 𝔼.map_smul (-1) (fun _ : Ω => θ), 𝔼.const] using hcenter
  have hcross : 𝔼.E (fun ω =>
      2 * ((1 - c) * (T ω - θ)) * (c * (θstar - θ))) = 0 := by
    rw [show (fun ω => 2 * ((1 - c) * (T ω - θ)) * (c * (θstar - θ))) =
      (2 * (1 - c) * c * (θstar - θ)) • (fun ω => T ω - θ) by
        funext ω; simp [smul_eq_mul]; ring,
      𝔼.map_smul, hEsub]
    ring
  calc
    𝔼.E (fun ω => ((1 - c) * T ω + c * θstar - θ) ^ 2) =
        𝔼.E (fun ω => ((1 - c) * (T ω - θ) + c * (θstar - θ)) ^ 2) := by
          congr 1; funext ω; ring
    _ = 𝔼.E (fun ω => (1 - c) ^ 2 * (T ω - θ) ^ 2 +
        2 * ((1 - c) * (T ω - θ)) * (c * (θstar - θ)) +
        (c * (θstar - θ)) ^ 2) := by
          congr 1; funext ω; ring
    _ = (1 - c) ^ 2 * 𝔼.E (fun ω => (T ω - θ) ^ 2) +
        𝔼.E (fun ω => 2 * ((1 - c) * (T ω - θ)) * (c * (θstar - θ))) +
        (c * (θstar - θ)) ^ 2 := by
          have hfun : (fun ω => (1 - c) ^ 2 * (T ω - θ) ^ 2 +
              2 * ((1 - c) * (T ω - θ)) * (c * (θstar - θ)) +
              (c * (θstar - θ)) ^ 2) =
              ((fun ω => (1 - c) ^ 2 * (T ω - θ) ^ 2) +
                (fun ω => 2 * ((1 - c) * (T ω - θ)) * (c * (θstar - θ)))) +
                (fun _ : Ω => (c * (θstar - θ)) ^ 2) := by
            funext ω
            rfl
          have hscale : 𝔼.E (fun ω => (1 - c) ^ 2 * (T ω - θ) ^ 2) =
              (1 - c) ^ 2 * 𝔼.E (fun ω => (T ω - θ) ^ 2) := by
            have hfun : (fun ω => (1 - c) ^ 2 * (T ω - θ) ^ 2) =
                ((1 - c) ^ 2) • (fun ω => (T ω - θ) ^ 2) := by
              funext ω
              rfl
            rw [hfun, 𝔼.map_smul]
          rw [hfun, 𝔼.map_add, 𝔼.map_add, hscale, 𝔼.const]
    _ = c ^ 2 * (θstar - θ) ^ 2 +
        (1 - c) ^ 2 * LectureNotes.Expectation.variance 𝔼 T := by
      change (1 - c) ^ 2 * 𝔼.E (fun ω => (T ω - θ) ^ 2) +
        𝔼.E (fun ω => 2 * ((1 - c) * (T ω - θ)) * (c * (θstar - θ))) +
        (c * (θstar - θ)) ^ 2 =
        c ^ 2 * (θstar - θ) ^ 2 +
          (1 - c) ^ 2 * 𝔼.E (fun ω => (T ω - 𝔼.E T) ^ 2)
      rw [hcross, add_zero, hvar2]
      ring

end LectureNotes
