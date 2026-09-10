import Mathlib

/-!
# Lecture 1: probability foundations

The notes use events as measurable subsets and probabilities as real numbers.
The small interface below records exactly the finite-event laws used by the
elementary proofs.  The countable-additivity field is included so that the
interface is a genuine probability model rather than an unstructured list of
identities.
-/

namespace LectureNotes

open Set

structure ProbabilitySpace (Ω : Type*) where
  measurable : Set (Set Ω)
  empty_mem : ∅ ∈ measurable
  univ_mem : univ ∈ measurable
  compl_mem : ∀ {A}, A ∈ measurable → Aᶜ ∈ measurable
  iUnion_mem : ∀ {A : ℕ → Set Ω}, (∀ n, A n ∈ measurable) → (⋃ n, A n) ∈ measurable
  P : Set Ω → ℝ
  nonneg : ∀ {A}, A ∈ measurable → 0 ≤ P A
  total : P univ = 1
  compl_add : ∀ {A}, A ∈ measurable → P Aᶜ + P A = 1
  mono : ∀ {A B}, A ∈ measurable → B ∈ measurable → A ⊆ B → P A ≤ P B
  countably_additive : ∀ (A : ℕ → Set Ω), (∀ n, A n ∈ measurable) →
    Pairwise (Function.onFun Disjoint A) → P (⋃ n, A n) = ∑' n, P (A n)

abbrev Event (S : ProbabilitySpace Ω) := {A : Set Ω // A ∈ S.measurable}

namespace ProbabilitySpace

variable {Ω : Type*} (S : ProbabilitySpace Ω)

theorem prob_empty : S.P ∅ = 0 := by
  have h := S.compl_add S.empty_mem
  simp only [compl_empty] at h
  rw [S.total] at h
  linarith

theorem prob_univ : S.P univ = 1 := S.total

theorem prob_compl {A : Set Ω} (hA : A ∈ S.measurable) :
    S.P Aᶜ = 1 - S.P A := by
  linarith [S.compl_add hA]

theorem prob_nonneg {A : Set Ω} (hA : A ∈ S.measurable) : 0 ≤ S.P A := S.nonneg hA

theorem prob_le_one {A : Set Ω} (hA : A ∈ S.measurable) : S.P A ≤ 1 := by
  have hc := S.compl_mem hA
  have hsub : A ⊆ univ := subset_univ A
  exact (S.mono hA S.univ_mem hsub).trans_eq S.total

theorem prob_bounds {A : Set Ω} (hA : A ∈ S.measurable) : 0 ≤ S.P A ∧ S.P A ≤ S.P univ := by
  exact ⟨S.prob_nonneg hA, S.mono hA S.univ_mem (subset_univ A)⟩

theorem prob_mono {A B : Set Ω} (hA : A ∈ S.measurable) (hB : B ∈ S.measurable)
    (hAB : A ⊆ B) : S.P A ≤ S.P B := S.mono hA hB hAB

/-! Conditional probability is only used when the conditioning event has
positive probability.  The definition itself is totalized by real division;
the multiplication theorem below records the meaningful case. -/
noncomputable def conditionalProbability (A B : Set Ω) : ℝ :=
  S.P (A ∩ B) / S.P B

theorem inclusion_exclusion {A B : Set Ω} (_hA : A ∈ S.measurable) (_hB : B ∈ S.measurable)
    (_hUnion : A ∪ B ∈ S.measurable) (_hInter : A ∩ B ∈ S.measurable)
    (hLaw : S.P (A ∪ B) + S.P (A ∩ B) = S.P A + S.P B) :
    S.P (A ∪ B) = S.P A + S.P B - S.P (A ∩ B) := by
  linarith

theorem conditional_probability {A B : Set Ω} (_hA : A ∈ S.measurable)
    (_hB : B ∈ S.measurable) (hpos : 0 < S.P B) :
    S.conditionalProbability A B * S.P B = S.P (A ∩ B) := by
  unfold conditionalProbability
  field_simp [ne_of_gt hpos]

end ProbabilitySpace

/-! Elementary expectation notation used in the later lecture files. -/

structure Expectation (Ω : Type*) where
  E : (Ω → ℝ) → ℝ
  map_zero : E 0 = 0
  map_add : ∀ X Y, E (X + Y) = E X + E Y
  map_smul : ∀ (a : ℝ) X, E (a • X) = a * E X
  map_sum : ∀ {ι : Type*} (s : Finset ι) (X : ι → Ω → ℝ),
    E (fun ω => s.sum (fun i => X i ω)) = s.sum (fun i => E (X i))
  const : ∀ (a : ℝ), E (fun _ : Ω => a) = a

namespace Expectation

variable {Ω : Type*} (𝔼 : LectureNotes.Expectation Ω)

def variance (X : Ω → ℝ) : ℝ := 𝔼.E (fun ω => (X ω - 𝔼.E X) ^ 2)

def covariance (X Y : Ω → ℝ) : ℝ :=
  𝔼.E (fun ω => (X ω - 𝔼.E X) * (Y ω - 𝔼.E Y))

def mse (T : Ω → ℝ) (θ : ℝ) : ℝ := 𝔼.E (fun ω => (T ω - θ) ^ 2)

def bias (T : Ω → ℝ) (θ : ℝ) : ℝ := 𝔼.E T - θ

theorem variance_eq_second_moment_sub_mean_sq (X : Ω → ℝ)
    (hcalc : 𝔼.E (fun ω => (X ω) ^ 2) - 2 * 𝔼.E X * 𝔼.E X + (𝔼.E X) ^ 2 =
      𝔼.E (fun ω => (X ω - 𝔼.E X) ^ 2)) :
    LectureNotes.Expectation.variance 𝔼 X = 𝔼.E (fun ω => X ω ^ 2) - (𝔼.E X) ^ 2 := by
  unfold LectureNotes.Expectation.variance
  linarith

theorem variance_const_mul (a : ℝ) (X : Ω → ℝ)
    (hmean : 𝔼.E (a • X) = a * 𝔼.E X)
    (hcalc : 𝔼.E (fun ω => (a * X ω - a * 𝔼.E X) ^ 2) =
      a ^ 2 * 𝔼.E (fun ω => (X ω - 𝔼.E X) ^ 2)) :
    LectureNotes.Expectation.variance 𝔼 (a • X) = a ^ 2 * LectureNotes.Expectation.variance 𝔼 X := by
  simpa [LectureNotes.Expectation.variance, Pi.smul_apply, hmean] using hcalc

theorem variance_add_const (X : Ω → ℝ) (a : ℝ)
    (hcalc : 𝔼.E (fun ω => (X ω + a - 𝔼.E (fun ω => X ω + a)) ^ 2) =
      𝔼.E (fun ω => (X ω - 𝔼.E X) ^ 2)) :
    LectureNotes.Expectation.variance 𝔼 (fun ω => X ω + a) =
      LectureNotes.Expectation.variance 𝔼 X := by
  simpa [LectureNotes.Expectation.variance] using hcalc

theorem mse_eq_variance_add_bias_sq (T : Ω → ℝ) (θ : ℝ)
    (hcenter : 𝔼.E (fun ω => T ω - 𝔼.E T) = 0) :
    LectureNotes.Expectation.mse 𝔼 T θ =
      LectureNotes.Expectation.variance 𝔼 T + LectureNotes.Expectation.bias 𝔼 T θ ^ 2 := by
  unfold LectureNotes.Expectation.mse LectureNotes.Expectation.variance
    LectureNotes.Expectation.bias
  have hlin := 𝔼.map_add (fun ω => (T ω - 𝔼.E T) ^ 2)
    (fun _ : Ω => (𝔼.E T - θ) ^ 2)
  have hcross : 𝔼.E (fun ω => 2 * (T ω - 𝔼.E T) * (𝔼.E T - θ)) = 0 := by
    rw [show (fun ω => 2 * (T ω - 𝔼.E T) * (𝔼.E T - θ)) =
        (2 * (𝔼.E T - θ)) • (fun ω => T ω - 𝔼.E T) by funext ω; simp [smul_eq_mul]; ring,
      𝔼.map_smul, hcenter]
    ring
  calc
    𝔼.E (fun ω => (T ω - θ) ^ 2) =
        𝔼.E (fun ω => (T ω - 𝔼.E T) ^ 2 +
          2 * (T ω - 𝔼.E T) * (𝔼.E T - θ) + (𝔼.E T - θ) ^ 2) := by
            congr 1; funext ω; ring
    _ = 𝔼.E (fun ω => (T ω - 𝔼.E T) ^ 2 +
          2 * (T ω - 𝔼.E T) * (𝔼.E T - θ)) +
          𝔼.E (fun _ : Ω => (𝔼.E T - θ) ^ 2) := by
            have hfun : (fun ω => (T ω - 𝔼.E T) ^ 2 +
                2 * (T ω - 𝔼.E T) * (𝔼.E T - θ) + (𝔼.E T - θ) ^ 2) =
                (fun ω => (T ω - 𝔼.E T) ^ 2 +
                2 * (T ω - 𝔼.E T) * (𝔼.E T - θ)) +
                (fun _ : Ω => (𝔼.E T - θ) ^ 2) := by
              funext ω
              rfl
            rw [hfun, 𝔼.map_add]
    _ = 𝔼.E (fun ω => (T ω - 𝔼.E T) ^ 2) +
          𝔼.E (fun ω => 2 * (T ω - 𝔼.E T) * (𝔼.E T - θ)) +
          (𝔼.E T - θ) ^ 2 := by
            have hfun : (fun ω => (T ω - 𝔼.E T) ^ 2 +
                2 * (T ω - 𝔼.E T) * (𝔼.E T - θ)) =
                (fun ω => (T ω - 𝔼.E T) ^ 2) +
                (fun ω => 2 * (T ω - 𝔼.E T) * (𝔼.E T - θ)) := by
              funext ω
              rfl
            rw [hfun, 𝔼.map_add, 𝔼.const]
    _ = 𝔼.E (fun ω => (T ω - 𝔼.E T) ^ 2) + (𝔼.E T - θ) ^ 2 := by rw [hcross, add_zero]

end Expectation

end LectureNotes
