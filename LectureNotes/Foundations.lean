import Mathlib

/-! # Lecture 1: probability and moments
All probabilities and expectations are Mathlib measures and Bochner integrals.
Linearity has integrability hypotheses; no moment identities are assumed. -/

noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

abbrev Event (Ω : Type*) [MeasurableSpace Ω] := {A : Set Ω // MeasurableSet A}
abbrev RandomVariable (Ω : Type*) [MeasurableSpace Ω] := {X : Ω → ℝ // Measurable X}

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The ratio used for measurable events with positive conditioning
probability. At a null conditioning event Lean returns zero by convention. -/
def conditionalProbability (A B : Set Ω) : ℝ := P.real (A ∩ B) / P.real B
/-- Product independence also handles null events. -/
def IndependentEvents (A B : Set Ω) : Prop :=
  MeasurableSet A ∧ MeasurableSet B ∧ P (A ∩ B) = P A * P B

theorem prob_empty : P.real ∅ = 0 := by simp
theorem prob_univ : P.real univ = 1 := by simp
theorem prob_compl {A : Set Ω} (hA : MeasurableSet A) :
    P.real Aᶜ = 1 - P.real A := probReal_compl_eq_one_sub hA
theorem prob_mono {A B : Set Ω} (hAB : A ⊆ B) : P.real A ≤ P.real B :=
  measureReal_mono hAB
theorem prob_bounds (A : Set Ω) : 0 ≤ P.real A ∧ P.real A ≤ 1 := by
  exact ⟨ENNReal.toReal_nonneg, by simpa using measureReal_mono (μ := P) (subset_univ A)⟩

/-- L1 Theorem 1: derived from countable additivity in the measure API. -/
theorem inclusion_exclusion {A B : Set Ω} (hB : MeasurableSet B) :
    P.real (A ∪ B) = P.real A + P.real B - P.real (A ∩ B) := by
  have h := measureReal_union_add_inter (μ := P) (s := A) hB
  linarith
theorem union_bound (A B : Set Ω) :
    P.real (A ∪ B) ≤ P.real A + P.real B := measureReal_union_le A B
theorem conditional_probability {A B : Set Ω} (hB : P.real B ≠ 0) :
    conditionalProbability P A B * P.real B = P.real (A ∩ B) := by
  exact div_mul_cancel₀ _ hB
theorem bayes {A B : Set Ω} (hA : P.real A ≠ 0) (_hB : P.real B ≠ 0) :
    conditionalProbability P A B =
      conditionalProbability P B A * P.real A / P.real B := by
  rw [conditional_probability P hA, inter_comm]
  rfl
end Probability

section Moments
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- Real expectation, interpreted as a finite expectation when `X` is integrable. -/
def expectation (X : Ω → ℝ) : ℝ := ∫ ω, X ω ∂P
/-- Finite squared-error risk for square-integrable estimators. The totalized
real integral does not represent infinite risk outside this domain. -/
def mse (T : Ω → ℝ) (θ : ℝ) : ℝ := ∫ ω, (T ω - θ) ^ 2 ∂P
def bias (T : Ω → ℝ) (θ : ℝ) : ℝ := P[T] - θ

theorem expectation_const (a : ℝ) : P[fun _ : Ω => a] = a := by simp
theorem expectation_linear {X Y : Ω → ℝ} (hX : Integrable X P) (hY : Integrable Y P)
    (a b : ℝ) : P[fun ω => a * X ω + b * Y ω] = a * P[X] + b * P[Y] := by
  rw [integral_add (hX.const_mul a) (hY.const_mul b), integral_const_mul, integral_const_mul]

theorem expectation_add {X Y : Ω → ℝ} (hX : Integrable X P) (hY : Integrable Y P) :
    P[fun ω => X ω + Y ω] = P[X] + P[Y] := integral_add hX hY
theorem variance_eq_second_moment_sub_mean_sq {X : Ω → ℝ} (hX : MemLp X 2 P) :
    Var[X; P] = (∫ ω, X ω ^ 2 ∂P) - P[X] ^ 2 := variance_eq_sub hX
theorem variance_scale (a : ℝ) {X : Ω → ℝ} (_hX : MemLp X 2 P) :
    Var[fun ω => a * X ω; P] = a ^ 2 * Var[X; P] := variance_const_mul a X P
theorem variance_translate {X : Ω → ℝ} (hX : MemLp X 2 P) (a : ℝ) :
    Var[fun ω => X ω + a; P] = Var[X; P] :=
  variance_add_const hX.aestronglyMeasurable a
theorem zero_variance_is_constant {X : Ω → ℝ} (hX : MemLp X 2 P)
    (hv : Var[X; P] = 0) : X =ᵐ[P] (fun _ => P[X]) :=
  ae_eq_integral_of_variance_eq_zero hX hv

/-- L5 Theorem 1. The centering and second-moment identities are proved. -/
theorem mse_eq_variance_add_bias_sq {T : Ω → ℝ} (hT : MemLp T 2 P) (θ : ℝ) :
    mse P T θ = Var[T; P] + bias P T θ ^ 2 := by
  have hi := hT.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hs := variance_eq_sub (hT.sub (memLp_const θ))
  change Var[fun ω => T ω - θ; P] =
    mse P T θ - (P[fun ω => T ω - θ]) ^ 2 at hs
  rw [variance_sub_const hT.aestronglyMeasurable θ] at hs
  have hm : P[fun ω => T ω - θ] = P[T] - θ := by
    rw [integral_sub hi (integrable_const θ)]
    simp
  change Var[T; P] = mse P T θ - (P[fun ω => T ω - θ]) ^ 2 at hs
  rw [hm] at hs
  dsimp [bias]
  linarith
theorem covariance_eq_product_moment {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    cov[X, Y; P] = (∫ ω, X ω * Y ω ∂P) - P[X] * P[Y] :=
  covariance_eq_sub hX hY
theorem independent_covariance_zero {X Y : Ω → ℝ}
    (h : IndepFun X Y P) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    cov[X, Y; P] = 0 := h.covariance_eq_zero hX hY
theorem variance_of_sum {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    Var[fun ω => X ω + Y ω; P] = Var[X; P] + 2 * cov[X, Y; P] + Var[Y; P] := by
  have h := variance_fun_add hX hY
  linarith
end Moments
end LectureNotes
