import LectureNotes.Estimation

set_option autoImplicit false

/-! L13 decision-theoretic definitions and the finite-parameter admissibility
argument. General losses take values in ℝ≥0∞, avoiding undefined real integrals
and allowing infinite risk. The finite-risk comparison is stated separately. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

def risk {Ω Θ A : Type*} [MeasurableSpace Ω]
    (P : Θ → Measure Ω) (loss : A → Θ → ℝ≥0∞) (δ : Ω → A) (θ : Θ) : ℝ≥0∞ :=
  ∫⁻ x, loss (δ x) θ ∂P θ

def integratedRisk {Ω Θ A : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (P : Θ → Measure Ω) (loss : A → Θ → ℝ≥0∞) (prior : Measure Θ)
    (δ : Ω → A) : ℝ≥0∞ := ∫⁻ θ, risk P loss δ θ ∂prior

def Dominates {D Θ : Type*} {R : Type*} [Preorder R]
    (r : D → Θ → R) (δ ε : D) : Prop :=
  (∀ θ, r δ θ ≤ r ε θ) ∧ ∃ θ, r δ θ < r ε θ

def Admissible {D Θ : Type*} {R : Type*} [Preorder R]
    (r : D → Θ → R) (δ : D) : Prop := ¬ ∃ ε, Dominates r ε δ

def IsBayesRule {D : Type*} {R : Type*} [Preorder R] (r : D → R) (δ : D) : Prop :=
  ∀ ε, r δ ≤ r ε

def worstRisk {D Θ : Type*} (r : D → Θ → ℝ≥0∞) (δ : D) : ℝ≥0∞ := ⨆ θ, r δ θ

def IsMinimax {D Θ : Type*} (r : D → Θ → ℝ≥0∞) (δ : D) : Prop :=
  ∀ ε, worstRisk r δ ≤ worstRisk r ε

theorem dominates_trans {D Θ R : Type*} [PartialOrder R]
    {r : D → Θ → R} {δ ε ζ : D} (hδε : Dominates r δ ε) (hεζ : Dominates r ε ζ) :
    Dominates r δ ζ := by
  refine ⟨fun θ => (hδε.1 θ).trans (hεζ.1 θ), ?_⟩
  obtain ⟨θ, hθ⟩ := hδε.2
  exact ⟨θ, hθ.trans_le (hεζ.1 θ)⟩

theorem dominates_irrefl {D Θ R : Type*} [Preorder R]
    (r : D → Θ → R) (δ : D) : ¬ Dominates r δ δ := by
  rintro ⟨_, θ, hθ⟩
  exact lt_irrefl _ hθ

/-- L13 §1.2: strictly positive prior weights at every parameter and finite
real risks imply admissibility of every Bayes rule. No uniqueness is needed. -/
theorem finite_bayes_admissible {D Θ : Type*} [Fintype Θ]
    (r : D → Θ → ℝ) (w : Θ → ℝ) (hw : ∀ θ, 0 < w θ) (δ : D)
    (hδ : IsBayesRule (fun ε => ∑ θ, w θ * r ε θ) δ) : Admissible r δ := by
  rintro ⟨ε, hle, θ₀, hlt⟩
  have hs : (∑ θ, w θ * r ε θ) < ∑ θ, w θ * r δ θ := by
    apply Finset.sum_lt_sum
    · intro θ _
      exact mul_le_mul_of_nonneg_left (hle θ) (hw θ).le
    · exact ⟨θ₀, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt (hw θ₀)⟩
  exact (not_lt_of_ge (hδ ε)) hs

/-- A rule with pointwise smaller risk inherits minimaxity from a minimax rule. -/
theorem minimax_of_pointwise_le {D Θ : Type*} {r : D → Θ → ℝ≥0∞} {δ ε : D}
    (hδ : IsMinimax r δ) (hε : ∀ θ, r ε θ ≤ r δ θ) : IsMinimax r ε := by
  intro ζ
  exact (iSup_mono hε).trans (hδ ζ)

/-- Under quadratic loss, the posterior mean minimizes posterior expected loss.
Square integrability prevents totalized real integration from hiding divergence. -/
theorem posterior_mean_minimizes_squared_loss {Θ : Type*} [MeasurableSpace Θ]
    (π : Measure Θ) [IsProbabilityMeasure π] {g : Θ → ℝ} (hg : MemLp g 2 π)
    (a : ℝ) :
    (∫ θ, (g θ - ∫ t, g t ∂π) ^ 2 ∂π) ≤ ∫ θ, (g θ - a) ^ 2 ∂π := by
  have h := mse_bias_variance_decomposition π hg a
  change (∫ θ, (g θ - ∫ t, g t ∂π) ^ 2 ∂π) ≤ mse π g a
  rw [h]
  rw [← variance_eq_integral hg.aemeasurable]
  exact le_add_of_nonneg_right (sq_nonneg _)

end LectureNotes
