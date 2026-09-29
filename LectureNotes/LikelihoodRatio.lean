import LectureNotes.EstimationTheory

set_option autoImplicit false

/-! L9–L11 likelihood-ratio and scalar test statistics. Domain hypotheses
guard real suprema, logarithms, and divisions. -/
noncomputable section
namespace LectureNotes
open Set

def likelihoodRatio {Θ Ω : Type*} (L : Ω → Θ → ℝ) (null : Set Θ) (x : Ω) : ℝ :=
  sSup (L x '' null) / sSup (Set.range (L x))

theorem likelihoodRatio_eq_of_maximizers {Θ Ω : Type*} (L : Ω → Θ → ℝ)
    (null : Set Θ) (x : Ω) {t₀ t : Θ} (ht₀ : t₀ ∈ null)
    (h₀ : ∀ θ ∈ null, L x θ ≤ L x t₀) (h : IsMLE L x t) :
    likelihoodRatio L null x = L x t₀ / L x t := by
  unfold likelihoodRatio
  congr 1
  · apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    · exact ⟨L x t₀, mem_image_of_mem _ ht₀⟩
    · rintro _ ⟨θ, hθ, rfl⟩; exact h₀ θ hθ
    · intro b hb; exact ⟨L x t₀, mem_image_of_mem _ ht₀, hb⟩
  · apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    · exact ⟨L x t, mem_range_self t⟩
    · rintro _ ⟨θ, rfl⟩; exact h θ
    · intro b hb; exact ⟨L x t, mem_range_self _, hb⟩

theorem likelihoodRatio_bounds {Θ Ω : Type*} (L : Ω → Θ → ℝ) (null : Set Θ)
    (x : Ω) {t₀ t : Θ} (ht₀ : t₀ ∈ null)
    (h₀ : ∀ θ ∈ null, L x θ ≤ L x t₀) (h : IsMLE L x t)
    (hnonneg : 0 ≤ L x t₀) (hpos : 0 < L x t) :
    likelihoodRatio L null x ∈ Icc (0 : ℝ) 1 := by
  rw [likelihoodRatio_eq_of_maximizers L null x ht₀ h₀ h]
  exact ⟨div_nonneg hnonneg hpos.le, (div_le_one hpos).mpr (h t₀)⟩

theorem minus_two_log_ratio (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    -2 * Real.log (a / b) = 2 * (Real.log b - Real.log a) := by
  rw [Real.log_div ha.ne' hb.ne']; ring

def scalarWald (n estimate null variance : ℝ) : ℝ := n * (estimate - null) ^ 2 / variance
def scalarScoreStatistic (score totalInformation : ℝ) : ℝ := score ^ 2 / totalInformation

/-- L10 Poisson formulas, with sample mean m and null rate λ₀. -/
def poissonLR (n m rate₀ : ℝ) : ℝ := 2 * n * (m * Real.log (m / rate₀) - m + rate₀)
def poissonWald (n m rate₀ : ℝ) : ℝ := n * (m - rate₀) ^ 2 / m
def poissonLM (n m rate₀ : ℝ) : ℝ := n * (m - rate₀) ^ 2 / rate₀

theorem poisson_score_statistic (n m rate₀ : ℝ) (hn : n ≠ 0) (hrate : rate₀ ≠ 0) :
    scalarScoreStatistic (n * (m / rate₀ - 1)) (n / rate₀) = poissonLM n m rate₀ := by
  unfold scalarScoreStatistic poissonLM
  field_simp
  <;> ring

theorem poisson_example_wald : poissonWald 100 5 6 = 20 := by norm_num [poissonWald]
theorem poisson_example_score : poissonLM 100 5 6 = 100 / 6 := by norm_num [poissonLM]

/-- L11 Bernoulli score-test inversion is a quadratic inequality; squaring
retains both tails. The information denominator is positive in the model. -/
theorem bernoulli_score_quadratic (n s p z : ℝ) (hn : 0 < n)
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    (s - n * p) ^ 2 / (n * p * (1 - p)) ≤ z ^ 2 ↔
      (n ^ 2 + z ^ 2 * n) * p ^ 2 - (2 * n * s + z ^ 2 * n) * p + s ^ 2 ≤ 0 := by
  have hd : 0 < n * p * (1 - p) := mul_pos (mul_pos hn hp.1) (sub_pos.mpr hp.2)
  rw [div_le_iff₀ hd]
  constructor <;> intro h <;> nlinarith [h]

end LectureNotes
