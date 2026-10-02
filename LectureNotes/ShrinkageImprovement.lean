import LectureNotes.Estimation

noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory

/-- The exact pointwise range of beneficial shrinkage. The variance is positive;
the shrinkage target can coincide with the true parameter. -/
theorem shrinkage_mse_lt_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : Ω → ℝ}
    (hT : MemLp T 2 P) (θ θstar c : ℝ) (hunbiased : P[T] = θ)
    (hv : 0 < Var[T; P]) :
    mse P (fun ω => (1 - c) * T ω + c * θstar) θ < mse P T θ ↔
      0 < c ∧ c < 2 * Var[T; P] / ((θstar - θ) ^ 2 + Var[T; P]) := by
  have hbase : mse P T θ = Var[T; P] := by
    rw [mse_eq_variance_add_bias_sq P hT θ]
    simp [bias, hunbiased]
  rw [shrinkage_mse P hT θ θstar c hunbiased, hbase]
  have ha : 0 < (θstar - θ) ^ 2 + Var[T; P] := by positivity
  rw [lt_div_iff₀ ha]
  constructor
  · intro h
    have hc : 0 < c := by
      by_contra hn
      have hn' : c ≤ 0 := le_of_not_gt hn
      have hs := mul_nonneg (sq_nonneg c) (le_of_lt ha)
      have hm := mul_nonpos_of_nonpos_of_nonneg hn' (le_of_lt hv)
      nlinarith
    refine ⟨hc, ?_⟩
    have hf : c * (c * ((θstar - θ) ^ 2 + Var[T; P]) - 2 * Var[T; P]) < 0 := by
      nlinarith
    have hneg : c * ((θstar - θ) ^ 2 + Var[T; P]) - 2 * Var[T; P] < 0 := by
      nlinarith
    exact sub_neg.mp hneg
  · rintro ⟨hc, hc'⟩
    have hf := mul_neg_of_pos_of_neg hc (sub_neg.mpr hc')
    nlinarith

/-- A strictly interior improving coefficient always exists pointwise. Its
choice depends on the unknown signal distance and variance. -/
theorem exists_improving_shrinkage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : Ω → ℝ}
    (hT : MemLp T 2 P) (θ θstar : ℝ) (hunbiased : P[T] = θ)
    (hv : 0 < Var[T; P]) :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      mse P (fun ω => (1 - c) * T ω + c * θstar) θ < mse P T θ := by
  let a := (θstar - θ) ^ 2 + Var[T; P]
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨Var[T; P] / (2 * a), ⟨by positivity, ?_⟩, ?_⟩
  · rw [div_lt_one (by positivity)]
    dsimp [a]
    nlinarith [sq_nonneg (θstar - θ)]
  · rw [shrinkage_mse_lt_iff P hT θ θstar _ hunbiased hv]
    refine ⟨by positivity, ?_⟩
    change Var[T; P] / (2 * a) < 2 * Var[T; P] / a
    rw [div_lt_div_iff₀ (by positivity) ha]
    nlinarith [mul_pos hv ha]

/-- Completing the square identifies the unique pointwise oracle coefficient. -/
theorem shrinkage_oracle_risk_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : Ω → ℝ}
    (hT : MemLp T 2 P) (θ θstar c : ℝ) (hunbiased : P[T] = θ)
    (hv : 0 < Var[T; P]) :
    mse P (fun ω => (1 - c) * T ω + c * θstar) θ =
      (θstar - θ) ^ 2 * Var[T; P] / ((θstar - θ) ^ 2 + Var[T; P]) +
        ((θstar - θ) ^ 2 + Var[T; P]) *
          (c - Var[T; P] / ((θstar - θ) ^ 2 + Var[T; P])) ^ 2 := by
  rw [shrinkage_mse P hT θ θstar c hunbiased]
  have ha : (θstar - θ) ^ 2 + Var[T; P] ≠ 0 := ne_of_gt (by positivity)
  field_simp
  <;> ring

/-- The signed shrinkage bias from the source, under actual unbiasedness. -/
theorem shrinkage_bias {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : Ω → ℝ}
    (hT : MemLp T 2 P) (θ θstar c : ℝ) (hunbiased : P[T] = θ) :
    bias P (fun ω => (1 - c) * T ω + c * θstar) θ = c * (θstar - θ) := by
  rw [bias, integral_add ((hT.integrable (by norm_num)).const_mul _) (integrable_const _),
    integral_const_mul, hunbiased, integral_const, probReal_univ, one_smul]
  ring

theorem shrinkage_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : Ω → ℝ}
    (hT : MemLp T 2 P) (θstar c : ℝ) :
    Var[fun ω => (1 - c) * T ω + c * θstar; P] = (1 - c) ^ 2 * Var[T; P] := by
  rw [variance_add_const (hT.aestronglyMeasurable.const_mul _), variance_const_mul]

/-- The risk derivative at zero shrinkage is −2 times the original variance.
Thus its claimed negativity requires strictly positive variance. -/
theorem shrinkage_risk_derivative_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : Ω → ℝ}
    (hT : MemLp T 2 P) (θ θstar : ℝ) (hunbiased : P[T] = θ) :
    HasDerivAt (fun c => mse P (fun ω => (1 - c) * T ω + c * θstar) θ)
      (-2 * Var[T; P]) 0 := by
  have h₁ := ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const ((θstar - θ) ^ 2)
  have h₂ := (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0)).pow 2).mul_const Var[T; P]
  convert! h₁.add h₂ using 1
  · funext c
    exact shrinkage_mse P hT θ θstar c hunbiased
  · norm_num

end LectureNotes
