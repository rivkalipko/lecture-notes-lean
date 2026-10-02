import LectureNotes.NormalHighestDensity

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- Standard normal CDF reflection, with atomlessness justifying the choice
of open or closed boundary at the reflected cutoff. -/
theorem standardNormal_cdf_neg (x : ℝ) :
    cdf (gaussianReal 0 1) (-x) = 1 - cdf (gaussianReal 0 1) x := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have h := cdf_map_strictAnti (gaussianReal 0 1)
    (show StrictAnti (fun x : ℝ => -x) from fun _ _ h => neg_lt_neg h) x
  simpa only [gaussianReal_map_neg, neg_zero] using h

/-- Exact power of the two-sided standardized normal test, retaining both
of the source formula's tails. -/
theorem normal_two_sided_power_symmetric {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → ℝ} {δ c : ℝ}
    (hm : Measurable T) (hT : HasLaw T (gaussianReal δ 1) P) (hc : 0 ≤ c) :
    P.real {ω | c < |T ω|} =
      cdf (gaussianReal 0 1) (δ - c) + cdf (gaussianReal 0 1) (-δ - c) := by
  have he : {ω | c < |T ω|} = {ω | T ω < -c ∨ c < T ω} := by
    ext ω
    simp only [mem_ofPred_eq, lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  rw [he, normal_two_sided_power (by norm_num) hm hT (-c) c (by linarith)]
  simp only [NNReal.coe_one, Real.sqrt_one, div_one]
  have hs := standardNormal_cdf_neg (δ - c)
  rw [show -(δ - c) = c - δ by ring] at hs
  rw [hs, show -c - δ = -δ - c by ring]
  ring

/-- Dropping the far tail yields a lower bound on exact two-sided normal
power. It is not an equality at nonzero or zero effects. -/
theorem normal_two_sided_power_dominant_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → ℝ} {δ c : ℝ}
    (hm : Measurable T) (hT : HasLaw T (gaussianReal δ 1) P) (hc : 0 ≤ c) :
    cdf (gaussianReal 0 1) (|δ| - c) ≤ P.real {ω | c < |T ω|} := by
  rw [normal_two_sided_power_symmetric hm hT hc]
  by_cases hδ : 0 ≤ δ
  · rw [abs_of_nonneg hδ]
    exact le_add_of_nonneg_right (cdf_nonneg _ _)
  · rw [abs_of_neg (lt_of_not_ge hδ)]
    exact le_add_of_nonneg_left (cdf_nonneg _ _)

/-- The common sample-size approximation is a sufficient condition for the
exact normal power target, since the omitted tail has nonnegative mass. -/
theorem normal_two_sided_power_sufficient {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → ℝ} {δ c q : ℝ}
    (hm : Measurable T) (hT : HasLaw T (gaussianReal δ 1) P) (hc : 0 ≤ c)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (heffect : c + distributionQuantile (gaussianReal 0 1) q ≤ |δ|) :
    q ≤ P.real {ω | c < |T ω|} := by
  apply le_trans _ (normal_two_sided_power_dominant_tail hm hT hc)
  exact (distributionQuantile_le_iff _ hq).mp (by linarith)

/-- Squaring the design inequality is valid only with a nonnegative target,
a positive standard deviation and a nonzero effect. -/
theorem normal_sample_size_rule (n : ℕ) {σ τ z : ℝ}
    (hσ : 0 < σ) (hτ : τ ≠ 0) (hz : 0 ≤ z) :
    z ≤ Real.sqrt n * |τ| / σ ↔ z ^ 2 * σ ^ 2 / τ ^ 2 ≤ (n : ℝ) := by
  rw [le_div_iff₀ hσ, ← sq_le_sq₀ (mul_nonneg hz hσ.le)
    (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))]
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), sq_abs,
    div_le_iff₀ (sq_pos_of_ne_zero hτ)]

/-- The same design inequality solved for the magnitude of the effect. -/
theorem normal_minimum_detectable_effect (n : ℕ) (hn : 0 < n)
    {σ τ z : ℝ} (hσ : 0 < σ) :
    z ≤ Real.sqrt n * |τ| / σ ↔ z * σ / Real.sqrt n ≤ |τ| := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  rw [le_div_iff₀ hσ, div_le_iff₀ hs]
  ring_nf

/-- Halving the target effect quadruples the displayed sample-size bound. -/
theorem normal_sample_size_halved_effect (σ τ z : ℝ) :
    z ^ 2 * σ ^ 2 / (τ / 2) ^ 2 = 4 * (z ^ 2 * σ ^ 2 / τ ^ 2) := by
  ring

/-- An equally allocated two-group design with total size 2m has standard
error 2σ/√(2m), for independent means with common observation variance σ². -/
theorem balanced_two_group_standard_error (m : ℕ) (hm : 0 < m)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    Real.sqrt (σ ^ 2 / m + σ ^ 2 / m) = 2 * σ / Real.sqrt (2 * (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hs : 0 < Real.sqrt (2 * (m : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity), div_pow, mul_pow,
    Real.sq_sqrt (by positivity)]
  field_simp
  ring

end LectureNotes
