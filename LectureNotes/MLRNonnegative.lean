import LectureNotes.MLRExistence

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

namespace StatisticalTest
/-- Complement a randomized rejection rule. -/
def complement {Ω : Type*} [MeasurableSpace Ω] (φ : StatisticalTest Ω) : StatisticalTest Ω where
  reject x := 1 - φ.reject x
  measurable_reject := measurable_const.sub φ.measurable_reject
  nonneg x := sub_nonneg.mpr (φ.le_one x)
  le_one x := by linarith [φ.nonneg x]

theorem complement_densityPower {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (φ : StatisticalTest Ω) {f : Ω → ℝ} (hi : Integrable f ν)
    (hnorm : (∫ x, f x ∂ν) = 1) :
    φ.complement.densityPower ν f = 1 - φ.densityPower ν f := by
  unfold densityPower complement
  simp only
  simp_rw [sub_mul, one_mul]
  rw [integral_sub hi (φ.integrable_mul_density hi), hnorm]

/-- Positive test size requires a point with both positive rejection and
positive null density; null-zero points cannot be the only contributors. -/
theorem positive_densityPower_point {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (φ : StatisticalTest Ω) {f : Ω → ℝ} (hn : ∀ x, 0 ≤ f x)
    (hp : 0 < φ.densityPower ν f) : ∃ x, 0 < φ.reject x ∧ 0 < f x := by
  by_contra h
  push Not at h
  have he (x : Ω) : φ.reject x * f x = 0 := by
    rcases eq_or_lt_of_le (φ.nonneg x) with hx | hx
    · rw [← hx, zero_mul]
    · rw [le_antisymm (h x hx) (hn x), mul_zero]
  simp only [densityPower, he, integral_zero] at hp
  exact (lt_irrefl 0) hp

/-- A threshold exists for nonnegative densities whenever the rule separates
all rejection and acceptance points in likelihood-ratio order. Calibration
strictly between zero and one guarantees a finite threshold, even when the
densities have different supports. -/
theorem likelihood_threshold_of_separated_cross_products
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (φ : StatisticalTest Ω) {f₀ f₁ : Ω → ℝ}
    (h₀ : ∀ x, 0 ≤ f₀ x) (h₁ : ∀ x, 0 ≤ f₁ x)
    (hlo : ∃ x, 0 < φ.reject x ∧ 0 < f₀ x)
    (hhi : ∃ x, φ.reject x < 1 ∧ 0 < f₀ x)
    (hcross : ∀ x y, 0 < φ.reject x → φ.reject y < 1 →
      f₁ y * f₀ x ≤ f₁ x * f₀ y) :
    ∃ k, 0 ≤ k ∧ φ.HasLikelihoodThreshold ν f₀ f₁ k := by
  classical
  obtain ⟨lo, hlo, hlo0⟩ := hlo
  obtain ⟨hi, hhi, hhi0⟩ := hhi
  let r := fun x => f₁ x / f₀ x
  let A : Set ℝ := r '' {x | φ.reject x < 1 ∧ 0 < f₀ x}
  have hA : A.Nonempty := ⟨r hi, hi, ⟨hhi, hhi0⟩, rfl⟩
  have hbdd : BddAbove A := ⟨r lo, by
    rintro a ⟨x, hx, rfl⟩
    exact (div_le_div_iff₀ hx.2 hlo0).mpr (hcross lo x hlo hx.1)⟩
  have hk : 0 ≤ sSup A := (div_nonneg (h₁ hi) hhi0.le).trans
    (le_csSup hbdd ⟨hi, ⟨hhi, hhi0⟩, rfl⟩)
  refine ⟨sSup A, hk, ae_of_all _ (fun x => ?_)⟩
  constructor
  · intro hx
    apply le_antisymm (φ.le_one x)
    by_contra hn
    have hxr : φ.reject x < 1 := lt_of_not_ge hn
    rcases eq_or_lt_of_le (h₀ x) with hx0 | hx0
    · have hcx := hcross lo x hlo hxr
      rw [← hx0, mul_zero] at hcx
      have hf : f₁ x ≤ 0 := by nlinarith
      rw [← hx0, mul_zero] at hx
      linarith
    · have hr : r x ≤ sSup A := le_csSup hbdd ⟨x, ⟨hxr, hx0⟩, rfl⟩
      exact (not_lt_of_ge hr) ((lt_div_iff₀ hx0).mpr hx)
  · intro hx
    apply le_antisymm _ (φ.nonneg x)
    by_contra hn
    have hxr : 0 < φ.reject x := lt_of_not_ge hn
    have hx0 : 0 < f₀ x := by
      by_contra h
      have hz := le_antisymm (le_of_not_gt h) (h₀ x)
      rw [hz, mul_zero] at hx
      linarith [h₁ x]
    have hr : sSup A ≤ r x := csSup_le hA (by
      rintro a ⟨y, hy, rfl⟩
      exact (div_le_div_iff₀ hy.2 hx0).mpr (hcross x y hxr hy.1))
    exact (not_lt_of_ge hr) ((div_lt_iff₀ hx0).mpr hx)

/-- Interior calibration supplies the two support points required by the
nonnegative-density threshold construction. -/
theorem calibrated_cross_product_threshold
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (φ : StatisticalTest Ω) {f₀ f₁ : Ω → ℝ} (hi₀ : Integrable f₀ ν)
    (h₀ : ∀ x, 0 ≤ f₀ x) (h₁ : ∀ x, 0 ≤ f₁ x)
    (hnorm : (∫ x, f₀ x ∂ν) = 1)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hcal : φ.densityPower ν f₀ = α)
    (hcross : ∀ x y, 0 < φ.reject x → φ.reject y < 1 →
      f₁ y * f₀ x ≤ f₁ x * f₀ y) :
    ∃ k, 0 ≤ k ∧ φ.HasLikelihoodThreshold ν f₀ f₁ k := by
  apply φ.likelihood_threshold_of_separated_cross_products h₀ h₁
    (φ.positive_densityPower_point h₀ (by rw [hcal]; exact hα.1)) _ hcross
  obtain ⟨x, hx, hx0⟩ := φ.complement.positive_densityPower_point h₀
    (by rw [φ.complement_densityPower hi₀ hnorm, hcal]; linarith [hα.2])
  exact ⟨x, by change 0 < 1 - φ.reject x at hx; linarith, hx0⟩
end StatisticalTest

/-- Any point with positive lower-tail rejection is no higher in the statistic
than any point with nonzero acceptance. The boundary may be randomized. -/
theorem lowerTailTest_separates {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → ℝ) (hT : Measurable T) (c γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1)
    (x y : Ω) (hx : 0 < (lowerTailTest T hT c γ hγ).reject x)
    (hy : (lowerTailTest T hT c γ hγ).reject y < 1) : T x ≤ T y := by
  have hx' : T x ≤ c := by
    by_contra h
    have hh : c < T x := lt_of_not_ge h
    simp [lowerTailTest, not_lt.mpr hh.le, ne_of_gt hh] at hx
  have hy' : c ≤ T y := by
    by_contra h
    have hh : T y < c := lt_of_not_ge h
    simp [lowerTailTest, hh] at hy
  exact hx'.trans hy'

/-- Ordered cross products imply the power comparison directly, including
size zero and one. Iterated integrals of separated products suffice; no
product-space finiteness assumption or common support is required. -/
theorem cross_product_power_ge_size {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (φ : StatisticalTest Ω) {f₀ f₁ : Ω → ℝ}
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hnorm₀ : (∫ x, f₀ x ∂ν) = 1) (hnorm₁ : (∫ x, f₁ x ∂ν) = 1)
    (hcross : ∀ x y, 0 < φ.reject x → φ.reject y < 1 →
      f₁ y * f₀ x ≤ f₁ x * f₀ y) :
    φ.densityPower ν f₀ ≤ φ.densityPower ν f₁ := by
  let χ := φ.complement
  have hn (x y : Ω) :
      0 ≤ φ.reject x * (f₁ x * (χ.reject y * f₀ y) - f₀ x * (χ.reject y * f₁ y)) := by
    by_cases hx : φ.reject x = 0
    · simp [hx]
    by_cases hy : φ.reject y = 1
    · simp [χ, StatisticalTest.complement, hy]
    have hp := hcross x y (lt_of_le_of_ne (φ.nonneg x) (Ne.symm hx))
      (lt_of_le_of_ne (φ.le_one y) hy)
    have hh := mul_nonneg (mul_nonneg (φ.nonneg x) (χ.nonneg y)) (sub_nonneg.mpr hp)
    nlinarith
  have hh (x : Ω) : 0 ≤ φ.reject x *
      (f₁ x * χ.densityPower ν f₀ - f₀ x * χ.densityPower ν f₁) := by
    have h : 0 ≤ ∫ y, φ.reject x *
        (f₁ x * (χ.reject y * f₀ y) - f₀ x * (χ.reject y * f₁ y)) ∂ν :=
      integral_nonneg (hn x)
    rw [integral_const_mul,
      integral_sub ((χ.integrable_mul_density hi₀).const_mul (f₁ x))
        ((χ.integrable_mul_density hi₁).const_mul (f₀ x)),
      integral_const_mul, integral_const_mul] at h
    exact h
  have h : 0 ≤ ∫ x, φ.reject x *
      (f₁ x * χ.densityPower ν f₀ - f₀ x * χ.densityPower ν f₁) ∂ν :=
    integral_nonneg hh
  have he (x : Ω) : φ.reject x *
      (f₁ x * χ.densityPower ν f₀ - f₀ x * χ.densityPower ν f₁) =
      (φ.reject x * f₁ x) * χ.densityPower ν f₀ -
        (φ.reject x * f₀ x) * χ.densityPower ν f₁ := by ring
  simp_rw [he] at h
  rw [integral_sub ((φ.integrable_mul_density hi₁).mul_const _)
    ((φ.integrable_mul_density hi₀).mul_const _), integral_mul_const, integral_mul_const] at h
  change 0 ≤ φ.densityPower ν f₁ * φ.complement.densityPower ν f₀ -
    φ.densityPower ν f₀ * φ.complement.densityPower ν f₁ at h
  rw [φ.complement_densityPower hi₀ hnorm₀, φ.complement_densityPower hi₁ hnorm₁] at h
  nlinarith

/-- Nonnegative MLR densities give nonincreasing power for every lower-tail
rule, including its endpoint sizes and parameter-dependent supports. -/
theorem mlr_nonnegative_lower_tail_power_antitone
    {Ω Θ : Type*} [MeasurableSpace Ω] [Preorder Θ] {ν : Measure Ω}
    (f : Θ → Ω → ℝ) (T : Ω → ℝ) (hT : Measurable T)
    (hi : ∀ θ, Integrable (f θ) ν) (hnorm : ∀ θ, (∫ x, f θ x ∂ν) = 1)
    (hmlr : HasMonotoneLikelihoodRatio f T)
    (c γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1) :
    Antitone (fun θ => (lowerTailTest T hT c γ hγ).densityPower ν (f θ)) := by
  intro θ₁ θ₂ hθ
  apply cross_product_power_ge_size _ (hi θ₂) (hi θ₁) (hnorm θ₂) (hnorm θ₁)
  intro x y hx hy
  have h := hmlr θ₁ θ₂ hθ x y (lowerTailTest_separates T hT c γ hγ x y hx hy)
  nlinarith

/-- The same nonincreasing power assertion for the actual probability models. -/
theorem mlr_nonnegative_model_power_antitone
    {Ω Θ : Type*} [MeasurableSpace Ω] [Preorder Θ] {ν : Measure Ω}
    (f : Θ → Ω → ℝ) (T : Ω → ℝ) (hT : Measurable T)
    (hi : ∀ θ, Integrable (f θ) ν) (hn : ∀ θ x, 0 ≤ f θ x)
    (hnorm : ∀ θ, (∫ x, f θ x ∂ν) = 1) (hmlr : HasMonotoneLikelihoodRatio f T)
    (c γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1) :
    Antitone (fun θ => (lowerTailTest T hT c γ hγ).power
      (ν.withDensity (fun x => ENNReal.ofReal (f θ x)))) := by
  intro θ₁ θ₂ hθ
  have hb θ := (lowerTailTest T hT c γ hγ).densityPower_eq_power
    (hi θ).aemeasurable (ae_of_all _ (hn θ))
  dsimp only
  rw [← hb θ₂, ← hb θ₁]
  exact mlr_nonnegative_lower_tail_power_antitone f T hT hi hnorm hmlr c γ hγ hθ

/-- L9's calibrated composite-null UMP result for nonnegative densities.
Zeros and changing supports are allowed; likelihood ordering is imposed as
cross products rather than an undefined ratio on those zeros. -/
theorem mlr_nonnegative_lower_tail_ump
    {Ω Θ : Type*} [MeasurableSpace Ω] [LinearOrder Θ] {ν : Measure Ω}
    (f : Θ → Ω → ℝ) (T : Ω → ℝ) (hT : Measurable T)
    (hi : ∀ θ, Integrable (f θ) ν) (hn : ∀ θ x, 0 ≤ f θ x)
    (hnorm : ∀ θ, (∫ x, f θ x ∂ν) = 1) (hmlr : HasMonotoneLikelihoodRatio f T)
    (c γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1) (θ₀ : Θ)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hcal : (lowerTailTest T hT c γ hγ).densityPower ν (f θ₀) = α) :
    (lowerTailTest T hT c γ hγ).IsUMP
      (fun θ => ν.withDensity (fun x => ENNReal.ofReal (f θ x)))
      (Ici θ₀) (Iio θ₀) α := by
  let φ := lowerTailTest T hT c γ hγ
  have bridge (ψ : StatisticalTest Ω) θ := ψ.densityPower_eq_power
    (hi θ).aemeasurable (ae_of_all _ (hn θ))
  have hanti := mlr_nonnegative_lower_tail_power_antitone f T hT hi hnorm hmlr c γ hγ
  constructor
  · intro θ hθ
    rw [← bridge φ θ]
    exact (hanti hθ).trans hcal.le
  · intro ψ hψ θ hθ
    obtain ⟨k, hk, ht⟩ := φ.calibrated_cross_product_threshold (hi θ₀) (hn θ₀)
      (hn θ) (hnorm θ₀) hα hcal (fun x y hx hy => by
        have h := hmlr θ θ₀ hθ.le x y (lowerTailTest_separates T hT c γ hγ x y hx hy)
        nlinarith)
    rw [← bridge ψ θ, ← bridge φ θ]
    apply φ.neyman_pearson ψ (hi θ₀) (hi θ) hk ht
    rw [hcal, bridge ψ θ₀]
    exact hψ θ₀ (mem_Ici.mpr le_rfl)

/-- Exact quantile calibration and MLR optimality for arbitrary nonnegative
normalized densities, including discrete, continuous and mixed statistic laws
and models whose support depends on the parameter. -/
theorem exists_mlr_ump_nonnegative
    {Ω Θ : Type*} [MeasurableSpace Ω] [LinearOrder Θ]
    (ν : Measure Ω) (f : Θ → Ω → ℝ) (T : Ω → ℝ) (hT : Measurable T)
    (hi : ∀ θ, Integrable (f θ) ν) (hn : ∀ θ x, 0 ≤ f θ x)
    (hnorm : ∀ θ, (∫ x, f θ x ∂ν) = 1) (hmlr : HasMonotoneLikelihoodRatio f T)
    (θ₀ : Θ) (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) :
    ∃ c γ, ∃ hγ : γ ∈ Icc (0 : ℝ) 1,
      let φ := lowerTailTest T hT c γ hγ
      φ.densityPower ν (f θ₀) = α ∧
      φ.IsUMP (fun θ => ν.withDensity (fun x => ENNReal.ofReal (f θ x)))
        (Ici θ₀) (Iio θ₀) α := by
  let P := fun θ => ν.withDensity (fun x => ENNReal.ofReal (f θ x))
  letI (θ : Θ) : IsProbabilityMeasure (P θ) :=
    density_model_isProbabilityMeasure (hi θ) (ae_of_all _ (hn θ)) (hnorm θ)
  obtain ⟨c, γ, hγ, hcal⟩ := exists_calibrated_lowerTailTest (P θ₀) T hT α hα
  have hb := (lowerTailTest T hT c γ hγ).densityPower_eq_power
    (hi θ₀).aemeasurable (ae_of_all _ (hn θ₀))
  have hsize : (lowerTailTest T hT c γ hγ).densityPower ν (f θ₀) = α := hb.trans hcal
  exact ⟨c, γ, hγ, hsize, mlr_nonnegative_lower_tail_ump f T hT hi hn hnorm hmlr c γ hγ θ₀ hα hsize⟩

end LectureNotes
