import LectureNotes.Quantiles

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- Existence and exact calibration of a Neyman–Pearson test. Null-density
zero points are handled separately, so the alternative need not be absolutely
continuous with respect to the null. The size is strictly between zero and one. -/
theorem exists_neyman_pearson_test {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (f₀ f₁ : Ω → ℝ) (hm₀ : Measurable f₀) (hm₁ : Measurable f₁)
    (hi₀ : Integrable f₀ ν) (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) :
    ∃ k, 0 ≤ k ∧ ∃ φ : StatisticalTest Ω,
      φ.HasLikelihoodThreshold ν f₀ f₁ k ∧ φ.densityPower ν f₀ = α := by
  let P := ν.withDensity (fun x => ENNReal.ofReal (f₀ x))
  letI : IsProbabilityMeasure P := density_model_isProbabilityMeasure hi₀ (ae_of_all _ hn₀) h₀
  let T := fun x => f₁ x / f₀ x
  have hT : Measurable T := hm₁.div hm₀
  have hTpos (x) : 0 ≤ T x := div_nonneg (hn₁ x) (hn₀ x)
  obtain ⟨k, γ, hγ, hcal⟩ := exists_calibrated_lowerTailTest P T hT (1 - α)
    (by constructor <;> linarith [hα.1, hα.2])
  let ψ := lowerTailTest T hT k γ hγ
  have hk : 0 ≤ k := by
    by_contra h
    have hlt : k < 0 := lt_of_not_ge h
    have he (x) : ψ.reject x = 0 := by
      have hx : k < T x := hlt.trans_le (hTpos x)
      simp [ψ, lowerTailTest, not_lt.mpr hx.le, ne_of_gt hx]
    have hz : ψ.power P = 0 := by unfold StatisticalTest.power; simp_rw [he]; simp
    change ψ.power P = 1 - α at hcal
    linarith [hα.2]
  let φ : StatisticalTest Ω := {
    reject := fun x => if f₀ x = 0 then 1 else 1 - ψ.reject x
    measurable_reject := Measurable.ite (measurableSet_eq_fun hm₀ measurable_const)
      measurable_const (measurable_const.sub ψ.measurable_reject)
    nonneg := fun x => by split_ifs; norm_num; exact sub_nonneg.mpr (ψ.le_one x)
    le_one := fun x => by split_ifs; rfl; linarith [ψ.nonneg x] }
  refine ⟨k, hk, φ, ?_, ?_⟩
  · apply ae_of_all
    intro x
    by_cases hz : f₀ x = 0
    · constructor
      · intro _; simp [φ, hz]
      · intro h; have := hn₁ x; simp only [hz, mul_zero] at h; linarith
    · have hp : 0 < f₀ x := lt_of_le_of_ne (hn₀ x) (Ne.symm hz)
      constructor
      · intro h
        have hx : k < T x := (lt_div_iff₀ hp).mpr h
        simp [φ, hz, ψ, lowerTailTest, not_lt.mpr hx.le, ne_of_gt hx]
      · intro h
        have hx : T x < k := (div_lt_iff₀ hp).mpr h
        simp [φ, hz, ψ, lowerTailTest, hx]
  · have he (x) : φ.reject x * f₀ x = f₀ x - ψ.reject x * f₀ x := by
      dsimp [φ]
      split_ifs with h
      · simp [h]
      · ring
    unfold StatisticalTest.densityPower
    simp_rw [he]
    rw [integral_sub hi₀ (ψ.integrable_mul_density hi₀), h₀]
    have hb := ψ.densityPower_eq_power (ν := ν) hm₀.aemeasurable (ae_of_all _ hn₀)
    change ψ.densityPower ν f₀ = ψ.power P at hb
    change 1 - ψ.densityPower ν f₀ = α
    rw [hb]
    change ψ.power P = 1 - α at hcal
    linarith

/-- The existence and comparison parts together give an exactly sized test
maximizing alternative power over every test of size at most α. -/
theorem exists_most_powerful_test {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (f₀ f₁ : Ω → ℝ) (hm₀ : Measurable f₀) (hm₁ : Measurable f₁)
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) :
    ∃ φ : StatisticalTest Ω, φ.densityPower ν f₀ = α ∧
      ∀ ψ : StatisticalTest Ω, ψ.densityPower ν f₀ ≤ α →
        ψ.densityPower ν f₁ ≤ φ.densityPower ν f₁ := by
  obtain ⟨k, hk, φ, hφ, hsize⟩ := exists_neyman_pearson_test ν f₀ f₁ hm₀ hm₁ hi₀ hn₀ hn₁ h₀ α hα
  refine ⟨φ, hsize, fun ψ hψ => ?_⟩
  exact φ.neyman_pearson ψ hi₀ hi₁ hk hφ (hψ.trans hsize.ge)

end LectureNotes
