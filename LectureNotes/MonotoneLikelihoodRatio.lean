import LectureNotes.NeymanPearson

set_option autoImplicit false

/-! L9 monotone likelihood ratios. The cross-product formulation avoids
division by zero; the power conclusion is non-strict monotonicity. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Increasing likelihood ratio in T as the ordered parameter increases. -/
def HasMonotoneLikelihoodRatio {Θ : Type*} [Preorder Θ]
    (f : Θ → Ω → ℝ) (T : Ω → ℝ) : Prop :=
  ∀ θ₁ θ₂, θ₁ ≤ θ₂ → ∀ x y, T x ≤ T y →
    f θ₂ x * f θ₁ y ≤ f θ₂ y * f θ₁ x

def lowerTailTest (T : Ω → ℝ) (hT : Measurable T) (c γ : ℝ)
    (hγ : γ ∈ Icc (0 : ℝ) 1) : StatisticalTest Ω where
  reject x := if T x < c then 1 else if T x = c then γ else 0
  measurable_reject := Measurable.ite (measurableSet_lt hT measurable_const)
    measurable_const (Measurable.ite (measurableSet_eq_fun hT measurable_const)
      measurable_const measurable_const)
  nonneg x := by split_ifs <;> simp_all
  le_one x := by split_ifs <;> simp_all

/-- MLR gives the Neyman–Pearson threshold for every ordered pair of models.
The cutoff is represented by a sample point z, and densities are positive.
Calibration of this threshold is a separate existence problem. -/
theorem mlr_lower_tail_threshold {Θ : Type*} [Preorder Θ] {ν : Measure Ω}
    (f : Θ → Ω → ℝ) (T : Ω → ℝ) (hT : Measurable T)
    (hpos : ∀ θ x, 0 < f θ x) (hmlr : HasMonotoneLikelihoodRatio f T)
    {θ₁ θ₂ : Θ} (hθ : θ₁ ≤ θ₂) (z : Ω) (γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1) :
    (lowerTailTest T hT (T z) γ hγ).HasLikelihoodThreshold ν (f θ₂) (f θ₁)
      (f θ₁ z / f θ₂ z) := by
  apply ae_of_all
  intro x
  constructor
  · intro hx
    have ht : T x < T z := by
      by_contra hn
      have hm := hmlr θ₁ θ₂ hθ z x (le_of_not_gt hn)
      have hh : f θ₁ z * f θ₂ x < f θ₁ x * f θ₂ z := by
        apply (div_lt_iff₀ (hpos θ₂ z)).mp
        simpa only [div_mul_eq_mul_div] using hx
      nlinarith
    simp [lowerTailTest, ht]
  · intro hx
    have ht : T z < T x := by
      by_contra hn
      have hm := hmlr θ₁ θ₂ hθ x z (le_of_not_gt hn)
      have hh : f θ₁ x * f θ₂ z < f θ₁ z * f θ₂ x := by
        apply (lt_div_iff₀ (hpos θ₂ z)).mp
        simpa only [div_mul_eq_mul_div] using hx
      nlinarith
    simp [lowerTailTest, not_lt.mpr ht.le, ne_of_gt ht]

/-- Any likelihood-threshold test has greater power at the alternative than
at the null. Compare with a constant randomized test of the same null size. -/
theorem threshold_power_ge_size {ν : Measure Ω} (φ : StatisticalTest Ω)
    {f₀ f₁ : Ω → ℝ} (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) (h₁ : (∫ x, f₁ x ∂ν) = 1)
    {k : ℝ} (hk : 0 ≤ k) (hφ : φ.HasLikelihoodThreshold ν f₀ f₁ k) :
    φ.densityPower ν f₀ ≤ φ.densityPower ν f₁ := by
  have ha : 0 ≤ φ.densityPower ν f₀ := integral_nonneg (fun x => mul_nonneg (φ.nonneg x) (hn₀ x))
  have hb : φ.densityPower ν f₀ ≤ 1 := by
    rw [← h₀]
    exact integral_mono (φ.integrable_mul_density hi₀) hi₀ (fun x => by
      simpa using mul_le_mul_of_nonneg_right (φ.le_one x) (hn₀ x))
  let ψ : StatisticalTest Ω := ⟨fun _ => φ.densityPower ν f₀, measurable_const,
    fun _ => ha, fun _ => hb⟩
  have he₀ : ψ.densityPower ν f₀ = φ.densityPower ν f₀ := by
    simp [StatisticalTest.densityPower, ψ, integral_const_mul, h₀]
  have he₁ : ψ.densityPower ν f₁ = φ.densityPower ν f₀ := by
    simp [StatisticalTest.densityPower, ψ, integral_const_mul, h₁]
  simpa only [he₁] using φ.neyman_pearson ψ hi₀ hi₁ hk hφ he₀.le

/-- The non-strict power monotonicity actually justified by L9's proof. -/
theorem mlr_lower_tail_power_antitone {Θ : Type*} [Preorder Θ] {ν : Measure Ω}
    (f : Θ → Ω → ℝ) (T : Ω → ℝ) (hT : Measurable T)
    (hi : ∀ θ, Integrable (f θ) ν) (hpos : ∀ θ x, 0 < f θ x)
    (hnorm : ∀ θ, (∫ x, f θ x ∂ν) = 1) (hmlr : HasMonotoneLikelihoodRatio f T)
    (z : Ω) (γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1) :
    Antitone (fun θ => (lowerTailTest T hT (T z) γ hγ).densityPower ν (f θ)) := by
  intro θ₁ θ₂ hθ
  exact threshold_power_ge_size _ (hi θ₂) (hi θ₁) (fun x => (hpos θ₂ x).le)
    (fun x => (hpos θ₁ x).le) (hnorm θ₂) (hnorm θ₁)
    (div_nonneg (hpos θ₁ z).le (hpos θ₂ z).le)
    (mlr_lower_tail_threshold f T hT hpos hmlr hθ z γ hγ)

/-- L9 Theorem 2, optimality for a calibrated lower-tail test of θ ≥ θ₀
against θ < θ₀. Existence of a calibrating cutoff/tie probability is separate;
the cutoff here lies in the image of T and the model has positive densities. -/
theorem mlr_lower_tail_ump {Θ : Type*} [LinearOrder Θ] {ν : Measure Ω}
    (f : Θ → Ω → ℝ) (T : Ω → ℝ) (hT : Measurable T)
    (hi : ∀ θ, Integrable (f θ) ν) (hpos : ∀ θ x, 0 < f θ x)
    (hnorm : ∀ θ, (∫ x, f θ x ∂ν) = 1) (hmlr : HasMonotoneLikelihoodRatio f T)
    (z : Ω) (γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1) (θ₀ : Θ) (α : ℝ)
    (hcal : (lowerTailTest T hT (T z) γ hγ).densityPower ν (f θ₀) = α) :
    (lowerTailTest T hT (T z) γ hγ).IsUMP
      (fun θ => ν.withDensity (fun x => ENNReal.ofReal (f θ x)))
      (Ici θ₀) (Iio θ₀) α := by
  let φ := lowerTailTest T hT (T z) γ hγ
  have bridge (ψ : StatisticalTest Ω) (θ) := ψ.densityPower_eq_power
    (hi θ).aemeasurable (ae_of_all _ (fun x => (hpos θ x).le))
  have hanti := mlr_lower_tail_power_antitone f T hT hi hpos hnorm hmlr z γ hγ
  constructor
  · intro θ hθ
    rw [← bridge φ θ]
    exact (hanti hθ).trans hcal.le
  · intro ψ hψ θ hθ
    rw [← bridge ψ θ, ← bridge φ θ]
    apply φ.neyman_pearson ψ (hi θ₀) (hi θ)
      (div_nonneg (hpos θ z).le (hpos θ₀ z).le)
      (mlr_lower_tail_threshold f T hT hpos hmlr hθ.le z γ hγ)
    rw [hcal, bridge ψ θ₀]
    exact hψ θ₀ (mem_Ici.mpr le_rfl)

end LectureNotes
