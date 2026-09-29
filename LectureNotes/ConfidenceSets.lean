import LectureNotes.Testing

set_option autoImplicit false

/-! L11: confidence coverage, test inversion, projection, and Pratt's identity.
Expected volume uses a nonnegative integral, so infinite expected lengths are
handled correctly. Joint measurability of the confidence region is explicit. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]

def coverage (P : Θ → Measure Ω) (C : Ω → Set Θ) (θ : Θ) : ℝ :=
  (P θ).real {x | θ ∈ C x}

def HasConfidenceLevel (P : Θ → Measure Ω) (C : Ω → Set Θ) (γ : ℝ) : Prop :=
  ∀ θ, γ ≤ coverage P C θ

/-- Pointwise asymptotic coverage, with θ fixed before the sample-size limit. -/
def HasPointwiseAsymptoticCoverage (P : Θ → Measure Ω)
    (C : ℕ → Ω → Set Θ) (γ : ℝ) : Prop :=
  ∀ θ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, γ - ε ≤ coverage P (C n) θ

/-- Uniform asymptotic coverage uses one eventual sample-size bound for all θ. -/
def HasUniformAsymptoticCoverage (P : Θ → Measure Ω)
    (C : ℕ → Ω → Set Θ) (γ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, ∀ θ, γ - ε ≤ coverage P (C n) θ

theorem uniform_coverage_implies_pointwise {P : Θ → Measure Ω}
    {C : ℕ → Ω → Set Θ} {γ : ℝ} (h : HasUniformAsymptoticCoverage P C γ) :
    HasPointwiseAsymptoticCoverage P C γ := by
  intro θ ε hε
  exact (h ε hε).mono (fun _ hn => hn θ)

def invertTests (R : Θ → Set Ω) (x : Ω) : Set Θ := {θ | x ∉ R θ}

/-- Exact finite-sample duality: level at most α corresponds to coverage at
least 1−α. Neither direction claims exact size from a one-sided bound. -/
theorem test_confidence_duality (P : Θ → Measure Ω)
    [∀ θ, IsProbabilityMeasure (P θ)] (R : Θ → Set Ω)
    (hR : ∀ θ, MeasurableSet (R θ)) (α : ℝ) :
    (∀ θ, (P θ).real (R θ) ≤ α) ↔ HasConfidenceLevel P (invertTests R) (1 - α) := by
  unfold HasConfidenceLevel coverage invertTests
  simp only [mem_setOf_eq]
  have he (θ) : {x | x ∉ R θ} = (R θ)ᶜ := rfl
  simp only [he, measureReal_compl (hR _), probReal_univ]
  constructor <;> intro h θ <;> linarith [h θ]

theorem confidence_projection {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (P θ)]
    (C : Ω → Set Θ) (g : Θ → Ξ) (γ : ℝ) (h : HasConfidenceLevel P C γ) (θ : Θ)
    (_hC : MeasurableSet {x | θ ∈ C x})
    (_hprojected : MeasurableSet {x | g θ ∈ g '' C x}) :
    γ ≤ (P θ).real {x | g θ ∈ g '' C x} := by
  apply (h θ).trans
  refine measureReal_mono ?_ (measure_ne_top (P θ) _)
  intro x hx
  exact mem_image_of_mem g hx

def expectedVolume (P : Measure Ω) (ν : Measure Θ) (C : Ω → Set Θ) : ℝ≥0∞ :=
  ∫⁻ x, ν (C x) ∂P

/-- L11 Theorem 1, first assertion. For Θ = ℝ and ν = volume this is expected
Lebesgue length. Tonelli avoids unnecessary finiteness assumptions. -/
theorem pratt_identity (P : Measure Ω) [SFinite P] (ν : Measure Θ) [SFinite ν]
    (C : Ω → Set Θ) (hC : MeasurableSet {z : Ω × Θ | z.2 ∈ C z.1}) :
    expectedVolume P ν C = ∫⁻ θ, P {x | θ ∈ C x} ∂ν := by
  let f : Ω → Θ → ℝ≥0∞ := fun x θ => (C x).indicator (fun _ => 1) θ
  have hf : Measurable (Function.uncurry f) := by
    exact measurable_const.indicator hC
  have hleft (x : Ω) : (∫⁻ θ, f x θ ∂ν) = ν (C x) := by
    exact lintegral_indicator_one (measurable_prodMk_left hC)
  have hright (θ : Θ) : (∫⁻ x, f x θ ∂P) = P {x | θ ∈ C x} := by
    exact lintegral_indicator_one (measurable_prodMk_right hC)
  simpa only [hleft, hright, expectedVolume] using
    lintegral_lintegral_swap (μ := P) (ν := ν) hf.aemeasurable

/-- The comparison part of Pratt: pointwise acceptance-probability comparison
outside a ν-null set implies the expected-volume comparison. -/
theorem pratt_minimal_expected_volume (P : Measure Ω) [SFinite P]
    (ν : Measure Θ) [SFinite ν] (C D : Ω → Set Θ)
    (hC : MeasurableSet {z : Ω × Θ | z.2 ∈ C z.1})
    (hD : MeasurableSet {z : Ω × Θ | z.2 ∈ D z.1})
    (h : ∀ᵐ θ ∂ν, P {x | θ ∈ C x} ≤ P {x | θ ∈ D x}) :
    expectedVolume P ν C ≤ expectedVolume P ν D := by
  rw [pratt_identity P ν C hC, pratt_identity P ν D hD]
  exact lintegral_mono_ae h

/-- L11 Theorem 1, the UMP consequence. A UMP test is needed for *each*
singleton null. Such tests need not exist, in particular for the usual
unrestricted two-sided normal-mean alternative. -/
theorem pratt_ump_confidence_minimal (P : Θ → Measure Ω)
    [∀ θ, IsProbabilityMeasure (P θ)] (ν : Measure Θ) [SFinite ν]
    [MeasurableSingletonClass Θ] [NullSingletonClass ν]
    (C D : Ω → Set Θ)
    (hC : MeasurableSet {z : Ω × Θ | z.2 ∈ C z.1})
    (hD : MeasurableSet {z : Ω × Θ | z.2 ∈ D z.1}) (α : ℝ)
    (hUMP : ∀ θ, (StatisticalTest.ofRejectionSet {x | θ ∉ C x}
      (measurable_prodMk_right hC).compl).IsUMP P {θ} {θ}ᶜ α)
    (hDlevel : HasConfidenceLevel P D (1 - α)) (θ₀ : Θ) :
    expectedVolume (P θ₀) ν C ≤ expectedVolume (P θ₀) ν D := by
  have hCm (θ : Θ) : MeasurableSet {x | θ ∈ C x} := measurable_prodMk_right hC
  have hDm (θ : Θ) : MeasurableSet {x | θ ∈ D x} := measurable_prodMk_right hD
  apply pratt_minimal_expected_volume (P θ₀) ν C D hC hD
  filter_upwards [ν.ae_ne θ₀] with θ hθ
  let ψ := StatisticalTest.ofRejectionSet {x | θ ∉ D x}
    (measurable_prodMk_right hD).compl
  have hψ : ψ.HasLevel P {θ} α := by
    intro t ht
    have ht' : t = θ := mem_singleton_iff.mp ht
    subst t
    rw [StatisticalTest.power_ofRejectionSet]
    change (P θ).real ({x | θ ∈ D x}ᶜ) ≤ α
    rw [measureReal_compl (hDm θ), probReal_univ]
    have := hDlevel θ
    unfold coverage at this
    linarith
  have hp := (hUMP θ).2 ψ hψ θ₀ (by simpa using Ne.symm hθ)
  dsimp [ψ] at hp
  rw [StatisticalTest.power_ofRejectionSet, StatisticalTest.power_ofRejectionSet] at hp
  change (P θ₀).real ({x | θ ∈ D x}ᶜ) ≤ (P θ₀).real ({x | θ ∈ C x}ᶜ) at hp
  rw [measureReal_compl (hDm θ), measureReal_compl (hCm θ)] at hp
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (P θ₀).real {x | θ ∈ C x} ≤ (P θ₀).real {x | θ ∈ D x}
  linarith

/-- Inverting a location pivot reverses the order of its two endpoints. -/
theorem location_pivot_inversion (t θ a b s : ℝ) (hs : 0 < s) :
    a ≤ (t - θ) / s ∧ (t - θ) / s ≤ b ↔ t - b * s ≤ θ ∧ θ ≤ t - a * s := by
  rw [le_div_iff₀ hs, div_le_iff₀ hs]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem variance_pivot_inversion (v A a b : ℝ) (hv : 0 < v)
    (ha : 0 < a) (hb : 0 < b) :
    a ≤ A / v ∧ A / v ≤ b ↔ A / b ≤ v ∧ v ≤ A / a := by
  rw [le_div_iff₀ hv, div_le_iff₀ hv, div_le_iff₀ hb, le_div_iff₀ ha]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith

end LectureNotes
