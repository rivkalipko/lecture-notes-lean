import LectureNotes.NormalUMPNonexistence
import LectureNotes.NormalHighestDensity
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace StatisticalTest
/-- Uniformly most powerful among unbiased tests of the given level. -/
def IsUMPU {Ω Θ : Type*} [MeasurableSpace Ω] (φ : StatisticalTest Ω)
    (P : Θ → Measure Ω) (null alternative : Set Θ) (α : ℝ) : Prop :=
  φ.HasLevel P null α ∧ φ.IsUnbiased P null alternative ∧
    ∀ ψ : StatisticalTest Ω, ψ.HasLevel P null α → ψ.IsUnbiased P null alternative →
      ∀ θ ∈ alternative, ψ.power (P θ) ≤ φ.power (P θ)

/-- Neyman–Pearson with one additional equal-moment constraint. The second
coefficient has either sign; only the coefficient of the size constraint
must be nonnegative. -/
theorem neyman_pearson_equal_moment {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} (φ ψ : StatisticalTest Ω) {f₀ f₁ g : Ω → ℝ}
    (h₀ : Integrable f₀ ν) (h₁ : Integrable f₁ ν) (hg : Integrable g ν)
    (A B : ℝ) (hA : 0 ≤ A)
    (hthreshold : φ.HasLikelihoodThreshold ν (fun x => A * f₀ x + B * g x) f₁ 1)
    (hsize : ψ.densityPower ν f₀ ≤ φ.densityPower ν f₀)
    (hmoment : ψ.densityPower ν g = φ.densityPower ν g) :
    ψ.densityPower ν f₁ ≤ φ.densityPower ν f₁ := by
  apply φ.neyman_pearson ψ ((h₀.const_mul A).add (hg.const_mul B)) h₁ zero_le_one hthreshold
  have he (χ : StatisticalTest Ω) :
      χ.densityPower ν (fun x => A * f₀ x + B * g x) =
        A * χ.densityPower ν f₀ + B * χ.densityPower ν g := by
    unfold densityPower
    simp_rw [mul_add, mul_left_comm (χ.reject _) A, mul_left_comm (χ.reject _) B]
    rw [integral_add ((χ.integrable_mul_density h₀).const_mul A)
      ((χ.integrable_mul_density hg).const_mul B), integral_const_mul, integral_const_mul]
  change ψ.densityPower ν (fun x => A * f₀ x + B * g x) ≤
    φ.densityPower ν (fun x => A * f₀ x + B * g x)
  rw [he, he, hmoment]
  exact add_le_add (mul_le_mul_of_nonneg_left hsize hA) le_rfl
end StatisticalTest

/-- The secant through the two symmetric boundary points. -/
def symmetricSecant (f : ℝ → ℝ) (c x : ℝ) : ℝ :=
  (f (-c) + f c) / 2 + (f c - f (-c)) / (2 * c) * x

private theorem symmetricSecant_mul (f : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    (2 * c) * symmetricSecant f c x = (c - x) * f (-c) + (c + x) * f c := by
  unfold symmetricSecant
  field_simp
  ring

/-- A convex function lies below its secant inside the two boundary points,
and above the extended secant outside them. -/
theorem convex_symmetric_secant_sign {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    {c : ℝ} (hc : 0 < c) (x : ℝ) :
    (|x| ≤ c → f x ≤ symmetricSecant f c x) ∧
      (c ≤ |x| → symmetricSecant f c x ≤ f x) := by
  have he := symmetricSecant_mul f hc x
  have hc2 : 0 < 2 * c := by positivity
  constructor
  · intro hx
    rcases abs_le.mp hx with ⟨hl, hr⟩
    rcases eq_or_lt_of_le hl with h | hl
    · subst x
      nlinarith
    rcases eq_or_lt_of_le hr with h | hr
    · subst x
      nlinarith
    have h := hf.secant_mono_aux1 (by trivial) (by trivial) hl hr
    nlinarith
  · intro hx
    rcases le_abs.mp hx with hl | hr
    · rcases eq_or_lt_of_le hl with h | hl
      · subst x
        nlinarith
      have h := hf.secant_mono_aux1 (by trivial) (by trivial) (by linarith : -c < c) hl
      nlinarith
    · rcases eq_or_lt_of_le hr with h | hr
      · have hx : x = -c := by linarith
        subst x
        nlinarith
      have h := hf.secant_mono_aux1 (by trivial) (by trivial) (by linarith : x < -c)
        (by linarith : -c < c)
      nlinarith

/-- Exponential likelihood ratios are convex even when their slope is negative. -/
theorem convexOn_exp_affine (a b : ℝ) :
    ConvexOn ℝ univ (fun x : ℝ => Real.exp (a * x + b)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  have h := convexOn_exp.2 (mem_univ (a * x + b)) (mem_univ (a * y + b)) hs ht hst
  simp only [smul_eq_mul] at h ⊢
  convert h using 1
  congr 1
  linear_combination -b * hst

/-- The symmetric two-tail rejection rule. -/
def gaussianTwoTail (θ₀ c : ℝ) : StatisticalTest ℝ :=
  StatisticalTest.ofRejectionSet {x | c < |x - θ₀|}
    (measurableSet_lt measurable_const ((measurable_id.sub_const θ₀).abs))

/-- Reflection about the null mean leaves this rejection rule unchanged. -/
theorem gaussianTwoTail_reflect (θ₀ c x : ℝ) :
    (gaussianTwoTail θ₀ c).reject (2 * θ₀ - x) = (gaussianTwoTail θ₀ c).reject x := by
  have he : |2 * θ₀ - x - θ₀| = |x - θ₀| := by
    rw [show 2 * θ₀ - x - θ₀ = -(x - θ₀) by ring, abs_neg]
  simp [gaussianTwoTail, StatisticalTest.ofRejectionSet, Set.indicator, he]

/-- The central Gaussian interval gives the exact size of the calibrated rule. -/
theorem gaussianTwoTail_quantile_size (θ₀ : ℝ) {v : ℝ≥0} (hv : 0 < v)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    (gaussianTwoTail θ₀ (distributionQuantile (gaussianReal 0 1) (1 - α / 2) *
      Real.sqrt v)).power (gaussianReal θ₀ v) = α := by
  let c := distributionQuantile (gaussianReal 0 1) (1 - α / 2) * Real.sqrt v
  have he : {x : ℝ | c < |x - θ₀|} = (Icc (θ₀ - c) (θ₀ + c))ᶜ := by
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_Icc, ← not_le, abs_le]
    constructor
    · contrapose!
      rintro ⟨h₁, h₂⟩
      constructor <;> linarith
    · contrapose!
      rintro ⟨h₁, h₂⟩
      constructor <;> linarith
  rw [gaussianTwoTail, StatisticalTest.power_ofRejectionSet, he,
    measureReal_compl measurableSet_Icc, probReal_univ,
    (gaussian_equalTailed_minimum_volume θ₀ v hv hα).1]
  ring

/-- The rejection rule has zero first centered moment under the null law. -/
theorem gaussianTwoTail_centered_moment (θ₀ c : ℝ) (v : ℝ≥0) :
    (∫ x, (gaussianTwoTail θ₀ c).reject x * (x - θ₀) ∂gaussianReal θ₀ v) = 0 := by
  have hR : HasLaw (fun x : ℝ => 2 * θ₀ - x) (gaussianReal θ₀ v)
      (gaussianReal θ₀ v) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [show 2 * θ₀ - θ₀ = θ₀ by ring] using
      gaussianReal_map_const_sub (μ := θ₀) (v := v) (2 * θ₀)
  have hmeas : Measurable (fun x => (gaussianTwoTail θ₀ c).reject x * (x - θ₀)) :=
    (gaussianTwoTail θ₀ c).measurable_reject.mul (measurable_id.sub_const θ₀)
  have h := hR.integral_comp hmeas.aestronglyMeasurable
  have he (x : ℝ) :
      (gaussianTwoTail θ₀ c).reject (2 * θ₀ - x) * (2 * θ₀ - x - θ₀) =
        -((gaussianTwoTail θ₀ c).reject x * (x - θ₀)) := by
    rw [gaussianTwoTail_reflect]
    ring
  simp only [Function.comp_apply, he, integral_neg] at h
  linarith

/-- The density-weighted centered coordinate is integrable. -/
theorem gaussian_centered_density_integrable (θ₀ : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    Integrable (fun x : ℝ => (x - θ₀) * gaussianPDFReal θ₀ v x) volume := by
  have hi : Integrable (fun x : ℝ => x - θ₀) (gaussianReal θ₀ v) :=
    ((memLp_id_gaussianReal 1).integrable (by norm_num)).sub (integrable_const θ₀)
  rw [gaussianReal_of_var_ne_zero θ₀ hv.ne'] at hi
  have h := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF θ₀ v) (ae_of_all _ (fun _ => gaussianPDF_lt_top))).mp hi
  simpa only [toReal_gaussianPDF, smul_eq_mul, mul_comm] using h

/-- Convert the density-weighted moment to its null-distribution expectation. -/
theorem gaussian_centered_densityPower (ψ : StatisticalTest ℝ) (θ₀ : ℝ)
    {v : ℝ≥0} (hv : 0 < v) :
    ψ.densityPower volume (fun x => (x - θ₀) * gaussianPDFReal θ₀ v x) =
      ∫ x, ψ.reject x * (x - θ₀) ∂gaussianReal θ₀ v := by
  rw [integral_gaussianReal_eq_integral_smul hv.ne']
  unfold StatisticalTest.densityPower
  congr 1
  ext x
  simp only [smul_eq_mul]
  ring

/-- The symmetric normal test maximizes power under a size budget and a zero
null-score moment. These are consequences of level and unbiasedness below. -/
theorem gaussianTwoTail_most_powerful_zero_moment (θ₀ θ₁ : ℝ)
    {v : ℝ≥0} (hv : 0 < v) {c : ℝ} (hc : 0 < c) (ψ : StatisticalTest ℝ)
    (hsize : ψ.power (gaussianReal θ₀ v) ≤ (gaussianTwoTail θ₀ c).power (gaussianReal θ₀ v))
    (hmoment : (∫ x, ψ.reject x * (x - θ₀) ∂gaussianReal θ₀ v) = 0) :
    ψ.power (gaussianReal θ₁ v) ≤ (gaussianTwoTail θ₀ c).power (gaussianReal θ₁ v) := by
  let f : ℝ → ℝ := fun z => Real.exp ((θ₁ - θ₀) / v * z - (θ₁ - θ₀) ^ 2 / (2 * v))
  let A : ℝ := (f (-c) + f c) / 2
  let B : ℝ := (f c - f (-c)) / (2 * c)
  have hA : 0 ≤ A := by dsimp [A, f]; positivity
  have hf : ConvexOn ℝ univ f := by
    simpa only [f, sub_eq_add_neg] using
      convexOn_exp_affine ((θ₁ - θ₀) / v) (-((θ₁ - θ₀) ^ 2 / (2 * v)))
  have hratio (x : ℝ) : gaussianPDFReal θ₁ v x = f (x - θ₀) * gaussianPDFReal θ₀ v x := by
    apply (div_eq_iff (gaussianPDFReal_pos θ₀ v x hv.ne').ne').mp
    rw [gaussian_density_ratio hv]
    dsimp [f]
    congr 1
    ring
  have ht : (gaussianTwoTail θ₀ c).HasLikelihoodThreshold volume
      (fun x => A * gaussianPDFReal θ₀ v x + B * ((x - θ₀) * gaussianPDFReal θ₀ v x))
      (gaussianPDFReal θ₁ v) 1 := by
    apply ae_of_all
    intro x
    have he : A * gaussianPDFReal θ₀ v x + B * ((x - θ₀) * gaussianPDFReal θ₀ v x) =
        symmetricSecant f c (x - θ₀) * gaussianPDFReal θ₀ v x := by
      dsimp [A, B, symmetricSecant]
      ring
    have hp := gaussianPDFReal_pos θ₀ v x hv.ne'
    have hs := convex_symmetric_secant_sign hf hc (x - θ₀)
    dsimp only
    rw [one_mul, he, hratio, mul_lt_mul_iff_left₀ hp, mul_lt_mul_iff_left₀ hp]
    constructor
    · intro h
      have hx : c < |x - θ₀| := lt_of_not_ge (fun hx => (not_lt_of_ge (hs.1 hx)) h)
      simp [gaussianTwoTail, StatisticalTest.ofRejectionSet, Set.indicator, hx]
    · intro h
      have hx : ¬ c < |x - θ₀| := fun hx => (not_lt_of_ge (hs.2 hx.le)) h
      simp [gaussianTwoTail, StatisticalTest.ofRejectionSet, Set.indicator, hx]
  have hm : ψ.densityPower volume (fun x => (x - θ₀) * gaussianPDFReal θ₀ v x) =
      (gaussianTwoTail θ₀ c).densityPower volume (fun x => (x - θ₀) * gaussianPDFReal θ₀ v x) := by
    rw [gaussian_centered_densityPower ψ θ₀ hv, gaussian_centered_densityPower _ θ₀ hv,
      hmoment, gaussianTwoTail_centered_moment]
  simpa only [gaussian_densityPower _ _ hv] using
    (gaussianTwoTail θ₀ c).neyman_pearson_equal_moment ψ
      (integrable_gaussianPDFReal θ₀ v) (integrable_gaussianPDFReal θ₁ v)
      (gaussian_centered_density_integrable θ₀ hv) A B hA ht
      (by simpa only [gaussian_densityPower _ _ hv] using hsize) hm

/-- Its power is at least its null size at every mean: comparison with a
constant randomized test proves unbiasedness without a power approximation. -/
theorem gaussianTwoTail_unbiased (θ₀ : ℝ) {v : ℝ≥0} (hv : 0 < v)
    {c : ℝ} (hc : 0 < c) :
    (gaussianTwoTail θ₀ c).IsUnbiased (fun θ => gaussianReal θ v)
      {θ₀} {θ | θ ≠ θ₀} := by
  let α := (gaussianTwoTail θ₀ c).power (gaussianReal θ₀ v)
  have ha : α ∈ Icc (0 : ℝ) 1 :=
    ⟨(gaussianTwoTail θ₀ c).power_nonneg _, (gaussianTwoTail θ₀ c).power_le_one _⟩
  let coin : StatisticalTest ℝ :=
    ⟨fun _ => α, measurable_const, fun _ => ha.1, fun _ => ha.2⟩
  have hcoin (θ : ℝ) : coin.power (gaussianReal θ v) = α := by
    simp [coin, StatisticalTest.power]
  refine ⟨α, ha, ?_, ?_⟩
  · intro θ hθ
    simpa only [mem_singleton_iff.mp hθ] using le_refl α
  · intro θ _
    rw [← hcoin θ]
    apply gaussianTwoTail_most_powerful_zero_moment θ₀ θ hv hc coin
    · exact (hcoin θ₀).le
    · change (∫ x, α * (x - θ₀) ∂gaussianReal θ₀ v) = 0
      have hi : Integrable (fun x : ℝ => x) (gaussianReal θ₀ v) :=
        (memLp_id_gaussianReal 1).integrable (by norm_num)
      rw [integral_const_mul, integral_sub hi (integrable_const θ₀)]
      simp

end LectureNotes
