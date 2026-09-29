import LectureNotes.NormalMeansDecision
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

theorem gaussianPDFReal_hasDerivAt (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v)
      (-(x - μ) / v * gaussianPDFReal μ v x) x := by
  have h := (((((hasDerivAt_id x).sub_const μ).pow 2).neg.div_const
    (2 * (v : ℝ))).exp).const_mul (Real.sqrt (2 * Real.pi * v))⁻¹
  convert! h using 1
  dsimp [gaussianPDFReal]
  ring

theorem integrable_gaussian_iff_weighted {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {f : ℝ → ℝ} :
    Integrable f (gaussianReal μ v) ↔ Integrable (fun x => gaussianPDFReal μ v x * f x) := by
  rw [gaussianReal_of_var_ne_zero μ hv]
  have h := integrable_withDensity_iff_integrable_smul'
    (μ := volume) (g := f) (measurable_gaussianPDF μ v) (ae_of_all _ (fun _ => gaussianPDF_lt_top))
  simpa only [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul] using h

/-- Gaussian integration by parts, with all integrability obligations explicit. -/
theorem gaussian_stein_identity {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x)
    (hg : Integrable g (gaussianReal μ v)) (hg' : Integrable g' (gaussianReal μ v))
    (hxg : Integrable (fun x => (x - μ) * g x) (gaussianReal μ v)) :
    (∫ x, (x - μ) * g x ∂gaussianReal μ v) = (v : ℝ) * ∫ x, g' x ∂gaussianReal μ v := by
  have hgw := (integrable_gaussian_iff_weighted hv).mp hg
  have hgw' := (integrable_gaussian_iff_weighted hv).mp hg'
  have hxgw := (integrable_gaussian_iff_weighted hv).mp hxg
  have hleft : Integrable (fun x => g x * (-(x - μ) / v * gaussianPDFReal μ v x)) := by
    convert hxgw.const_mul (-(v : ℝ)⁻¹) using 1
    funext x
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (v := gaussianPDFReal μ v) (u' := g')
    (v' := fun x => -(x - μ) / v * gaussianPDFReal μ v x)
    (fun x _ => hd x) (fun x _ => gaussianPDFReal_hasDerivAt μ v x) hleft
    (by simpa only [Pi.mul_apply, mul_comm] using! hgw')
    (by simpa only [Pi.mul_apply, mul_comm] using! hgw)
  have he x : g x * (-(x - μ) / v * gaussianPDFReal μ v x) =
      -(v : ℝ)⁻¹ * (gaussianPDFReal μ v x * ((x - μ) * g x)) := by ring
  simp_rw [he] at h
  rw [integral_const_mul] at h
  simp_rw [integral_gaussianReal_eq_integral_smul hv, smul_eq_mul]
  have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h' : (v : ℝ)⁻¹ * (∫ x, gaussianPDFReal μ v x * ((x - μ) * g x)) =
      ∫ x, gaussianPDFReal μ v x * g' x := by
    simpa only [neg_mul, neg_inj, mul_comm] using h
  calc
    _ = (v : ℝ) * ((v : ℝ)⁻¹ * (∫ x, gaussianPDFReal μ v x * ((x - μ) * g x))) := by field_simp
    _ = _ := by rw [h']

theorem gaussian_stein_identity_bounded {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x) (hgm : Measurable g')
    {C C' : ℝ} (hg : ∀ x, |g x| ≤ C) (hg' : ∀ x, |g' x| ≤ C') :
    (∫ x, (x - μ) * g x ∂gaussianReal μ v) = (v : ℝ) * ∫ x, g' x ∂gaussianReal μ v := by
  have hm : Measurable g := (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).measurable
  have hgint : Integrable g (gaussianReal μ v) :=
    (integrable_const C).mono' hm.aestronglyMeasurable (ae_of_all _ (by simpa only [Real.norm_eq_abs] using hg))
  have hg'int : Integrable g' (gaussianReal μ v) :=
    (integrable_const C').mono' hgm.aestronglyMeasurable (ae_of_all _ (by simpa only [Real.norm_eq_abs] using hg'))
  apply gaussian_stein_identity hv hd hgint hg'int
  have hx : Integrable (fun x : ℝ => x - μ) (gaussianReal μ v) :=
    ((memLp_id_gaussianReal 2).integrable (by norm_num)).sub (integrable_const μ)
  exact hx.mul_bdd hm.aestronglyMeasurable (ae_of_all _ (by simpa only [Real.norm_eq_abs] using hg))

end LectureNotes
