import LectureNotes.ConditionalDensities
import Mathlib.Probability.HasLaw

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

section General
variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace β] [Nonempty β]
    {P : Measure Ω} [IsFiniteMeasure P]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {X : Ω → α} {Y : Ω → β} (hX : Measurable X) (hY : Measurable Y)
include hX hY

theorem joint_density_first_marginal {f : α × β → ℝ≥0∞} (hf : Measurable f)
    (hXY : HasLaw (fun ω => (X ω, Y ω)) ((μ.prod ν).withDensity f) P) :
    P.map X = μ.withDensity (marginalDensity ν f) := by
  calc
    P.map X = (P.map (fun ω => (X ω, Y ω))).map Prod.fst := by
      rw [Measure.map_map measurable_fst (hX.prodMk hY)]
      rfl
    _ = _ := by rw [hXY.map_eq, density_map_fst μ ν hf]

/-- Conditional densities transported from the joint law to random variables
on an arbitrary probability space. The equality is under the actual X-law. -/
theorem conditional_density_ratio_of_hasLaw {f : α × β → ℝ≥0∞} (hf : Measurable f)
    (hXY : HasLaw (fun ω => (X ω, Y ω)) ((μ.prod ν).withDensity f) P) :
    condDistrib Y X P =ᵐ[P.map X]
      (fun x => ν.withDensity (fun y => f (x, y) / marginalDensity ν f x)) := by
  have : IsFiniteMeasure ((μ.prod ν).withDensity f) := hXY.isFiniteMeasure_iff.mp inferInstance
  have hfin : (∫⁻ z, f z ∂μ.prod ν) ≠ ∞ := by
    have h := measure_ne_top ((μ.prod ν).withDensity f) univ
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
    exact h
  have : IsFiniteKernel (densityConditionalKernel ν f) := densityConditionalKernel_finite ν hf
  have he : P.map (fun ω => (X ω, Y ω)) = P.map X ⊗ₘ densityConditionalKernel ν f := by
    rw [hXY.map_eq, joint_density_first_marginal μ ν hX hY hf hXY,
      density_disintegration μ ν hf hfin]
  have hh := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hX hY he
  filter_upwards [hh] with x hx
  exact hx.trans (densityConditionalKernel_apply ν hf x)

/-- The marginal density written as an ordinary real integral. Joint
integrability ensures that the sections are integrable almost everywhere. -/
theorem real_joint_density_first_marginal {f : α × β → ℝ}
    (hf : Measurable f) (hi : Integrable f (μ.prod ν)) (h0 : ∀ z, 0 ≤ f z)
    (hXY : HasLaw (fun ω => (X ω, Y ω))
      ((μ.prod ν).withDensity (fun z => ENNReal.ofReal (f z))) P) :
    P.map X = μ.withDensity (fun x => ENNReal.ofReal (∫ y, f (x, y) ∂ν)) := by
  rw [joint_density_first_marginal μ ν hX hY hf.ennreal_ofReal hXY]
  apply withDensity_congr_ae
  filter_upwards [hi.prod_right_ae] with x hx
  exact (ofReal_integral_eq_lintegral_ofReal hx (ae_of_all _ fun y => h0 (x, y))).symm

/-- L1's familiar real-valued conditional PDF formula. The marginal is the
integral of the joint PDF, and the formula identifies the actual conditional
law rather than assigning an arbitrary meaning to a null conditioning event. -/
theorem real_conditional_density_ratio_of_hasLaw {f : α × β → ℝ}
    (hf : Measurable f) (hi : Integrable f (μ.prod ν)) (h0 : ∀ z, 0 ≤ f z)
    (hXY : HasLaw (fun ω => (X ω, Y ω))
      ((μ.prod ν).withDensity (fun z => ENNReal.ofReal (f z))) P) :
    condDistrib Y X P =ᵐ[P.map X] (fun x => ν.withDensity
      (fun y => ENNReal.ofReal (f (x, y) / (∫ t, f (x, t) ∂ν)))) := by
  let F : α × β → ℝ≥0∞ := fun z => ENNReal.ofReal (f z)
  have hF : Measurable F := hf.ennreal_ofReal
  have hfin : (∫⁻ z, F z ∂μ.prod ν) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ h0)]
    exact ENNReal.ofReal_ne_top
  have hm : P.map X = μ.withDensity (marginalDensity ν F) :=
    joint_density_first_marginal μ ν hX hY hF hXY
  have hint : ∀ᵐ x ∂P.map X, Integrable (fun y => f (x, y)) ν := by
    rw [hm, ae_withDensity_iff (measurable_marginalDensity ν hF)]
    exact hi.prod_right_ae.mono (fun _ hx _ => hx)
  have hpos : ∀ᵐ x ∂P.map X, 0 < marginalDensity ν F x := by
    rw [hm]
    exact (marginalDensity_positive_finite_ae μ ν hF hfin).mono (fun _ h => h.1)
  filter_upwards [conditional_density_ratio_of_hasLaw μ ν hX hY hF hXY, hint, hpos]
    with x hx hxi hxp
  rw [hx]
  have hg : marginalDensity ν F x = ENNReal.ofReal (∫ y, f (x, y) ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal hxi (ae_of_all _ fun y => h0 (x, y))).symm
  have hp : 0 < ∫ y, f (x, y) ∂ν := ENNReal.ofReal_pos.mp (hg ▸ hxp)
  apply congrArg (fun q : β → ℝ≥0∞ => ν.withDensity q)
  funext y
  rw [hg]
  exact (ENNReal.ofReal_div_of_pos hp).symm

end General
end LectureNotes
