import LectureNotes.JointDistributions
import Mathlib.Probability.Kernel.CompProdEqIff

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

section General
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]

/-- The density-ratio kernel. It is a probability measure on every fiber
whose marginal density is positive and finite; exceptional fibers may be zero. -/
def densityConditionalKernel (f : α × β → ℝ≥0∞) : Kernel α β :=
  (Kernel.const α ν).withDensity (fun x y => f (x, y) / marginalDensity ν f x)

theorem measurable_conditionalDensity {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z : α × β => f z / marginalDensity ν f z.1) :=
  hf.div ((measurable_marginalDensity ν hf).comp measurable_fst)

theorem densityConditionalKernel_apply {f : α × β → ℝ≥0∞} (hf : Measurable f) (x : α) :
    densityConditionalKernel ν f x = ν.withDensity (fun y => f (x, y) / marginalDensity ν f x) := by
  exact Kernel.withDensity_apply _ (measurable_conditionalDensity ν hf) x

theorem densityConditionalKernel_univ {f : α × β → ℝ≥0∞} (hf : Measurable f) (x : α) :
    densityConditionalKernel ν f x univ = marginalDensity ν f x / marginalDensity ν f x := by
  rw [densityConditionalKernel_apply ν hf, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  simp only [div_eq_mul_inv]
  exact lintegral_mul_const _ (show Measurable (fun y => f (x, y)) from hf.comp measurable_prodMk_left)

theorem densityConditionalKernel_finite {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    IsFiniteKernel (densityConditionalKernel ν f) := by
  refine ⟨⟨1, by simp, fun x => ?_⟩⟩
  rw [densityConditionalKernel_univ ν hf]
  exact ENNReal.div_self_le_one

theorem densityConditionalKernel_probability_on_fiber {f : α × β → ℝ≥0∞}
    (hf : Measurable f) {x : α} (hx0 : marginalDensity ν f x ≠ 0)
    (hxfin : marginalDensity ν f x ≠ ∞) :
    IsProbabilityMeasure (densityConditionalKernel ν f x) := by
  constructor
  rw [densityConditionalKernel_univ ν hf, ENNReal.div_self hx0 hxfin]

theorem marginalDensity_integral {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, marginalDensity ν f x ∂μ) = ∫⁻ z, f z ∂μ.prod ν :=
  (lintegral_prod _ hf.aemeasurable).symm

theorem marginalDensity_ae_finite {f : α × β → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ z, f z ∂μ.prod ν) ≠ ∞) :
    ∀ᵐ x ∂μ, marginalDensity ν f x < ∞ := by
  exact ae_lt_top (measurable_marginalDensity ν hf)
    (by rwa [marginalDensity_integral μ ν hf])

/-- Positive, finite marginal density holds almost everywhere under the
marginal law itself, even when it does not hold everywhere under the reference. -/
theorem marginalDensity_positive_finite_ae {f : α × β → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ z, f z ∂μ.prod ν) ≠ ∞) :
    ∀ᵐ x ∂μ.withDensity (marginalDensity ν f),
      0 < marginalDensity ν f x ∧ marginalDensity ν f x < ∞ := by
  rw [ae_withDensity_iff (measurable_marginalDensity ν hf)]
  filter_upwards [marginalDensity_ae_finite μ ν hf hfin] with x hx
  exact fun h0 => ⟨pos_iff_ne_zero.mpr h0, hx⟩

/-- The density ratio reconstructs the actual joint measure by integrating
its conditional kernel against the actual marginal measure. -/
theorem density_disintegration {f : α × β → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ z, f z ∂μ.prod ν) ≠ ∞) :
    μ.withDensity (marginalDensity ν f) ⊗ₘ densityConditionalKernel ν f =
      (μ.prod ν).withDensity f := by
  have hg := measurable_marginalDensity ν hf
  have hq := measurable_conditionalDensity ν hf
  have : IsFiniteKernel ((Kernel.const α ν).withDensity
      (fun x y => f (x, y) / marginalDensity ν f x)) := densityConditionalKernel_finite ν hf
  have : IsFiniteMeasure (μ.withDensity (marginalDensity ν f)) :=
    isFiniteMeasure_withDensity (by rwa [marginalDensity_integral μ ν hf])
  rw [densityConditionalKernel, Measure.compProd_withDensity hq, Measure.compProd_const,
    prod_withDensity_left hg]
  change (((μ.prod ν).withDensity (fun z => marginalDensity ν f z.1)).withDensity
    (fun z => f z / marginalDensity ν f z.1)) = _
  rw [← withDensity_mul (μ.prod ν)
    (show Measurable (fun z : α × β => marginalDensity ν f z.1) from hg.comp measurable_fst) hq]
  apply withDensity_congr_ae
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun ((hg.comp measurable_fst).mul hq) hf)).mpr
  filter_upwards [marginalDensity_ae_finite μ ν hf hfin] with x hx
  by_cases hzero : marginalDensity ν f x = 0
  · have hz : (fun y => f (x, y)) =ᵐ[ν] 0 :=
      (lintegral_eq_zero_iff (hf.comp measurable_prodMk_left)).mp hzero
    filter_upwards [hz] with y hy
    simp [Pi.mul_apply, hzero, hy]
  · exact Eventually.of_forall fun y => by
      change marginalDensity ν f x * (f (x, y) / marginalDensity ν f x) = f (x, y)
      rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel hzero hx.ne, mul_one]

variable [StandardBorelSpace β] [Nonempty β]

/-- L1's conditional density formula is an equality with the actual regular
conditional distribution, almost everywhere under the conditioning marginal. -/
theorem conditional_density_ratio {f : α × β → ℝ≥0∞} (hf : Measurable f)
    [IsFiniteMeasure ((μ.prod ν).withDensity f)] :
    condDistrib Prod.snd Prod.fst ((μ.prod ν).withDensity f) =ᵐ[
      ((μ.prod ν).withDensity f).map Prod.fst]
      (fun x => ν.withDensity (fun y => f (x, y) / marginalDensity ν f x)) := by
  have hfin : (∫⁻ z, f z ∂μ.prod ν) ≠ ∞ := by
    have h := measure_ne_top ((μ.prod ν).withDensity f) univ
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
    exact h
  have : IsFiniteKernel (densityConditionalKernel ν f) := densityConditionalKernel_finite ν hf
  have he : ((μ.prod ν).withDensity f).map (fun z : α × β => (z.1, z.2)) =
      ((μ.prod ν).withDensity f).map Prod.fst ⊗ₘ densityConditionalKernel ν f := by
    rw [Measure.map_id', density_map_fst μ ν hf, density_disintegration μ ν hf hfin]
  have hh := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    measurable_fst measurable_snd he
  filter_upwards [hh] with x hx
  exact hx.trans (densityConditionalKernel_apply ν hf x)

end General
end LectureNotes
