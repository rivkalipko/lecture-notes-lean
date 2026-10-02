import LectureNotes.HighestDensity
import Mathlib.Probability.CDF
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

/-- The joint CDF of a real probability law. -/
def jointCDF (ρ : Measure (ℝ × ℝ)) (x y : ℝ) : ℝ := ρ.real (Iic x ×ˢ Iic y)

theorem jointCDF_randomVariables {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (x y : ℝ) :
    jointCDF (P.map (fun ω => (X ω, Y ω))) x y = P.real {ω | X ω ≤ x ∧ Y ω ≤ y} := by
  rw [jointCDF, map_measureReal_apply (hX.prodMk hY) (measurableSet_Iic.prod measurableSet_Iic)]
  rfl

theorem jointCDF_mono (ρ : Measure (ℝ × ℝ)) [IsFiniteMeasure ρ]
    {x x' y y' : ℝ} (hx : x ≤ x') (hy : y ≤ y') :
    jointCDF ρ x y ≤ jointCDF ρ x' y' :=
  measureReal_mono (prod_mono (Iic_subset_Iic.mpr hx) (Iic_subset_Iic.mpr hy)) (measure_ne_top _ _)

/-- Sending the second threshold to infinity recovers the first marginal CDF. -/
theorem jointCDF_tendsto_snd (ρ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ρ] (x : ℝ) :
    Tendsto (jointCDF ρ x) atTop (𝓝 (cdf (ρ.map Prod.fst) x)) := by
  have : IsProbabilityMeasure (ρ.map Prod.fst) := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hs : Monotone (fun y : ℝ => Iic x ×ˢ Iic y) :=
    fun a b hab => prod_mono Subset.rfl (Iic_subset_Iic.mpr hab)
  have he : (⋃ y : ℝ, Iic x ×ˢ Iic y) = Prod.fst ⁻¹' Iic x := by
    ext z
    simp only [mem_iUnion, mem_prod, mem_Iic, mem_preimage]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨z.2, h, le_rfl⟩⟩
  have ht := (ENNReal.tendsto_toReal (measure_ne_top ρ (⋃ y : ℝ, Iic x ×ˢ Iic y))).comp
    (tendsto_measure_iUnion_atTop (μ := ρ) hs)
  rw [he] at ht
  rw [cdf_eq_real, map_measureReal_apply measurable_fst measurableSet_Iic]
  exact ht

/-- Sending the first threshold to infinity recovers the second marginal CDF. -/
theorem jointCDF_tendsto_fst (ρ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ρ] (y : ℝ) :
    Tendsto (fun x => jointCDF ρ x y) atTop (𝓝 (cdf (ρ.map Prod.snd) y)) := by
  have : IsProbabilityMeasure (ρ.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hs : Monotone (fun x : ℝ => Iic x ×ˢ Iic y) :=
    fun a b hab => prod_mono (Iic_subset_Iic.mpr hab) Subset.rfl
  have he : (⋃ x : ℝ, Iic x ×ˢ Iic y) = Prod.snd ⁻¹' Iic y := by
    ext z
    simp only [mem_iUnion, mem_prod, mem_Iic, mem_preimage]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨z.1, le_rfl, h⟩⟩
  have ht := (ENNReal.tendsto_toReal (measure_ne_top ρ (⋃ x : ℝ, Iic x ×ˢ Iic y))).comp
    (tendsto_measure_iUnion_atTop (μ := ρ) hs)
  rw [he] at ht
  rw [cdf_eq_real, map_measureReal_apply measurable_snd measurableSet_Iic]
  exact ht

section Density
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]

/-- The first marginal density of a joint nonnegative density. -/
def marginalDensity (f : α × β → ℝ≥0∞) (x : α) : ℝ≥0∞ := ∫⁻ y, f (x, y) ∂ν

theorem measurable_marginalDensity {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    Measurable (marginalDensity ν f) := hf.lintegral_prod_right'

/-- Marginalization is proved for the actual weighted product measure. It
applies both to Lebesgue densities and to counting-measure mass functions. -/
theorem density_map_fst {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ((μ.prod ν).withDensity f).map Prod.fst = μ.withDensity (marginalDensity ν f) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, withDensity_apply _ (measurable_fst hs),
    withDensity_apply _ hs]
  have he : Prod.fst ⁻¹' s = s ×ˢ (univ : Set β) := by ext z; simp
  rw [he, setLIntegral_prod _ hf.aemeasurable.restrict]
  simp only [Measure.restrict_univ, marginalDensity]

theorem density_map_snd {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ((μ.prod ν).withDensity f).map Prod.snd =
      ν.withDensity (fun y => ∫⁻ x, f (x, y) ∂μ) := by
  ext s hs
  rw [Measure.map_apply measurable_snd hs, withDensity_apply _ (measurable_snd hs),
    withDensity_apply _ hs]
  have he : Prod.snd ⁻¹' s = (univ : Set α) ×ˢ s := by ext z; simp
  rw [he, setLIntegral_prod_symm _ hf.aemeasurable.restrict]
  simp only [Measure.restrict_univ]

theorem density_rectangle {f : α × β → ℝ≥0∞} (hf : Measurable f)
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ.prod ν).withDensity f (s ×ˢ t) = ∫⁻ x in s, ∫⁻ y in t, f (x, y) ∂ν ∂μ := by
  rw [withDensity_apply _ (hs.prod ht), setLIntegral_prod _ hf.aemeasurable.restrict]

end Density

/-- The continuous joint-CDF formula is an iterated integral over the lower
rectangle, with actual joint integrability and nonnegativity hypotheses. -/
theorem jointCDF_density {f : ℝ × ℝ → ℝ}
    (hi : Integrable f (volume.prod volume)) (h0 : ∀ z, 0 ≤ f z) (x y : ℝ) :
    jointCDF ((volume.prod volume).withDensity (fun z => ENNReal.ofReal (f z))) x y =
      ∫ u in Iic x, ∫ v in Iic y, f (u, v) := by
  rw [jointCDF, density_event_eq_integral hi h0 _ (measurableSet_Iic.prod measurableSet_Iic)]
  exact setIntegral_prod _ hi.integrableOn

/-- On a countable second coordinate, the marginal mass is the sum of the
joint masses in that row. -/
theorem discrete_marginal_mass {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]
    (ρ : Measure (α × β)) (x : α) :
    (ρ.map Prod.fst) {x} = ∑' y : β, ρ {(x, y)} := by
  rw [Measure.map_apply measurable_fst (measurableSet_singleton x)]
  exact measure_preimage_fst_singleton_eq_tsum ρ x

/-- On a conditioning atom of positive mass, the actual regular conditional
law is exactly the joint-to-marginal probability ratio. -/
theorem conditional_atom_ratio {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (x : α)
    (hx : (ρ.map Prod.fst) {x} ≠ 0) (s : Set β) :
    condDistrib Prod.snd Prod.fst ρ x s = ρ ({x} ×ˢ s) / (ρ.map Prod.fst) {x} := by
  have h := condDistrib_apply_of_ne_zero (μ := ρ) (X := Prod.fst) measurable_snd x hx s
  simpa only [Prod.mk.eta, Measure.map_id', div_eq_mul_inv, mul_comm] using h

end LectureNotes
