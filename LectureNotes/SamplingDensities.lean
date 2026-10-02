import LectureNotes.DensityTransform
import LectureNotes.Sampling
import Mathlib.Probability.Density

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Change of variables for nonnegative extended densities. This formulation
retains possible infinite values on null sets. -/
theorem ennreal_density_map_equiv (g : ℝ ≃ᵐ ℝ) (g' : ℝ → ℝ)
    (hg' : ∀ y, HasDerivAt g.symm (g' y) y) (f : ℝ → ℝ≥0∞) :
    (volume.withDensity f).map g =
      volume.withDensity (fun y => ENNReal.ofReal |g' y| * f (g.symm y)) := by
  ext s hs
  rw [Measure.map_apply g.measurable hs,
    withDensity_apply _ (g.measurable hs), withDensity_apply _ hs]
  have he : g ⁻¹' s = g.symm '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨g x, hx, g.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [he, lintegral_image_eq_lintegral_abs_deriv_mul hs
    (fun y _ => (hg' y).hasDerivWithinAt) g.symm.injective.injOn]

theorem ennreal_density_div_pos (f : ℝ → ℝ≥0∞) {b : ℝ} (hb : 0 < b) :
    (volume.withDensity f).map (fun x => x / b) =
      volume.withDensity (fun y => ENNReal.ofReal b * f (b * y)) := by
  have he (y : ℝ) : HasDerivAt (MeasurableEquiv.mulLeft₀ b⁻¹ (inv_ne_zero hb.ne')).symm b y := by
    simpa only [MeasurableEquiv.symm_mulLeft₀, MeasurableEquiv.coe_mulLeft₀, inv_inv, id_eq, mul_one]
      using (hasDerivAt_id y).const_mul b
  simpa only [MeasurableEquiv.symm_mulLeft₀, MeasurableEquiv.coe_mulLeft₀,
    inv_inv, abs_of_pos hb, div_eq_mul_inv, mul_comm] using
    ennreal_density_map_equiv (MeasurableEquiv.mulLeft₀ b⁻¹ (inv_ne_zero hb.ne')) (fun _ => b) he f

/-- L2 Example 4: the law of the sum of independent observations with actual
densities is given by the convolution integral. -/
theorem independent_sum_density {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hX : HasLaw X (volume.withDensity f) P) (hY : HasLaw Y (volume.withDensity g) P)
    (hind : IndepFun X Y P) :
    HasLaw (fun ω => X ω + Y ω)
      (volume.withDensity (fun z => ∫⁻ x, f x * g (z - x))) P := by
  refine ⟨hX.aemeasurable.add hY.aemeasurable, ?_⟩
  have he := hind.map_add_eq_map_conv_map₀ hX.aemeasurable hY.aemeasurable
  rw [hX.map_eq, hY.map_eq, conv_withDensity_eq_lconvolution hf hg] at he
  change P.map (fun ω => X ω + Y ω) =
    volume.withDensity (fun z => ∫⁻ x, f x * g (-x + z)) at he
  simpa only [sub_eq_add_neg, add_comm] using he

/-- Density of a sum of k+1 IID real observations, as the iterated convolution
integral printed in L2. A positive number of observations is built into indexing. -/
def iidSumDensity (f : ℝ → ℝ≥0∞) : ℕ → ℝ → ℝ≥0∞
  | 0 => f
  | k + 1 => fun z => ∫⁻ y, iidSumDensity f k y * f (z - y)

theorem iidSumDensity_measurable {f : ℝ → ℝ≥0∞} (hf : Measurable f) (k : ℕ) :
    Measurable (iidSumDensity f k) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    have he : iidSumDensity f (k + 1) = iidSumDensity f k ⋆ₗ f := by
      funext z
      simp only [iidSumDensity, lconvolution_def, sub_eq_add_neg, add_comm]
    rw [he]
    exact measurable_lconvolution volume ih hf

/-- The iterated density is identified with the actual IID sample sum law. -/
theorem iid_sample_sum_density {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hX : ∀ i, HasLaw (X i) (volume.withDensity f) P) (k : ℕ) :
    HasLaw (fun ω => ∑ i ∈ Finset.range (k + 1), X i ω)
      (volume.withDensity (iidSumDensity f k)) P := by
  induction k with
  | zero => simpa only [iidSumDensity, Nat.zero_add, Finset.sum_range_one] using! hX 0
  | succ k ih =>
    have hi : IndepFun (fun ω => ∑ i ∈ Finset.range (k + 1), X i ω) (X (k + 1)) P := by
      convert! hind.indepFun_sum_range_succ hXm (k + 1) using 1
      funext ω
      simp only [Finset.sum_apply]
    have hh := independent_sum_density (iidSumDensity_measurable hf k) hf ih (hX (k + 1)) hi
    simpa only [iidSumDensity, Finset.sum_range_succ] using hh

/-- The density of the actual sample mean is (k+1) times the sum density at
(k+1)y. This proves the scaling factor rather than postulating a density. -/
theorem iid_sample_mean_density {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hX : ∀ i, HasLaw (X i) (volume.withDensity f) P) (k : ℕ) :
    HasLaw (fun ω => sampleMean (fun i : Fin (k + 1) => X i ω))
      (volume.withDensity (fun y => ENNReal.ofReal ((k : ℝ) + 1) *
        iidSumDensity f k (((k : ℝ) + 1) * y))) P := by
  have hs := iid_sample_sum_density hXm hind hf hX k
  have hd : HasLaw (fun z : ℝ => z / ((k : ℝ) + 1))
      (volume.withDensity (fun y => ENNReal.ofReal ((k : ℝ) + 1) *
        iidSumDensity f k (((k : ℝ) + 1) * y)))
      (volume.withDensity (iidSumDensity f k)) :=
    ⟨by fun_prop, ennreal_density_div_pos _ (by positivity)⟩
  have hh := hd.comp hs
  apply hh.congr
  apply ae_of_all
  intro ω
  simp only [sampleMean, Fintype.card_fin, Nat.cast_add, Nat.cast_one, Function.comp_def]
  rw [Fin.sum_univ_eq_sum_range (fun i => X i ω) (k + 1)]
  ring

end LectureNotes
