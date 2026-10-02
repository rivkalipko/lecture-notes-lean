import LectureNotes.QuantileReparameterization
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Inverse

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

/-- The density of a transformed real observation, written using the derivative
of its inverse. This equality is of actual measures, so no normalization is
implicit in the formula. -/
theorem density_map_equiv (g : ℝ ≃ᵐ ℝ) (g' : ℝ → ℝ)
    (hg' : ∀ y, HasDerivAt g.symm (g' y) y) (p : ℝ → ℝ) :
    (volume.withDensity (fun x => ENNReal.ofReal (p x))).map g =
      volume.withDensity (fun y => ENNReal.ofReal (|g' y| * p (g.symm y))) := by
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
  congr 1
  funext y
  exact (ENNReal.ofReal_mul (abs_nonneg _)).symm

/-- L1's reciprocal-derivative density formula, with the nonzero-derivative
condition required by the inverse function theorem stated explicitly. -/
theorem density_map_homeomorph (g : ℝ ≃ₜ ℝ) (g' : ℝ → ℝ)
    (hg' : ∀ x, HasDerivAt g (g' x) x) (hn : ∀ x, g' x ≠ 0) (p : ℝ → ℝ) :
    (volume.withDensity (fun x => ENNReal.ofReal (p x))).map g =
      volume.withDensity (fun y => ENNReal.ofReal (p (g.symm y) / |g' (g.symm y)|)) := by
  have hi (y : ℝ) : HasDerivAt g.symm (g' (g.symm y))⁻¹ y :=
    (hg' (g.symm y)).of_local_left_inverse g.symm.continuous.continuousAt (hn _)
      (Eventually.of_forall fun z => g.apply_symm_apply z)
  have h := density_map_equiv g.toMeasurableEquiv (fun y => (g' (g.symm y))⁻¹) hi p
  simpa only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.toMeasurableEquiv_symm_coe,
    abs_inv, div_eq_mul_inv, mul_comm] using h

/-- The increasing case has a positive Jacobian, so its absolute value drops
out of the reciprocal-derivative expression. -/
theorem density_map_positive_derivative (g : ℝ ≃ₜ ℝ) (g' : ℝ → ℝ)
    (hg' : ∀ x, HasDerivAt g (g' x) x) (hp : ∀ x, 0 < g' x) (p : ℝ → ℝ) :
    (volume.withDensity (fun x => ENNReal.ofReal (p x))).map g =
      volume.withDensity (fun y => ENNReal.ofReal (p (g.symm y) / g' (g.symm y))) := by
  simpa only [abs_of_pos (hp _)] using density_map_homeomorph g g' hg' (fun x => (hp x).ne') p

/-- A version on a measurable source and target, allowing the transformation
to have a proper interval as its range. The inverse identities and derivative
are required only on these sets. -/
theorem density_map_on_sets {g h : ℝ → ℝ} {s t : Set ℝ}
    (_hs : MeasurableSet s) (ht : MeasurableSet t) (hg : Measurable g)
    (hgs : MapsTo g s t) (hht : MapsTo h t s)
    (hleft : LeftInvOn h g s) (hright : RightInvOn h g t)
    (h' : ℝ → ℝ) (hd : ∀ y ∈ t, HasDerivWithinAt h (h' y) t y) (p : ℝ → ℝ) :
    ((volume.restrict s).withDensity (fun x => ENNReal.ofReal (p x))).map g =
      (volume.restrict t).withDensity (fun y => ENNReal.ofReal (|h' y| * p (h y))) := by
  ext A hA
  rw [Measure.map_apply hg hA, withDensity_apply _ (hg hA), withDensity_apply _ hA,
    Measure.restrict_restrict (hg hA), Measure.restrict_restrict hA]
  have he : g ⁻¹' A ∩ s = h '' (A ∩ t) := by
    ext x
    constructor
    · rintro ⟨hx, hxs⟩
      exact ⟨g x, ⟨hx, hgs hxs⟩, hleft hxs⟩
    · rintro ⟨y, ⟨hyA, hyt⟩, rfl⟩
      exact ⟨by simpa only [mem_preimage, hright hyt] using hyA, hht hyt⟩
  rw [he, lintegral_image_eq_lintegral_abs_deriv_mul (hA.inter ht)
    (fun y hy => (hd y hy.2).mono inter_subset_right)
    ((hright.injOn).mono inter_subset_right)]
  congr 1
  funext y
  exact (ENNReal.ofReal_mul (abs_nonneg _)).symm

theorem cdf_sub_const (μ : Measure ℝ) [IsProbabilityMeasure μ] (a t : ℝ) :
    cdf (μ.map (fun x => x - a)) t = cdf μ (t + a) := by
  have h := cdf_map_strictMono μ (g := fun x => x - a) (by intro x y hxy; linarith) (t + a)
  simpa using h

theorem cdf_pos_scale (μ : Measure ℝ) [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b) (t : ℝ) :
    cdf (μ.map (fun x => b * x)) t = cdf μ (t / b) := by
  have h := cdf_map_strictMono μ (g := fun x => b * x) (by intro x y hxy; exact mul_lt_mul_of_pos_left hxy hb) (t / b)
  simpa [mul_div_cancel₀ _ hb.ne'] using h

theorem density_sub_const (p : ℝ → ℝ) (a : ℝ) :
    (volume.withDensity (fun x => ENNReal.ofReal (p x))).map (fun x => x - a) =
      volume.withDensity (fun y => ENNReal.ofReal (p (y + a))) := by
  have h := density_map_equiv (MeasurableEquiv.addRight (-a)) (fun _ => 1)
    (fun y => by simpa using (hasDerivAt_id y).add_const a) p
  simpa [sub_eq_add_neg] using h

theorem density_nonzero_scale (p : ℝ → ℝ) {b : ℝ} (hb : b ≠ 0) :
    (volume.withDensity (fun x => ENNReal.ofReal (p x))).map (fun x => b * x) =
      volume.withDensity (fun y => ENNReal.ofReal (p (y / b) / |b|)) := by
  have h := density_map_equiv (MeasurableEquiv.mulLeft₀ b hb) (fun _ => b⁻¹)
    (fun y => by simpa using (hasDerivAt_id y).const_mul b⁻¹) p
  simpa only [MeasurableEquiv.coe_mulLeft₀, MeasurableEquiv.symm_mulLeft₀,
    abs_inv, div_eq_mul_inv, mul_comm] using h

theorem density_pos_scale (p : ℝ → ℝ) {b : ℝ} (hb : 0 < b) :
    (volume.withDensity (fun x => ENNReal.ofReal (p x))).map (fun x => b * x) =
      volume.withDensity (fun y => ENNReal.ofReal (p (y / b) / b)) := by
  simpa only [abs_of_pos hb] using density_nonzero_scale p hb.ne'

end LectureNotes
