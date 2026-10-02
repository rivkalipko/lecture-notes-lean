import LectureNotes.JointDistributions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- Fundamental theorem of calculus for a lower-tail integral. -/
theorem lowerTailIntegral_hasDerivAt {f : ℝ → ℝ} (hi : Integrable f) {x : ℝ}
    (hc : ContinuousAt f x) : HasDerivAt (fun u => ∫ t in Iic u, f t) (f x) x := by
  have he : (fun u => ∫ t in Iic u, f t) =
      (fun u => (∫ t in Iic (0 : ℝ), f t) + ∫ t in (0 : ℝ)..u, f t) := by
    funext u
    have h := intervalIntegral.integral_Iic_sub_Iic (a := (0 : ℝ)) (b := u)
      hi.integrableOn hi.integrableOn
    linarith
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right hi.intervalIntegrable
    hi.aestronglyMeasurable.stronglyMeasurableAtFilter hc).const_add _

/-- A density equals the CDF derivative at a point where that density is
continuous. CDF continuity by itself would not be sufficient. -/
theorem density_cdf_hasDerivAt {f : ℝ → ℝ} (hi : Integrable f) (h0 : ∀ x, 0 ≤ f x)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))]
    {x : ℝ} (hc : ContinuousAt f x) :
    HasDerivAt (cdf (volume.withDensity (fun x => ENNReal.ofReal (f x)))) (f x) x := by
  have he : (fun t => cdf (volume.withDensity (fun x => ENNReal.ofReal (f x))) t) =
      (fun t => ∫ u in Iic t, f u) := by
    funext t
    rw [cdf_eq_real, density_event_eq_integral hi h0 _ measurableSet_Iic]
  rw [show (cdf (volume.withDensity (fun x => ENNReal.ofReal (f x))) : ℝ → ℝ) =
    (fun t => ∫ u in Iic t, f u) from he]
  exact lowerTailIntegral_hasDerivAt hi hc

/-- A continuous joint density with an integrable bound in the second
coordinate has a differentiable joint CDF in its first threshold. The bound
justifies continuity of the partial integral by dominated convergence. -/
theorem jointCDF_first_hasDerivAt {f : ℝ × ℝ → ℝ}
    (hi : Integrable f (volume.prod volume)) (h0 : ∀ z, 0 ≤ f z) (hc : Continuous f)
    (bound : ℝ → ℝ) (hb : Integrable bound)
    (hbound : ∀ x y, ‖f (x, y)‖ ≤ bound y) (x y : ℝ) :
    HasDerivAt (fun u => jointCDF
      ((volume.prod volume).withDensity (fun z => ENNReal.ofReal (f z))) u y)
      (∫ v in Iic y, f (x, v)) x := by
  have hrest := hi.restrict (s := (univ : Set ℝ) ×ˢ Iic y)
  rw [← Measure.prod_restrict, Measure.restrict_univ] at hrest
  have hInt : Integrable (fun u => ∫ v in Iic y, f (u, v)) := hrest.integral_prod_left
  have hCont : Continuous (fun u => ∫ v in Iic y, f (u, v)) :=
    continuous_of_dominated
      (fun u => (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (fun u => ae_of_all _ (fun v => hbound u v)) hb.integrableOn
      (ae_of_all _ (fun v => hc.comp (continuous_id.prodMk continuous_const)))
  have he : (fun u => jointCDF
      ((volume.prod volume).withDensity (fun z => ENNReal.ofReal (f z))) u y) =
      (fun u => ∫ t in Iic u, ∫ v in Iic y, f (t, v)) := by
    funext u
    exact jointCDF_density hi h0 u y
  rw [he]
  exact lowerTailIntegral_hasDerivAt hInt hCont.continuousAt

/-- L1's mixed joint-CDF derivative formula, with sufficient density
regularity and domination stated explicitly and the derivative derived. -/
theorem jointCDF_mixed_derivative {f : ℝ × ℝ → ℝ}
    (hi : Integrable f (volume.prod volume)) (h0 : ∀ z, 0 ≤ f z) (hc : Continuous f)
    (bound : ℝ → ℝ) (hb : Integrable bound)
    (hbound : ∀ x y, ‖f (x, y)‖ ≤ bound y) (x y : ℝ) :
    deriv (fun v => deriv (fun u => jointCDF
      ((volume.prod volume).withDensity (fun z => ENNReal.ofReal (f z))) u v) x) y = f (x, y) := by
  have he : (fun v => deriv (fun u => jointCDF
      ((volume.prod volume).withDensity (fun z => ENNReal.ofReal (f z))) u v) x) =
      (fun v => ∫ t in Iic v, f (x, t)) := by
    funext v
    exact (jointCDF_first_hasDerivAt hi h0 hc bound hb hbound x v).deriv
  rw [he]
  have hrow : Integrable (fun v => f (x, v)) := hb.mono
    (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun v => (hbound x v).trans (le_abs_self (bound v)))
  exact (lowerTailIntegral_hasDerivAt hrow (hc.comp (continuous_const.prodMk continuous_id)).continuousAt).deriv

end LectureNotes
