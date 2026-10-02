import LectureNotes.PoissonLikelihood
import Mathlib.Analysis.Calculus.LHopital

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- Half the per-observation Poisson likelihood-ratio expression. -/
def poissonDeviance (r m : ℝ) : ℝ := m * Real.log (m / r) - m + r

theorem poisson_log_ratio_derivative {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.log (t / r)) (1 / x) x := by
  convert! ((hasDerivAt_id x).div_const r).log (div_ne_zero hx.ne' hr.ne') using 1
  simp only [id_eq]
  field_simp

theorem poissonDeviance_derivative {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    HasDerivAt (poissonDeviance r) (Real.log (x / r)) x := by
  convert! (((hasDerivAt_id x).mul (poisson_log_ratio_derivative hr hx)).sub
    (hasDerivAt_id x)).add_const r using 1
  simp only [id_eq, one_mul]
  field_simp
  ring

/-- The quadratic coefficient follows from two applications of L'Hôpital's
rule, with every derivative and punctured-neighborhood condition verified. -/
theorem poissonDeviance_quadratic_limit {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x => poissonDeviance r x / (x - r) ^ 2) (𝓝[≠] r) (𝓝 (1 / (2 * r))) := by
  have hpos : ∀ᶠ x in 𝓝[≠] r, 0 < x := nhdsWithin_le_nhds (lt_mem_nhds hr)
  have hlog0 : Tendsto (fun x : ℝ => Real.log (x / r)) (𝓝[≠] r) (𝓝 0) := by
    have hh := (poisson_log_ratio_derivative hr hr).continuousAt.tendsto.mono_left
      (show 𝓝[≠] r ≤ 𝓝 r from nhdsWithin_le_nhds)
    simpa [hr.ne'] using hh
  have hlin0 : Tendsto (fun x : ℝ => 2 * (x - r)) (𝓝[≠] r) (𝓝 0) := by
    have hh : ContinuousAt (fun x : ℝ => 2 * (x - r)) r := by fun_prop
    simpa using hh.tendsto.mono_left nhdsWithin_le_nhds
  have hderivlim : Tendsto (fun x : ℝ => (1 / x) / 2) (𝓝[≠] r) (𝓝 (1 / (2 * r))) := by
    have hh : ContinuousAt (fun x : ℝ => (1 / x) / 2) r :=
      (continuousAt_const.div continuousAt_id hr.ne').div_const 2
    convert! hh.tendsto.mono_left nhdsWithin_le_nhds using 1
    congr 1
    ring
  have hfirst : Tendsto (fun x : ℝ => Real.log (x / r) / (2 * (x - r)))
      (𝓝[≠] r) (𝓝 (1 / (2 * r))) :=
    HasDerivAt.lhopital_zero_nhdsNE
      (hpos.mono (fun x hx => poisson_log_ratio_derivative hr hx))
      (Eventually.of_forall (fun x => by simpa using ((hasDerivAt_id x).sub_const r).const_mul 2))
      (Eventually.of_forall (fun _ => by norm_num)) hlog0 hlin0 hderivlim
  have hdev0 : Tendsto (poissonDeviance r) (𝓝[≠] r) (𝓝 0) := by
    have hh := (poissonDeviance_derivative hr hr).continuousAt.tendsto.mono_left
      (show 𝓝[≠] r ≤ 𝓝 r from nhdsWithin_le_nhds)
    simpa [poissonDeviance, hr.ne'] using hh
  have hsq0 : Tendsto (fun x : ℝ => (x - r) ^ 2) (𝓝[≠] r) (𝓝 0) := by
    have hh : ContinuousAt (fun x : ℝ => (x - r) ^ 2) r := by fun_prop
    simpa using hh.tendsto.mono_left nhdsWithin_le_nhds
  apply HasDerivAt.lhopital_zero_nhdsNE
    (hpos.mono (fun x hx => poissonDeviance_derivative hr hx))
    (Eventually.of_forall (fun x => by
      convert! ((hasDerivAt_id x).sub_const r).pow 2 using 1 <;> simp))
    _ hdev0 hsq0 hfirst
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hx)

/-- Fill the removable singularity at the true rate with its quadratic limit. -/
def poissonDevianceCoefficient (r : ℝ) : ℝ → ℝ :=
  Function.update (fun x => poissonDeviance r x / (x - r) ^ 2) r (1 / (2 * r))

theorem poissonDevianceCoefficient_continuousAt {r : ℝ} (hr : 0 < r) :
    ContinuousAt (poissonDevianceCoefficient r) r :=
  continuousAt_update_same.mpr (poissonDeviance_quadratic_limit hr)

theorem poissonDevianceCoefficient_measurable (r : ℝ) : Measurable (poissonDevianceCoefficient r) := by
  unfold poissonDevianceCoefficient
  classical
  have he : Function.update (fun x => poissonDeviance r x / (x - r) ^ 2) r (1 / (2 * r)) =
      (fun x => if x = r then 1 / (2 * r) else poissonDeviance r x / (x - r) ^ 2) :=
    funext (fun x => Function.update_apply _ _ _ x)
  rw [he]
  apply Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
  unfold poissonDeviance
  fun_prop

/-- Exact factorization, including both the center and the zero-count sample. -/
theorem poissonDeviance_factorization {r : ℝ} (hr : 0 < r) (m : ℝ) :
    poissonDeviance r m = (m - r) ^ 2 * poissonDevianceCoefficient r m := by
  classical
  by_cases hmr : m = r
  · subst m
    simp [poissonDeviance, hr.ne']
  · simp only [poissonDevianceCoefficient, Function.update_of_ne hmr]
    field_simp

end LectureNotes
