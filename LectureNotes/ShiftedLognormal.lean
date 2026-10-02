import LectureNotes.DensityTransform
import LectureNotes.NormalSampling
import LectureNotes.MonteCarlo

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- The shifted lognormal law is the actual exponential pushforward of a
Gaussian observation; the Gaussian variance parameter is v. -/
def shiftedLognormalLaw (μ : ℝ) (v : ℝ≥0) (γ : ℝ) : Measure ℝ :=
  (gaussianReal μ v).map (fun z => γ + Real.exp z)

instance shiftedLognormalLaw_probability (μ : ℝ) (v : ℝ≥0) (γ : ℝ) :
    IsProbabilityMeasure (shiftedLognormalLaw μ v γ) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- L2's shifted lognormal density, written first using the Gaussian density. -/
def shiftedLognormalDensity (μ : ℝ) (v : ℝ≥0) (γ x : ℝ) : ℝ :=
  if γ < x then gaussianPDFReal μ v (Real.log (x - γ)) / (x - γ) else 0

theorem shiftedLognormalDensity_formula (μ : ℝ) (v : ℝ≥0) (γ x : ℝ) :
    shiftedLognormalDensity μ v γ x = if γ < x then
      (Real.sqrt (2 * Real.pi * v))⁻¹ * (x - γ)⁻¹ *
        Real.exp (-((Real.log (x - γ) - μ) ^ 2) / (2 * v)) else 0 := by
  unfold shiftedLognormalDensity gaussianPDFReal
  split_ifs <;> ring

theorem shiftedLognormalDensity_nonneg (μ : ℝ) (v : ℝ≥0) (γ x : ℝ) :
    0 ≤ shiftedLognormalDensity μ v γ x := by
  unfold shiftedLognormalDensity
  split_ifs with hx
  · exact div_nonneg (gaussianPDFReal_nonneg _ _ _) (sub_pos.mpr hx).le
  · rfl

theorem shiftedLognormalDensity_measurable (μ : ℝ) (v : ℝ≥0) (γ : ℝ) :
    Measurable (shiftedLognormalDensity μ v γ) := by
  unfold shiftedLognormalDensity
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (((measurable_gaussianPDFReal μ v).comp (measurable_id.sub_const γ).log).div
      (measurable_id.sub_const γ)) measurable_const

/-- Change of variables proves the displayed density equals the actual
simulation law. Positive Gaussian variance excludes its point-mass degeneration. -/
theorem shiftedLognormalLaw_density (μ : ℝ) {v : ℝ≥0} (hv : 0 < v) (γ : ℝ) :
    volume.withDensity (fun x => ENNReal.ofReal (shiftedLognormalDensity μ v γ x)) =
      shiftedLognormalLaw μ v γ := by
  have hgt (y : ℝ) (hy : y ∈ Ioi γ) : 0 < y - γ := sub_pos.mpr hy
  have he := density_map_on_sets (g := fun z : ℝ => γ + Real.exp z)
    (h := fun y => Real.log (y - γ)) (s := univ) (t := Ioi γ)
    MeasurableSet.univ measurableSet_Ioi (by fun_prop)
    (by intro z _; exact lt_add_of_pos_right γ (Real.exp_pos z))
    (by intro y _; exact mem_univ _)
    (by intro z _; simp)
    (by intro y hy; change γ + Real.exp (Real.log (y - γ)) = y; rw [Real.exp_log (hgt y hy)]; ring)
    (fun y => (y - γ)⁻¹)
    (by intro y hy; simpa only [id_eq, one_div] using (((hasDerivAt_id y).sub_const γ).log (hgt y hy).ne').hasDerivWithinAt)
    (gaussianPDFReal μ v)
  simp only [Measure.restrict_univ] at he
  change (volume.withDensity (gaussianPDF μ v)).map (fun z => γ + Real.exp z) = _ at he
  rw [← gaussianReal_of_var_ne_zero μ hv.ne'] at he
  rw [shiftedLognormalLaw, he, ← withDensity_indicator measurableSet_Ioi]
  apply withDensity_congr_ae
  apply ae_of_all
  intro x
  by_cases hx : γ < x
  · rw [Set.indicator_of_mem (show x ∈ Ioi γ from hx)]
    simp only [shiftedLognormalDensity, hx, if_true,
      abs_of_pos (inv_pos.mpr (sub_pos.mpr hx)), div_eq_mul_inv]
    rw [mul_comm]
  · simp [shiftedLognormalDensity, hx]

/-- Exponentiating and shifting an actual Gaussian draw generates exactly
the distribution postulated in the lecture's Monte Carlo example. -/
theorem shiftedLognormal_simulation_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ} {μ γ : ℝ} {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal μ v) P) :
    HasLaw (fun ω => γ + Real.exp (Z ω)) (shiftedLognormalLaw μ v γ) P := by
  have hg : HasLaw (fun z : ℝ => γ + Real.exp z) (shiftedLognormalLaw μ v γ) (gaussianReal μ v) :=
    ⟨by fun_prop, rfl⟩
  exact hg.comp hZ

/-- A vector of independently generated Gaussian draws gives an actual IID
sample from the shifted lognormal density. -/
theorem shiftedLognormal_sample_simulation {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} {Z : Fin n → Ω → ℝ}
    {μ γ : ℝ} {v : ℝ≥0} (hZ : ∀ i, HasLaw (Z i) (gaussianReal μ v) P)
    (hind : iIndepFun Z P) :
    HasLaw (fun ω i => γ + Real.exp (Z i ω))
      (Measure.pi (fun _ : Fin n => shiftedLognormalLaw μ v γ)) P := by
  exact (hind.comp (fun _ z => γ + Real.exp z) (fun _ => by fun_prop)).hasLaw_pi
    (fun i => shiftedLognormal_simulation_law (hZ i))

/-- The simulated average therefore has the exact pushforward sampling law
whose CDF, moments, and quantiles the Monte Carlo procedure estimates. -/
theorem shiftedLognormal_sampleMean_simulation {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} {Z : Fin n → Ω → ℝ}
    {μ γ : ℝ} {v : ℝ≥0} (hZ : ∀ i, HasLaw (Z i) (gaussianReal μ v) P)
    (hind : iIndepFun Z P) :
    HasLaw (fun ω => sampleMean (fun i => γ + Real.exp (Z i ω)))
      ((Measure.pi (fun _ : Fin n => shiftedLognormalLaw μ v γ)).map sampleMean) P := by
  have hg : HasLaw (sampleMean : (Fin n → ℝ) → ℝ)
      ((Measure.pi (fun _ : Fin n => shiftedLognormalLaw μ v γ)).map sampleMean)
      (Measure.pi (fun _ : Fin n => shiftedLognormalLaw μ v γ)) :=
    ⟨by unfold sampleMean; fun_prop, rfl⟩
  exact hg.comp (shiftedLognormal_sample_simulation hZ hind)

end LectureNotes
