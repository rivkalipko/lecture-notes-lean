import LectureNotes.UniformSquare
import LectureNotes.HighestDensity
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- A version of the increasing triangular density, including its endpoints. -/
def hpdCounterexampleDensity (x : ℝ) : ℝ := (Icc (0 : ℝ) 1).indicator (fun x => 2 * x) x

local instance triangularProbability : IsProbabilityMeasure (betaMeasure 2 1) :=
  isProbabilityMeasureBeta (by norm_num) zero_lt_one

local instance triangularNoAtoms : NullSingletonClass (betaMeasure 2 1) := by
  change NullSingletonClass (volume.withDensity (fun x => ENNReal.ofReal (betaPDFReal 2 1 x)))
  infer_instance

theorem hpdCounterexample_density_law :
    volume.withDensity (fun x => ENNReal.ofReal (hpdCounterexampleDensity x)) = betaMeasure 2 1 := by
  change volume.withDensity _ = volume.withDensity (fun x => ENNReal.ofReal (betaPDFReal 2 1 x))
  apply withDensity_congr_ae
  filter_upwards [Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)] with x hx
  rw [beta_shape_one_density (by norm_num : (0 : ℝ) < 2)]
  have hiff : x ∈ Ioo (0 : ℝ) 1 ↔ x ∈ Icc (0 : ℝ) 1 := Eq.to_iff hx
  by_cases h : x ∈ Ioo (0 : ℝ) 1
  · norm_num [hpdCounterexampleDensity, indicator_of_mem h, indicator_of_mem (hiff.mp h)]
  · simp [hpdCounterexampleDensity, indicator_of_notMem h,
      indicator_of_notMem (fun hh => h (hiff.mpr hh))]

theorem hpdCounterexample_region :
    highestDensityRegion hpdCounterexampleDensity (6 / 5) = Icc (3 / 5 : ℝ) 1 := by
  ext x
  unfold highestDensityRegion hpdCounterexampleDensity
  simp only [mem_setOf_eq, mem_Icc]
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem hx]
    constructor
    · intro h; exact ⟨by linarith, hx.2⟩
    · intro h; linarith [h.1]
  · rw [indicator_of_notMem hx]
    constructor
    · norm_num
    · intro h
      exact (hx ⟨by linarith [h.1], h.2⟩).elim

private theorem triangular_interval_mass {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    (betaMeasure 2 1).real (Icc a b) = b ^ 2 - a ^ 2 := by
  rw [← measureReal_congr Ioc_ae_eq_Icc, measureReal_def, ← measure_cdf (betaMeasure 2 1),
    StieltjesFunction.measure_Ioc, beta_shape_one_cdf (by norm_num : (0 : ℝ) < 2),
    beta_shape_one_cdf (by norm_num : (0 : ℝ) < 2)]
  rw [min_eq_left hb, max_eq_left (ha.trans hab), min_eq_left (hab.trans hb), max_eq_left ha]
  rw [Real.rpow_two, Real.rpow_two, ENNReal.toReal_ofReal (by nlinarith)]

theorem hpdCounterexample_content :
    (betaMeasure 2 1).real (Icc (3 / 5 : ℝ) 1) = 16 / 25 := by
  rw [triangular_interval_mass (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The original region is genuinely a calibrated HPD minimum-volume region. -/
theorem hpdCounterexample_minimum_volume (A : Set ℝ) (hA : MeasurableSet A)
    (hcontent : 16 / 25 ≤ (betaMeasure 2 1).real A) :
    volume (Icc (3 / 5 : ℝ) 1) ≤ volume A := by
  have hm : Measurable hpdCounterexampleDensity :=
    (measurable_const.mul measurable_id).indicator measurableSet_Icc
  have hi : Integrable hpdCounterexampleDensity := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact (show Continuous (fun x : ℝ => 2 * x) from continuous_const.mul continuous_id).integrableOn_Icc
  have h0 : ∀ x, 0 ≤ hpdCounterexampleDensity x := by
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · simp only [hpdCounterexampleDensity, indicator_of_mem hx]
      exact mul_nonneg (by norm_num) hx.1
    · simp [hpdCounterexampleDensity, hx]
  have h := highest_density_minimum_volume hm hi h0 (by norm_num : (0 : ℝ) < 6 / 5) A hA
  rw [hpdCounterexample_region, hpdCounterexample_density_law] at h
  exact h (by rwa [hpdCounterexample_content])

private theorem cube_interval_mass (a b : ℝ) :
    ((betaMeasure 2 1).map (fun x : ℝ => x ^ 3)).real (Icc (a ^ 3) (b ^ 3)) =
      (betaMeasure 2 1).real (Icc a b) := by
  rw [map_measureReal_apply (by fun_prop) measurableSet_Icc]
  congr 1
  ext x
  have hg : StrictMono (fun x : ℝ => x ^ 3) := (by norm_num : Odd (3 : ℕ)).strictMono_pow
  simp only [mem_preimage, mem_Icc, hg.le_iff_le]

/-- L12: a smooth strictly increasing reparameterization can carry an HPD
region to a strictly longer credible region than another region of equal
content. The posterior is Beta(2,1), the map is x↦x³, and the content is 16/25. -/
theorem hpd_not_invariant_under_cube :
    let μ := betaMeasure 2 1
    let g := fun x : ℝ => x ^ 3
    let C := Icc (3 / 5 : ℝ) 1
    let D := Icc (0 : ℝ) (64 / 125)
    StrictMono g ∧ Continuous g ∧ μ.real C = 16 / 25 ∧
      (∀ A, MeasurableSet A → 16 / 25 ≤ μ.real A → volume C ≤ volume A) ∧
      (μ.map g).real (g '' C) = 16 / 25 ∧
      (μ.map g).real D = 16 / 25 ∧ volume D < volume (g '' C) := by
  dsimp
  have hg : StrictMono (fun x : ℝ => x ^ 3) := (by norm_num : Odd (3 : ℕ)).strictMono_pow
  have hc : Continuous (fun x : ℝ => x ^ 3) := by fun_prop
  have he : (fun x : ℝ => x ^ 3) '' Icc (3 / 5 : ℝ) 1 = Icc (27 / 125 : ℝ) 1 := by
    rw [hc.image_Icc_of_strictMono hg]
    norm_num
  refine ⟨hg, hc, hpdCounterexample_content, hpdCounterexample_minimum_volume, ?_, ?_, ?_⟩
  · rw [he]
    convert (cube_interval_mass (3 / 5) 1).trans hpdCounterexample_content using 1 <;> norm_num
  · have h := cube_interval_mass 0 (4 / 5)
    rw [triangular_interval_mass (by norm_num) (by norm_num) (by norm_num)] at h
    norm_num at h
    exact h
  · rw [he]
    norm_num [Real.volume_Icc]

end LectureNotes
