import LectureNotes.UniformEndpoint
import LectureNotes.DensityTransform
import LectureNotes.StochasticOrder

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

/-- L3 Remark 2, realized on one uniform unit-interval probability space. -/
def alternatingUniform (n : ℕ) : ℝ → ℝ := if Even n then id else fun x => x - 1

local instance unitUniformProbability : IsProbabilityMeasure (uniformEndpointLaw 1) :=
  uniformEndpointLaw_probability (by norm_num)

theorem alternatingUniform_measurable (n : ℕ) : Measurable (alternatingUniform n) := by
  unfold alternatingUniform
  split_ifs <;> fun_prop

/-- Even terms have the uniform [0,1] law. -/
theorem alternatingUniform_even_law (n : ℕ) :
    (uniformEndpointLaw 1).map (alternatingUniform (2 * n)) = volume.restrict (Icc (0 : ℝ) 1) := by
  simp [alternatingUniform, even_two_mul, uniformEndpointLaw]

/-- Odd terms have the uniform [-1,0] law. -/
theorem alternatingUniform_odd_law (n : ℕ) :
    (uniformEndpointLaw 1).map (alternatingUniform (2 * n + 1)) = volume.restrict (Icc (-1 : ℝ) 0) := by
  simp only [alternatingUniform, Nat.not_even_two_mul_add_one, if_false]
  rw [← uniformEndpointLaw_density (by norm_num : (0 : ℝ) < 1), density_sub_const]
  have he : (fun y => ENNReal.ofReal (uniformEndpointDensity 1 (y + 1))) =
      (Icc (-1 : ℝ) 0).indicator (fun _ => (1 : ENNReal)) := by
    funext y
    have hy : y + 1 ∈ Icc (0 : ℝ) 1 ↔ y ∈ Icc (-1 : ℝ) 0 := by
      simp only [mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    by_cases h : y ∈ Icc (-1 : ℝ) 0 <;> simp [uniformEndpointDensity, hy, h]
  rw [he, withDensity_indicator measurableSet_Icc, withDensity_const, one_smul]

theorem alternatingUniform_cdf (n : ℕ) (t : ℝ) :
    cdf ((uniformEndpointLaw 1).map (alternatingUniform n)) t =
      if Even n then max (min t 1) 0 else max (min (t + 1) 1) 0 := by
  by_cases hn : Even n
  · simp [alternatingUniform, hn, uniformEndpoint_cdf (by norm_num : (0 : ℝ) < 1)]
  · simp only [alternatingUniform, hn, if_false]
    rw [cdf_sub_const, uniformEndpoint_cdf (by norm_num : (0 : ℝ) < 1), div_one]

/-- The entire sequence is bounded by one almost surely, uniformly in n. -/
theorem alternatingUniform_ae_bounded :
    ∀ᵐ x ∂uniformEndpointLaw 1, ∀ n, |alternatingUniform n x| ≤ 1 := by
  have he : uniformEndpointLaw 1 = volume.restrict (Icc (0 : ℝ) 1) := by simp [uniformEndpointLaw]
  rw [he]
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  intro n
  unfold alternatingUniform
  split_ifs
  · change |x| ≤ 1
    rw [abs_of_nonneg hx.1]
    exact hx.2
  · rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
    linarith [hx.1]

theorem alternatingUniform_stochasticBigO :
    StochasticBigO (P := uniformEndpointLaw 1) alternatingUniform (fun _ => 1) := by
  refine ⟨by simp, fun ε hε => ⟨2, by norm_num, fun n => ?_⟩⟩
  have hz : uniformEndpointLaw 1 {x | 2 * |(1 : ℝ)| < |alternatingUniform n x|} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [alternatingUniform_ae_bounded] with x hx
    simpa using (show ¬(2 : ℝ) < |alternatingUniform n x| by linarith [hx n])
  simpa only [measureReal_def, hz, ENNReal.toReal_zero] using hε

/-- No random variable on any probability space is a distributional limit of
the alternating sequence. The two constant subsequences have different laws. -/
theorem alternatingUniform_not_convergesInDistribution
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q] (Z : Ω → ℝ) :
    ¬ ConvergesInDistribution (uniformEndpointLaw 1) Q alternatingUniform Z := by
  intro h
  let L : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨(uniformEndpointLaw 1).map (alternatingUniform n),
      Measure.isProbabilityMeasure_map (alternatingUniform_measurable n).aemeasurable⟩
  let ν : ProbabilityMeasure ℝ := ⟨Q.map Z, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩
  have ht : Tendsto L atTop (𝓝 ν) := h.tendsto
  have heven : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    apply tendsto_atTop_mono (f := id) (fun n => by dsimp; omega) tendsto_id
  have hodd : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp heven
  have h0 : Tendsto (fun _ : ℕ => L 0) atTop (𝓝 ν) := by
    convert ht.comp heven using 1
    funext n
    apply Subtype.ext
    change (uniformEndpointLaw 1).map (alternatingUniform 0) =
      (uniformEndpointLaw 1).map (alternatingUniform (2 * n))
    simp [alternatingUniform, even_two_mul]
  have h1 : Tendsto (fun _ : ℕ => L 1) atTop (𝓝 ν) := by
    convert ht.comp hodd using 1
    funext n
    apply Subtype.ext
    change (uniformEndpointLaw 1).map (alternatingUniform 1) =
      (uniformEndpointLaw 1).map (alternatingUniform (2 * n + 1))
    simp [alternatingUniform, Nat.not_even_two_mul_add_one]
  have heq : L 0 = L 1 :=
    (tendsto_nhds_unique tendsto_const_nhds h0).trans
      (tendsto_nhds_unique tendsto_const_nhds h1).symm
  have hc := congrArg (fun ρ : ProbabilityMeasure ℝ => cdf (ρ : Measure ℝ) 0) heq
  change cdf ((uniformEndpointLaw 1).map (alternatingUniform 0)) 0 =
    cdf ((uniformEndpointLaw 1).map (alternatingUniform 1)) 0 at hc
  rw [alternatingUniform_cdf, alternatingUniform_cdf] at hc
  norm_num at hc

end LectureNotes
