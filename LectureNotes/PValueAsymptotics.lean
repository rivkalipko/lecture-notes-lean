import LectureNotes.PValues
import LectureNotes.MeanTests
import LectureNotes.UniformEndpoint
import LectureNotes.UniformCDFConvergence

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

local instance : IsProbabilityMeasure (uniformEndpointLaw 1) :=
  uniformEndpointLaw_probability (by norm_num)

local instance : NullSingletonClass (uniformEndpointLaw 1) := by
  simp only [uniformEndpointLaw, ENNReal.ofReal_one, inv_one, one_smul]
  infer_instance

theorem normalTwoSidedPValue_continuous : Continuous (normalTwoSidedPValue (id : ℝ → ℝ)) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  exact continuous_const.mul
    (continuous_const.sub ((continuous_cdf_of_atomless (gaussianReal 0 1)).comp continuous_abs))

theorem normalTwoSidedPValue_measurable {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → ℝ} (hT : Measurable T) : Measurable (normalTwoSidedPValue T) :=
  normalTwoSidedPValue_continuous.measurable.comp hT

/-- Under the exact standard-normal null, the actual two-sided p-value has
uniform law, including its endpoint behavior. -/
theorem normalTwoSidedPValue_uniform_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → ℝ}
    (hTm : Measurable T) (hT : HasLaw T (gaussianReal 0 1) P) :
    HasLaw (normalTwoSidedPValue T) (uniformEndpointLaw 1) P := by
  have hm := normalTwoSidedPValue_measurable hTm
  have hp := normalTwoSidedPValue_valid hTm hT
  refine ⟨hm.aemeasurable, ?_⟩
  have : IsProbabilityMeasure (P.map (normalTwoSidedPValue T)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  apply Measure.eq_of_cdf
  ext t
  rw [cdf_eq_real, map_measureReal_apply hm measurableSet_Iic,
    uniformEndpoint_cdf (by norm_num : (0 : ℝ) < 1), div_one]
  change P.real {ω | normalTwoSidedPValue T ω ≤ t} = max (min t 1) 0
  by_cases ht0 : t < 0
  · have he : {ω | normalTwoSidedPValue T ω ≤ t} = ∅ := by
      ext ω
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact not_le.mpr (ht0.trans_le (hp.2.1 ω).1)
    rw [he, measureReal_empty, min_eq_left (by linarith), max_eq_right ht0.le]
  · have ht0' : 0 ≤ t := le_of_not_gt ht0
    by_cases ht1 : 1 ≤ t
    · have he : {ω | normalTwoSidedPValue T ω ≤ t} = univ := by
        ext ω
        simp only [mem_setOf_eq, mem_univ, iff_true]
        exact (hp.2.1 ω).2.trans ht1
      rw [he, probReal_univ, min_eq_right ht1, max_eq_left zero_le_one]
    · have ht1' : t < 1 := lt_of_not_ge ht1
      rw [min_eq_left ht1'.le, max_eq_left ht0']
      by_cases hz : t = 0
      · subst t
        exact le_antisymm (hp.2.2 () (mem_univ _) 0 ⟨le_rfl, zero_le_one⟩)
          (measureReal_nonneg)
      · exact normalTwoSidedPValue_exact hTm hT ⟨lt_of_le_of_ne ht0' (Ne.symm hz), ht1'⟩

/-- A standard-normal limit for a statistic yields a uniform limit for the
p-values computed with the normal two-sided formula. -/
theorem asymptotic_normalTwoSidedPValue_uniform {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : ℕ → Ω → ℝ}
    (hT : ConvergesInDistribution P (gaussianReal 0 1) T id) :
    ConvergesInDistribution P (uniformEndpointLaw 1)
      (fun n => normalTwoSidedPValue (T n)) id := by
  have h := continuous_mapping_distribution normalTwoSidedPValue_continuous hT
  have hl := normalTwoSidedPValue_uniform_law measurable_id
    (HasLaw.id : HasLaw id (gaussianReal 0 1) (gaussianReal 0 1))
  refine ⟨h.forall_aemeasurable, measurable_id.aemeasurable, ?_⟩
  convert! h.tendsto using 2
  congr 1
  apply Subtype.ext
  simpa only [id_eq, Measure.map_id] using hl.map_eq.symm

/-- Interior rejection probabilities computed from asymptotic normal
p-values converge to their nominal levels. -/
theorem asymptotic_normalTwoSidedPValue_exact {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : ℕ → Ω → ℝ}
    (hT : ConvergesInDistribution P (gaussianReal 0 1) T id)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω | normalTwoSidedPValue (T n) ω ≤ α}) atTop (𝓝 α) := by
  have h := asymptotic_rejection_probability (asymptotic_normalTwoSidedPValue_uniform hT)
    (Iic α) measurableSet_Iic (by simp only [Measure.map_id, frontier_Iic, measure_singleton])
  have hc : (uniformEndpointLaw 1).real (Iic α) = α := by
    rw [← cdf_eq_real, uniformEndpoint_cdf (by norm_num : (0 : ℝ) < 1), div_one,
      min_eq_left hα.2.le, max_eq_left hα.1.le]
  change Tendsto (fun n => P.real {ω | normalTwoSidedPValue (T n) ω ≤ α})
    atTop (𝓝 ((uniformEndpointLaw 1).real (Iic α))) at h
  rwa [hc] at h

/-- The actual sample t statistic from an arbitrary IID finite-variance
population gives asymptotically uniform normal p-values under its mean null. -/
theorem iid_oneSampleT_pValue_uniform {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[X 0; P]) {μ₀ : ℝ} (hnull : P[X 0] = μ₀) :
    ConvergesInDistribution P (uniformEndpointLaw 1)
      (fun n => normalTwoSidedPValue (fun ω =>
        oneSampleTStatistic (fun i : Fin (n + 1) => X i ω) μ₀)) id := by
  have h := iid_oneSampleT_clt hXm hX hind hident hv
  rw [hnull] at h
  exact asymptotic_normalTwoSidedPValue_uniform h

theorem iid_oneSampleT_pValue_exact {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[X 0; P]) {μ₀ : ℝ} (hnull : P[X 0] = μ₀)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω | normalTwoSidedPValue (fun ω =>
      oneSampleTStatistic (fun i : Fin (n + 1) => X i ω) μ₀) ω ≤ α}) atTop (𝓝 α) := by
  have h := iid_oneSampleT_clt hXm hX hind hident hv
  rw [hnull] at h
  exact asymptotic_normalTwoSidedPValue_exact h hα

end LectureNotes
