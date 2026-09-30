import LectureNotes.Quantiles
import LectureNotes.NormalSamplingDistribution

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- Exact lower-tail probability under an arbitrary nondegenerate normal law. -/
theorem normal_lower_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {T : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hv : 0 < v)
    (hT : HasLaw T (gaussianReal μ v) P) (c : ℝ) :
    P.real {ω | T ω ≤ c} = cdf (gaussianReal 0 1) ((c - μ) / Real.sqrt v) := by
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hv)
  have he : {ω | T ω ≤ c} = {ω | (T ω - μ) / Real.sqrt v ≤ (c - μ) / Real.sqrt v} := by
    ext ω
    simp only [mem_setOf_eq, div_le_div_iff_of_pos_right hs, sub_le_sub_iff_right]
  rw [he, (normal_standardize hv hT).measureReal_eq measurableSet_Iic, cdf_eq_real]
  rfl

/-- Exact upper-tail power, with rejection strictly above the critical value. -/
theorem normal_upper_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hv : 0 < v) (hm : Measurable T) (hT : HasLaw T (gaussianReal μ v) P) (c : ℝ) :
    P.real {ω | c < T ω} = 1 - cdf (gaussianReal 0 1) ((c - μ) / Real.sqrt v) := by
  have he : {ω | c < T ω} = {ω | T ω ≤ c}ᶜ := by ext ω; simp
  rw [he, measureReal_compl (measurableSet_le hm measurable_const), probReal_univ,
    normal_lower_tail hv hT]

/-- Exact two-sided power. Both tails are retained; discarding one tail gives
an approximation and must not be presented as an exact sample-size equation. -/
theorem normal_two_sided_power {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hv : 0 < v) (hm : Measurable T) (hT : HasLaw T (gaussianReal μ v) P)
    (l r : ℝ) (hlr : l ≤ r) :
    P.real {ω | T ω < l ∨ r < T ω} =
      1 - (cdf (gaussianReal 0 1) ((r - μ) / Real.sqrt v) -
        cdf (gaussianReal 0 1) ((l - μ) / Real.sqrt v)) := by
  have : NullSingletonClass (gaussianReal μ v) := nullSingletonClass_gaussianReal hv.ne'
  have he : {ω | T ω < l ∨ r < T ω} = {ω | T ω ∈ Icc l r}ᶜ := by
    ext ω; simp only [mem_setOf_eq, mem_compl_iff, mem_Icc, not_and_or, not_le]
  have hc : P.real {ω | T ω ∈ Icc l r} =
      (gaussianReal μ v).real (Iic r) - (gaussianReal μ v).real (Iic l) := by
    have heq : P.real {ω | T ω ∈ Icc l r} = (gaussianReal μ v).real (Icc l r) :=
      hT.measureReal_eq (p := fun x => x ∈ Icc l r) measurableSet_Icc
    rw [heq, ← measureReal_congr Ioc_ae_eq_Icc]
    rw [measureReal_def, ← measure_cdf (gaussianReal μ v), StieltjesFunction.measure_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr ((monotone_cdf _) hlr))]
    simp only [cdf_eq_real, measure_cdf]
  have ht (x : ℝ) : (gaussianReal μ v).real (Iic x) =
      cdf (gaussianReal 0 1) ((x - μ) / Real.sqrt v) := by
    exact (hT.measureReal_eq (p := fun y => y ≤ x) measurableSet_Iic).symm.trans
      (normal_lower_tail hv hT x)
  have hC : MeasurableSet {ω | T ω ∈ Icc l r} := measurableSet_Icc.preimage hm
  rw [he, measureReal_compl hC, probReal_univ, hc, ht, ht]

/-- A normal upper-tail quantile test has its advertised exact size. -/
theorem normal_upper_quantile_size {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hv : 0 < v) (hm : Measurable T) (hT : HasLaw T (gaussianReal μ v) P)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    P.real {ω | μ + distributionQuantile (gaussianReal 0 1) (1 - α) * Real.sqrt v < T ω} = α := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hs : Real.sqrt (v : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hv)).ne'
  rw [normal_upper_tail hv hm hT]
  simp only [add_sub_cancel_left, mul_div_cancel_right₀ _ hs, cdf_eq_real]
  rw [distributionQuantile_exact _ _ (by constructor <;> linarith [hα.1, hα.2])]
  ring

/-- Every nondegenerate normal CDF is strictly increasing. In particular,
the quantile convergence theorem applies to a standard-normal bootstrap limit. -/
theorem gaussian_cdf_strictMono (μ : ℝ) (v : ℝ≥0) (hv : 0 < v) :
    StrictMono (cdf (gaussianReal μ v)) := by
  intro x y hxy
  have hvol : (volume : Measure ℝ) (Ioc x y) ≠ 0 := by
    rw [Real.volume_Ioc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hxy)).ne'
  have hne : (gaussianReal μ v) (Ioc x y) ≠ 0 := fun h =>
    hvol ((gaussianReal_absolutelyContinuous' μ hv.ne') h)
  rw [← measure_cdf (gaussianReal μ v), StieltjesFunction.measure_Ioc] at hne
  exact sub_pos.mp (ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hne))

end LectureNotes
