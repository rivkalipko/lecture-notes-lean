import LectureNotes.Quantiles
import LectureNotes.ConfidenceSets
import LectureNotes.NormalSamplingDistribution
import LectureNotes.AsymptoticTests

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

/-- An atomless distribution places exactly the difference of the quantile
levels between the corresponding endpoints, including either boundary. -/
theorem quantile_interval_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    μ.real (Icc (distributionQuantile μ a) (distributionQuantile μ b)) = b - a := by
  let l := distributionQuantile μ a
  let r := distributionQuantile μ b
  have hl : cdf μ l = a := by rw [cdf_eq_real]; exact distributionQuantile_exact μ a ha
  have hr : cdf μ r = b := by rw [cdf_eq_real]; exact distributionQuantile_exact μ b hb
  change μ.real (Icc l r) = b - a
  rw [← measureReal_congr Ioc_ae_eq_Icc, measureReal_def, ← measure_cdf μ,
    StieltjesFunction.measure_Ioc, hl, hr, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

theorem distributionQuantile_strictMono (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a < b) :
    distributionQuantile μ a < distributionQuantile μ b := by
  by_contra h
  have hm := (monotone_cdf μ) (le_of_not_gt h)
  simp only [cdf_eq_real, distributionQuantile_exact μ a ha,
    distributionQuantile_exact μ b hb] at hm
  exact not_le_of_gt hab hm

theorem pivot_quantile_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {T : Ω → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (hT : HasLaw T μ P) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    P.real {ω | T ω ∈ Icc (distributionQuantile μ a) (distributionQuantile μ b)} = b - a := by
  exact (hT.measureReal_eq (p := fun x => x ∈ Icc
    (distributionQuantile μ a) (distributionQuantile μ b)) measurableSet_Icc).trans
    (quantile_interval_probability μ ha hb hab)

/-- Quantile inversion permits a random positive scale, as in Student intervals.
Only almost-sure positivity is needed. -/
theorem location_quantile_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {T S : Ω → ℝ} {θ : ℝ} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hS : ∀ᵐ ω ∂P, 0 < S ω)
    (hT : HasLaw (fun ω => (T ω - θ) / S ω) μ P) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    P.real {ω | θ ∈ Icc (T ω - distributionQuantile μ b * S ω)
      (T ω - distributionQuantile μ a * S ω)} = b - a := by
  rw [← pivot_quantile_coverage hT ha hb hab]
  apply measureReal_congr
  filter_upwards [hS] with ω hω
  exact propext (location_pivot_inversion _ _ _ _ _ hω).symm

/-- Exact normal location intervals; `a = α/2`, `b = 1-α/2` gives
equal tails, while arbitrary interior levels allow unequal tails. -/
theorem normal_quantile_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {T : Ω → ℝ} {θ : ℝ} {v : ℝ≥0}
    (hv : 0 < v) (hT : HasLaw T (gaussianReal θ v) P) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    P.real {ω | θ ∈ Icc
      (T ω - distributionQuantile (gaussianReal 0 1) b * Real.sqrt v)
      (T ω - distributionQuantile (gaussianReal 0 1) a * Real.sqrt v)} = b - a := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  exact location_quantile_coverage
    (ae_of_all _ (fun _ => Real.sqrt_pos.mpr (by exact_mod_cast hv)))
    (normal_standardize hv hT) ha hb hab

theorem normal_sampleMean_quantile_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    {θ : ℝ} {v : ℝ≥0} (hv : 0 < v)
    (hX : ∀ i, HasLaw (X i) (gaussianReal θ v) P) (hind : iIndepFun X P)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    P.real {ω | θ ∈ Icc
      (sampleMean (fun i => X i ω) - distributionQuantile (gaussianReal 0 1) b * Real.sqrt ((v : ℝ) / n))
      (sampleMean (fun i => X i ω) - distributionQuantile (gaussianReal 0 1) a * Real.sqrt ((v : ℝ) / n))}
      = b - a := by
  simpa using normal_quantile_coverage
    (show 0 < v / (n : ℝ≥0) from div_pos hv (by exact_mod_cast hn))
    (normal_sampleMean hn hX hind) ha hb hab

/-- Exact posterior content for any Gaussian posterior with positive variance.
This is a credible interval statement under the posterior measure. -/
theorem gaussian_credible_interval (m : ℝ) (v : ℝ≥0) (hv : 0 < v)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    (gaussianReal m v).real (Icc
      (m + distributionQuantile (gaussianReal 0 1) a * Real.sqrt v)
      (m + distributionQuantile (gaussianReal 0 1) b * Real.sqrt v)) = b - a := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have h := pivot_quantile_coverage
    (normal_standardize hv (show HasLaw id (gaussianReal m v) (gaussianReal m v) from
      ⟨measurable_id.aemeasurable, Measure.map_id⟩)) ha hb hab
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hv)
  convert h using 2
  ext x
  simp only [mem_Icc, mem_setOf_eq, id_eq, le_div_iff₀ hs, div_le_iff₀ hs]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- A weakly convergent pivot yields the claimed interval probability when
its limiting distribution has no atoms. -/
theorem asymptotic_quantile_coverage {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hT : ConvergesInDistribution P Q T Z) (hZ : HasLaw Z μ Q)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => P.real {ω | T n ω ∈ Icc
      (distributionQuantile μ a) (distributionQuantile μ b)}) atTop (𝓝 (b - a)) := by
  have hboundary : Q.map Z (frontier (Icc (distributionQuantile μ a) (distributionQuantile μ b))) = 0 := by
    rw [hZ.map_eq]
    by_cases h : distributionQuantile μ a ≤ distributionQuantile μ b
    · rw [frontier_Icc h]
      exact ((finite_singleton _).insert _).measure_zero μ
    · rw [Icc_eq_empty_of_lt (lt_of_not_ge h)]
      simp
  have h := asymptotic_rejection_probability hT _ measurableSet_Icc hboundary
  rwa [pivot_quantile_coverage hZ ha hb hab] at h

end LectureNotes
