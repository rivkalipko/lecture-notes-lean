import LectureNotes.ConfidenceLevel

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- Exact pointwise coverage in L11 Remark 1: the limit at every fixed true
parameter equals the target, rather than merely being at least the target. -/
def HasExactPointwiseAsymptoticCoverage {Ω Θ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ]
    (P : Θ → Measure Ω) (C : ℕ → Ω → Set Θ) (γ : ℝ) : Prop :=
  ∀ θ, Tendsto (fun n => coverage P (C n) θ) atTop (𝓝 γ)

/-- The exact worst-case limit displayed in L11 Remark 1. This is convergence
of the infimum of coverage; it is not uniform convergence of all coverage
probabilities to the target. Some parameters may permanently overcover. -/
def HasExactAsymptoticConfidenceLevel {Ω Θ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ]
    (P : Θ → Measure Ω) (C : ℕ → Ω → Set Θ) (γ : ℝ) : Prop :=
  Tendsto (fun n => confidenceLevel P (C n)) atTop (𝓝 γ)

variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]

theorem exact_pointwise_coverage_implies_lower_coverage
    {P : Θ → Measure Ω} {C : ℕ → Ω → Set Θ} {γ : ℝ}
    (h : HasExactPointwiseAsymptoticCoverage P C γ) :
    HasPointwiseAsymptoticCoverage P C γ := by
  intro θ ε hε
  exact ((tendsto_order.mp (h θ)).1 (γ - ε) (by linarith)).mono (fun _ hn => hn.le)

/-- An exact worst-case limit supplies the uniform lower bound, even if
pointwise coverage is strictly above the target at some parameters. -/
theorem exact_confidence_level_implies_uniform_lower_coverage
    {P : Θ → Measure Ω} {C : ℕ → Ω → Set Θ} {γ : ℝ}
    (h : HasExactAsymptoticConfidenceLevel P C γ) :
    HasUniformAsymptoticCoverage P C γ := by
  intro ε hε
  filter_upwards [(tendsto_order.mp h).1 (γ - ε) (by linarith)] with n hn θ
  exact hn.le.trans (confidenceLevel_le_coverage P (C n) θ)

/-- One parameter attaining the target asymptotically supplies the upper bound
on the worst-case level. Uniform lower coverage then makes its limit exact. -/
theorem exact_confidence_level_of_uniform_lower_and_one_exact
    [Nonempty Θ] {P : Θ → Measure Ω} {C : ℕ → Ω → Set Θ} {γ : ℝ}
    (hLower : HasUniformAsymptoticCoverage P C γ) (θ₀ : Θ)
    (hExact : Tendsto (fun n => coverage P (C n) θ₀) atTop (𝓝 γ)) :
    HasExactAsymptoticConfidenceLevel P C γ := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hLower ((γ - a) / 2) (by linarith)] with n hn
    have hlev : γ - (γ - a) / 2 ≤ confidenceLevel P (C n) :=
      (hasConfidenceLevel_iff_le_confidenceLevel P (C n) _).mp hn
    linarith
  · intro b hb
    filter_upwards [(tendsto_order.mp hExact).2 b hb] with n hn
    exact (confidenceLevel_le_coverage P (C n) θ₀).trans_lt hn

/-- Within the source's pointwise-exact setting, its displayed worst-case
limit is equivalent to the additional uniform lower-coverage requirement. -/
theorem exact_confidence_level_iff_uniform_lower_of_exact_pointwise
    [Nonempty Θ] {P : Θ → Measure Ω} {C : ℕ → Ω → Set Θ} {γ : ℝ}
    (h : HasExactPointwiseAsymptoticCoverage P C γ) :
    HasExactAsymptoticConfidenceLevel P C γ ↔ HasUniformAsymptoticCoverage P C γ := by
  constructor
  · exact exact_confidence_level_implies_uniform_lower_coverage
  · intro hLower
    obtain ⟨θ₀⟩ := ‹Nonempty Θ›
    exact exact_confidence_level_of_uniform_lower_and_one_exact hLower θ₀ (h θ₀)

/-- A finite, genuinely probabilistic counterexample to interpreting convergence
of worst-case coverage as exact convergence at every parameter. The false
parameter is included only on one fair-coin outcome; true is always included. -/
def overcoverageExperiment (_θ : Bool) : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true

def overcoverageRegion (_n : ℕ) (x : Bool) : Set Bool := {θ | θ = true ∨ x = true}

instance overcoverageExperiment_probability (θ : Bool) :
    IsProbabilityMeasure (overcoverageExperiment θ) := by
  constructor
  simpa [overcoverageExperiment] using ENNReal.inv_two_add_inv_two

private theorem overcoverageRegion_false (n : ℕ) :
    coverage overcoverageExperiment (overcoverageRegion n) false = (1 / 2 : ℝ) := by
  norm_num [coverage, overcoverageRegion, overcoverageExperiment, Measure.real,
    Measure.add_apply, Measure.smul_apply, ENNReal.toReal_add, ENNReal.toReal_div]

private theorem overcoverageRegion_true (n : ℕ) :
    coverage overcoverageExperiment (overcoverageRegion n) true = (1 : ℝ) := by
  norm_num [coverage, overcoverageRegion, overcoverageExperiment, Measure.real,
    Measure.add_apply, Measure.smul_apply, ENNReal.toReal_add, ENNReal.toReal_div]

theorem exact_worst_case_coverage_does_not_force_exact_pointwise :
    HasExactAsymptoticConfidenceLevel overcoverageExperiment overcoverageRegion (1 / 2) ∧
      ¬ HasExactPointwiseAsymptoticCoverage overcoverageExperiment overcoverageRegion (1 / 2) := by
  constructor
  · have he n : confidenceLevel overcoverageExperiment (overcoverageRegion n) = (1 / 2 : ℝ) := by
      apply le_antisymm
      · simpa only [overcoverageRegion_false] using
          confidenceLevel_le_coverage overcoverageExperiment (overcoverageRegion n) false
      · apply (hasConfidenceLevel_iff_le_confidenceLevel _ _ _).mp
        intro θ
        cases θ
        · exact (overcoverageRegion_false n).ge
        · rw [overcoverageRegion_true]
          norm_num
    change Tendsto _ atTop _
    simp_rw [he]
    exact tendsto_const_nhds
  · intro h
    have ht := h true
    simp only [overcoverageRegion_true] at ht
    have he : (1 : ℝ) = 1 / 2 := tendsto_nhds_unique tendsto_const_nhds ht
    norm_num at he

/-- The parameter excluded at each sample size moves with that size. Every
fixed parameter is eventually included on precisely the true coin outcome. -/
def movingCoverageExperiment (_θ : ℕ) : Measure Bool := overcoverageExperiment false

def movingCoverageRegion (n : ℕ) (x : Bool) : Set ℕ := {θ | θ < n ∧ x = true}

instance movingCoverageExperiment_probability (θ : ℕ) :
    IsProbabilityMeasure (movingCoverageExperiment θ) :=
  overcoverageExperiment_probability false

private theorem movingCoverageRegion_coverage (n θ : ℕ) :
    coverage movingCoverageExperiment (movingCoverageRegion n) θ =
      if θ < n then (1 / 2 : ℝ) else 0 := by
  by_cases h : θ < n
  · norm_num [coverage, movingCoverageExperiment, movingCoverageRegion, h,
      overcoverageExperiment, Measure.real, Measure.add_apply, Measure.smul_apply,
      ENNReal.toReal_add, ENNReal.toReal_div]
  · simp [coverage, movingCoverageRegion, h]

/-- L11 Remark 1's moving-bad-parameter phenomenon, in an actual probability
model: pointwise exact coverage is one half, but the confidence level is zero
at every sample size and the uniform lower-coverage condition fails. -/
theorem pointwise_exact_coverage_does_not_force_uniform_lower :
    HasExactPointwiseAsymptoticCoverage movingCoverageExperiment movingCoverageRegion (1 / 2) ∧
    (∀ n, confidenceLevel movingCoverageExperiment (movingCoverageRegion n) = 0) ∧
    ¬ HasUniformAsymptoticCoverage movingCoverageExperiment movingCoverageRegion (1 / 2) := by
  have hbad n : coverage movingCoverageExperiment (movingCoverageRegion n) n = 0 := by
    simp [movingCoverageRegion_coverage]
  refine ⟨?_, ?_, ?_⟩
  · intro θ
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop θ] with n hn
    simp [movingCoverageRegion_coverage, hn]
  · intro n
    apply le_antisymm
    · simpa only [hbad] using
        confidenceLevel_le_coverage movingCoverageExperiment (movingCoverageRegion n) n
    · exact (confidenceLevel_bounds movingCoverageExperiment (movingCoverageRegion n)).1
  · intro h
    obtain ⟨n, hn⟩ := (h (1 / 4) (by norm_num)).exists
    have hb := hn n
    rw [hbad] at hb
    norm_num at hb

end LectureNotes
