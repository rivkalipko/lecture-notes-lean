import LectureNotes.RowDeltaMethod
import LectureNotes.BootstrapIntervals

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
  (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]

/-- Pointwise CDF convergence to an atomless law also controls strict lower
half-lines, with no relation between the row sample spaces. -/
theorem row_strict_cdf_of_cdf (T : ∀ n, Ω n → ℝ)
    (hT : ∀ t, Tendsto (fun n => (P n).real {ω | T n ω ≤ t}) atTop (𝓝 (cdf ν t)))
    (t : ℝ) :
    Tendsto (fun n => (P n).real {ω | T n ω < t}) atTop (𝓝 (cdf ν t)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have hc : ContinuousAt (fun δ : ℝ => cdf ν (t - δ)) 0 :=
      (continuous_cdf_of_atomless ν).continuousAt.comp (by fun_prop)
    have hc' : Tendsto (fun δ : ℝ => cdf ν (t - δ)) (𝓝 0) (𝓝 (cdf ν t)) := by
      simpa using hc.tendsto
    have he := hc'.eventually (lt_mem_nhds ha)
    have hs : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ a < cdf ν (t - δ) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds he] with δ hδ0 hδ
      exact ⟨hδ0, hδ⟩
    obtain ⟨δ, hδ0, hδ⟩ := hs.exists
    filter_upwards [(hT (t - δ)).eventually (lt_mem_nhds hδ)] with n hn
    apply hn.trans_le
    have hsub : {ω | T n ω ≤ t - δ} ⊆ {ω | T n ω < t} := by
      intro ω hω
      change T n ω < t
      change T n ω ≤ t - δ at hω
      linarith
    exact measureReal_mono hsub (measure_ne_top (P n) _)
  · intro b hb
    filter_upwards [(hT t).eventually (gt_mem_nhds hb)] with n hn
    exact (measureReal_mono (μ := P n) (show {ω | T n ω < t} ⊆ {ω | T n ω ≤ t}
      from fun ω h => show T n ω ≤ t from (show T n ω < t from h).le)).trans_lt hn

/-- A consistent random critical value can be used in a varying-row experiment.
The critical value need not be independent of the statistic. -/
theorem row_random_critical_value_cdf (T C : ∀ n, Ω n → ℝ) {c : ℝ}
    (hT : ∀ t, Tendsto (fun n => (P n).real {ω | T n ω ≤ t}) atTop (𝓝 (cdf ν t)))
    (hC : RowProbabilityZero P (fun n ω => C n ω - c)) :
    Tendsto (fun n => (P n).real {ω | T n ω ≤ C n ω}) atTop (𝓝 (cdf ν c)) := by
  have hR : ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ |-(C n ω - c)|})
      atTop (𝓝 0) := by simpa only [RowProbabilityZero, Real.norm_eq_abs, abs_neg] using hC
  have hh := dependent_rows_additive_error_cdf P T (fun n ω => -(C n ω - c)) ν hT hR c
  apply hh.congr
  intro n
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- The same random-critical-value limit for strict rejection or acceptance
boundaries. Atomlessness of the limiting law removes boundary ambiguity. -/
theorem row_random_critical_value_strict_cdf (T C : ∀ n, Ω n → ℝ) {c : ℝ}
    (hT : ∀ t, Tendsto (fun n => (P n).real {ω | T n ω ≤ t}) atTop (𝓝 (cdf ν t)))
    (hC : RowProbabilityZero P (fun n ω => C n ω - c)) :
    Tendsto (fun n => (P n).real {ω | T n ω < C n ω}) atTop (𝓝 (cdf ν c)) := by
  have hR : ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ |-(C n ω - c)|})
      atTop (𝓝 0) := by simpa only [RowProbabilityZero, Real.norm_eq_abs, abs_neg] using hC
  have hd t := dependent_rows_additive_error_cdf P T (fun n ω => -(C n ω - c)) ν hT hR t
  have hh := row_strict_cdf_of_cdf P ν (fun n ω => T n ω + -(C n ω - c)) hd c
  apply hh.congr
  intro n
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- Ordered, consistent random interval endpoints retain their target mass
under rowwise sampling, even with common data and simulation randomness. -/
theorem row_random_interval_probability (T A B : ∀ n, Ω n → ℝ) {a b : ℝ}
    (hT : ∀ t, Tendsto (fun n => (P n).real {ω | T n ω ≤ t}) atTop (𝓝 (cdf ν t)))
    (hA : RowProbabilityZero P (fun n ω => A n ω - a))
    (hB : RowProbabilityZero P (fun n ω => B n ω - b))
    (hmT : ∀ n, Measurable (T n)) (hmA : ∀ n, Measurable (A n))
    (hAB : ∀ n ω, A n ω ≤ B n ω) :
    Tendsto (fun n => (P n).real {ω | T n ω ∈ Icc (A n ω) (B n ω)})
      atTop (𝓝 (cdf ν b - cdf ν a)) := by
  have h₁ := row_random_critical_value_cdf P ν T B hT hB
  have h₂ := row_random_critical_value_strict_cdf P ν T A hT hA
  have he n : (P n).real {ω | T n ω ∈ Icc (A n ω) (B n ω)} =
      (P n).real {ω | T n ω ≤ B n ω} - (P n).real {ω | T n ω < A n ω} := by
    have hs : {ω | T n ω ∈ Icc (A n ω) (B n ω)} =
        {ω | T n ω ≤ B n ω} \ {ω | T n ω < A n ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, mem_Icc, Set.mem_sdiff, not_lt, and_comm]
    rw [hs, measureReal_sdiff]
    · intro ω hω
      exact hω.le.trans (hAB n ω)
    · exact measurableSet_lt (hmT n) (hmA n)
  simp_rw [he]
  exact h₁.sub h₂

/-- Inverting a location pivot in the same varying-row experiment gives a
confidence interval with the corresponding limiting coverage. -/
theorem row_random_interval_coverage (E S A B : ∀ n, Ω n → ℝ) {θ a b : ℝ}
    (hS : ∀ n ω, 0 < S n ω)
    (hT : ∀ t, Tendsto (fun n => (P n).real {ω | (E n ω - θ) / S n ω ≤ t})
      atTop (𝓝 (cdf ν t)))
    (hA : RowProbabilityZero P (fun n ω => A n ω - a))
    (hB : RowProbabilityZero P (fun n ω => B n ω - b))
    (hmT : ∀ n, Measurable (fun ω => (E n ω - θ) / S n ω))
    (hmA : ∀ n, Measurable (A n)) (hAB : ∀ n ω, A n ω ≤ B n ω) :
    Tendsto (fun n => (P n).real {ω | θ ∈ Icc
      (E n ω - B n ω * S n ω) (E n ω - A n ω * S n ω)})
      atTop (𝓝 (cdf ν b - cdf ν a)) := by
  have hh := row_random_interval_probability P ν (fun n ω => (E n ω - θ) / S n ω)
    A B hT hA hB hmT hmA hAB
  apply hh.congr
  intro n
  congr 1
  ext ω
  exact location_pivot_inversion (E n ω) θ (A n ω) (B n ω) (S n ω) (hS n ω)

end LectureNotes
