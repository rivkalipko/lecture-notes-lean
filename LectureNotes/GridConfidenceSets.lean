import LectureNotes.ConfidenceSets
import LectureNotes.QuantileConvergence

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- Invert parameter-specific tests only at the specified finite grid points. -/
def gridConfidenceSet {Θ Ω : Type*} (grid : Finset Θ)
    (T critical : Θ → Ω → ℝ) (ω : Ω) : Set Θ :=
  {θ | θ ∈ grid ∧ T θ ω ≤ critical θ ω}

theorem gridConfidenceSet_mem {Θ Ω : Type*} (grid : Finset Θ)
    (T critical : Θ → Ω → ℝ) (θ : Θ) (ω : Ω) :
    θ ∈ gridConfidenceSet grid T critical ω ↔ θ ∈ grid ∧ T θ ω ≤ critical θ ω := Iff.rfl

theorem gridConfidenceSet_subset {Θ Ω : Type*} (grid : Finset Θ)
    (T critical : Θ → Ω → ℝ) (ω : Ω) :
    gridConfidenceSet grid T critical ω ⊆ (grid : Set Θ) := fun _ h => h.1

/-- A literal finite-grid confidence set cannot cover any parameter absent
from its grid, irrespective of how accurately the tests are calibrated. -/
theorem gridConfidenceSet_coverage_of_not_mem {Θ Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (grid : Finset Θ) (T critical : Θ → Ω → ℝ)
    {θ : Θ} (hθ : θ ∉ grid) :
    P.real {ω | θ ∈ gridConfidenceSet grid T critical ω} = 0 := by
  have he : {ω | θ ∈ gridConfidenceSet grid T critical ω} = ∅ := by
    ext ω
    simp [gridConfidenceSet, hθ]
  rw [he, measureReal_empty]

/-- At a grid point, coverage is precisely the acceptance probability of
that point's test. No independence across grid-point tests is required. -/
theorem gridConfidenceSet_coverage_identity {Θ Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (grid : Finset Θ) (T critical : Θ → Ω → ℝ)
    {θ : Θ} (hθ : θ ∈ grid) :
    P.real {ω | θ ∈ gridConfidenceSet grid T critical ω} =
      P.real {ω | T θ ω ≤ critical θ ω} := by
  simp only [gridConfidenceSet, mem_ofPred_eq, hθ, true_and]

/-- L11's grid-bootstrap algorithm has the usual pointwise coverage at a
true parameter included in the grid, under the explicit bootstrap validity
conditions at that parameter. Values between grid points require an additional
interpolation argument and are not silently filled in. -/
theorem grid_bootstrap_confidence_coverage {Θ Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (grid : Finset Θ) {θ : Θ} (hθ : θ ∈ grid)
    (T : ℕ → Θ → Ω → ℝ) (B : ℕ → Θ → Ω → Measure ℝ)
    [∀ n θ ω, IsProbabilityMeasure (B n θ ω)]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    {Z : Ω' → ℝ}
    (hT : ConvergesInDistribution P Q (fun n => T n θ) Z) (hZ : HasLaw Z ν Q)
    (hstrict : StrictMono (cdf ν))
    (hconv : ∀ᵐ ω ∂P, ∀ x, Tendsto (fun n => cdf (B n θ ω) x) atTop (𝓝 (cdf ν x)))
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hBm : ∀ n, Measurable (fun ω => distributionQuantile (B n θ ω) q)) :
    Tendsto (fun n => P.real {ω | θ ∈ gridConfidenceSet grid (T n)
      (fun t w => distributionQuantile (B n t w) q) ω}) atTop (𝓝 q) := by
  simp_rw [gridConfidenceSet_coverage_identity P grid _ _ hθ]
  have hc := bootstrap_quantile_consistency (fun n ω => B n θ ω) ν hstrict hconv hq
    (fun n => (hBm n).aemeasurable)
  have hh := random_critical_value_probability hT hZ hc (fun n => (hBm n).aemeasurable)
  rw [cdf_eq_real, distributionQuantile_exact ν q hq] at hh
  exact hh

end LectureNotes
