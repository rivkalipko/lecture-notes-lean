import LectureNotes.Foundations
import Mathlib.Probability.Martingale.OptionalStopping

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

/-- The real-probability form of Doob's finite-horizon inequality used for
empirical counts. No independence of the crossing events is assumed. -/
theorem nonnegative_submartingale_crossing_bound {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : ℕ → Ω → ℝ}
    {ℱ : Filtration ℕ mΩ} (hf : Submartingale f ℱ P)
    (hf0 : ∀ i ω, 0 ≤ f i ω) {b : ℝ} (hb : 0 < b) (N : ℕ) :
    P.real {ω | ∃ i ≤ N, b ≤ f i ω} ≤ (∫ ω, f N ω ∂P) / b := by
  let b' : ℝ≥0 := ⟨b, hb.le⟩
  let A := {ω | (b' : ℝ) ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun i => f i ω)}
  have hd := maximal_ineq hf (show 0 ≤ f from hf0) (ε := b') N
  have hs : (∫ ω in A, f N ω ∂P) ≤ ∫ ω, f N ω ∂P :=
    setIntegral_le_integral (hf.integrable N) (ae_of_all _ (hf0 N))
  have hn : 0 ≤ ∫ ω in A, f N ω ∂P := integral_nonneg (hf0 N)
  have hr := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hd
  change (b' * P A).toReal ≤ (ENNReal.ofReal (∫ ω in A, f N ω ∂P)).toReal at hr
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal hn] at hr
  have he : A = {ω | ∃ i ≤ N, b ≤ f i ω} := by
    ext ω
    simp only [A, mem_ofPred_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff, b']
    rfl
  rw [he] at hr hs
  apply (le_div_iff₀ hb).mpr
  simpa only [b', measureReal_def, mul_comm] using! hr.trans hs

/-- Censor maps indexed by an increasingly informative sequence generate a
filtration. This will be instantiated by decreasing uniform thresholds. -/
def censorGeneratedFiltration {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (C : ℕ → Ω → Ω) (hC : ∀ i, Measurable (C i))
    (hcomp : ∀ i j, i ≤ j → C i = C i ∘ C j) : Filtration ℕ mΩ where
  seq i := mΩ.comap (C i)
  mono' i j hij := MeasurableSpace.comap_le_comap_of_eq_comp (C i) (hC i) (hcomp i j hij)
  le' i := (hC i).comap_le

end LectureNotes
