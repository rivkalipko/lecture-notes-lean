import LectureNotes.DKWMaximal
import LectureNotes.DKWCensorBridge
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

theorem dkwCensor_comp {n : ℕ} {u v : ℝ} (huv : u ≤ v) :
    (@dkwCensor n v) = dkwCensor v ∘ dkwCensor u := by
  funext x i
  simp only [dkwCensor, Function.comp_apply, max_assoc, max_eq_right huv]

/-- Observations censored at decreasing thresholds give increasing information. -/
def dkwFiltration {n : ℕ} (u : ℕ → ℝ) (hu : Antitone u) :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin n → ℝ)) :=
  censorGeneratedFiltration (fun i => dkwCensor (u i))
    (fun i => measurable_dkwCensor (u i))
    (fun i j hij => dkwCensor_comp (hu hij))

/-- The tilted count weights form a martingale in reverse threshold order. -/
theorem dkwProductWeight_martingale {n : ℕ} {u : ℕ → ℝ}
    (hu : Antitone u) (hu0 : ∀ i, 0 < u i) (hu1 : ∀ i, u i ≤ 1)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    Martingale (fun i => dkwProductWeight (u i) ℓ) (dkwFiltration (n := n) u hu)
      (dkwProductLaw n) := by
  constructor
  · intro i
    exact (measurable_dkwProductWeight_comap (u i) ℓ).stronglyMeasurable
  · intro i j hij
    exact dkw_censored_condExp_product (hu0 j) (hu1 i) (hu hij) hℓ

/-- A bound for crossing any one of finitely many ordered thresholds. -/
theorem dkw_ordered_grid_crossing_bound {n : ℕ} {u : ℕ → ℝ}
    (hu : Antitone u) (hu0 : ∀ i, 0 < u i) (hu1 : ∀ i, u i ≤ 1)
    {ℓ b : ℝ} (hℓ : 0 ≤ ℓ) (hb : 0 < b) (N : ℕ) :
    (dkwProductLaw n).real {x | ∃ i ≤ N, b ≤ dkwProductWeight (u i) ℓ x} ≤
      (1 + ℓ) ^ n / b := by
  have hh := nonnegative_submartingale_crossing_bound
    (dkwProductWeight_martingale (n := n) hu hu0 hu1 hℓ).submartingale
    (fun i x => dkwProductWeight_nonneg (hu0 i) hℓ x) hb N
  rwa [dkwProductWeight_integral (hu0 N) (hu1 N)] at hh

/-- The crossing bound holds for every finite grid, without assumptions on
how the grid is enumerated. -/
theorem dkw_finite_grid_crossing_bound {n : ℕ} (s : Finset ℝ)
    (hs0 : ∀ u ∈ s, 0 < u) (hs1 : ∀ u ∈ s, u ≤ 1)
    {ℓ b : ℝ} (hℓ : 0 ≤ ℓ) (hb : 0 < b) :
    (dkwProductLaw n).real {x | ∃ u ∈ s, b ≤ dkwProductWeight u ℓ x} ≤
      (1 + ℓ) ^ n / b := by
  classical
  by_cases hs : s.Nonempty
  · have hc : 0 < s.card := Finset.card_pos.mpr hs
    let q : ℕ → Fin s.card := fun i => ⟨s.card - 1 - min i (s.card - 1), by omega⟩
    let u : ℕ → ℝ := fun i => s.orderEmbOfFin rfl (q i)
    have hmem i : u i ∈ s := s.orderEmbOfFin_mem rfl (q i)
    have hu : Antitone u := by
      intro i j hij
      apply (s.orderEmbOfFin rfl).monotone
      change s.card - 1 - min j (s.card - 1) ≤ s.card - 1 - min i (s.card - 1)
      omega
    have hh := dkw_ordered_grid_crossing_bound (n := n) hu
      (fun i => hs0 _ (hmem i)) (fun i => hs1 _ (hmem i)) hℓ hb (s.card - 1)
    refine (measureReal_mono ?_).trans hh
    intro x hx
    rcases hx with ⟨v, hv, hx⟩
    have hr : v ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hv
    rcases hr with ⟨j, hj⟩
    refine ⟨s.card - 1 - j.val, by omega, ?_⟩
    have hq : q (s.card - 1 - j.val) = j := by
      apply Fin.ext
      dsimp only [q]
      have := j.isLt
      omega
    simpa only [u, hq, hj] using hx
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [he, Finset.notMem_empty, false_and, exists_false, setOf_false, measureReal_empty]
    exact div_nonneg (pow_nonneg (by linarith) _) hb.le

end LectureNotes
