import LectureNotes.LikelihoodRepresentationMinimal

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- The state space of the full ordered sample, including repeated values. -/
def SortedSample (n : ℕ) := {x : Fin n → ℝ // Monotone x}

instance sortedSample_measurableSpace (n : ℕ) : MeasurableSpace (SortedSample n) :=
  inferInstanceAs (MeasurableSpace {x : Fin n → ℝ // Monotone x})

theorem monotone_sample_measurableSet (n : ℕ) : MeasurableSet {x : Fin n → ℝ | Monotone x} := by
  simp only [Monotone, setOf_forall]
  measurability

instance sortedSample_standardBorel (n : ℕ) : StandardBorelSpace (SortedSample n) :=
  (monotone_sample_measurableSet n).standardBorel

instance sortedSample_nonempty (n : ℕ) : Nonempty (SortedSample n) :=
  ⟨⟨fun _ => 0, fun _ _ _ => le_rfl⟩⟩

/-- All n order statistics, represented as a monotone tuple. -/
def sortedSample {n : ℕ} (x : Fin n → ℝ) : SortedSample n :=
  ⟨x ∘ Tuple.sort x, Tuple.monotone_sort x⟩

theorem sortedSample_measurable {n : ℕ} : Measurable (sortedSample : (Fin n → ℝ) → SortedSample n) := by
  have hm : Measurable (fun x : Fin n → ℝ => x ∘ Tuple.sort x) := by
    intro B hB
    have he : (fun x : Fin n → ℝ => x ∘ Tuple.sort x) ⁻¹' B =
        ⋃ σ : Equiv.Perm (Fin n), {x | Monotone (x ∘ σ)} ∩ (fun x => x ∘ σ) ⁻¹' B := by
      ext x
      constructor
      · intro hx
        exact mem_iUnion.mpr ⟨Tuple.sort x, Tuple.monotone_sort x, hx⟩
      · intro hx
        obtain ⟨σ, hσ, hx⟩ := mem_iUnion.mp hx
        have hsort : x ∘ σ = x ∘ Tuple.sort x := Tuple.comp_sort_eq_comp_iff_monotone.mpr hσ
        change x ∘ Tuple.sort x ∈ B
        change x ∘ σ ∈ B at hx
        rw [← hsort]
        exact hx
    rw [he]
    apply MeasurableSet.iUnion
    intro σ
    have hmσ : Measurable (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
    exact ((monotone_sample_measurableSet n).preimage hmσ).inter (hmσ hB)
  exact hm.subtype_mk

theorem sortedSample_prod {n : ℕ} {M : Type*} [CommMonoid M]
    (f : ℝ → M) (x : Fin n → ℝ) :
    (∏ i, f ((sortedSample x).val i)) = ∏ i, f (x i) := by
  exact Equiv.prod_comp (Tuple.sort x) (fun i => f (x i))

end LectureNotes
