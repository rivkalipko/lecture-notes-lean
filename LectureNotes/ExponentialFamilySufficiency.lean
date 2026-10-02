import LectureNotes.DominatedSufficiency
import LectureNotes.GaussianBayesRisk

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The joint density of a finite iid sample with respect to the product of
its dominating measures. -/
theorem iid_product_withDensity {Ω : Type*} [MeasurableSpace Ω]
    (ν P : Measure Ω) [SigmaFinite ν] [IsProbabilityMeasure P]
    (f : Ω → ℝ≥0∞) (hf : Measurable f) (hP : ν.withDensity f = P) (n : ℕ) :
    Measure.pi (fun _ : Fin n => P) =
      (Measure.pi (fun _ : Fin n => ν)).withDensity (fun x => ∏ i, f (x i)) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    change Measure.pi (fun _ : Fin 0 => P) =
      (Measure.pi (fun _ : Fin 0 => ν)).withDensity (1 : (Fin 0 → Ω) → ℝ≥0∞)
    rw [withDensity_one]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0
    have hsample := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) 0
    have hbase := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    have : IsProbabilityMeasure (ν.withDensity f) := by rw [hP]; infer_instance
    apply e.measurableEmbedding.map_injective
    rw [hsample.map_eq, map_withDensity_equiv _ e _ (by fun_prop), hbase.map_eq,
      ih, ← hP, prod_withDensity]
    · congr 1
      ext z
      simp [e, Fin.prod_univ_succ]
    all_goals fun_prop

/-- L5's exponential-family product-likelihood algebra, retaining the carrier
and normalization and permitting a carrier that vanishes. -/
theorem exponentialFamily_product_factorization {Ω : Type*} {n k : ℕ}
    (h : Ω → ℝ≥0∞) (t : Fin k → Ω → ℝ) (η : Fin k → ℝ) (A : ℝ)
    (x : Fin n → Ω) :
    (∏ i, h (x i) * ENNReal.ofReal (Real.exp ((∑ j, η j * t j (x i)) - A))) =
      (∏ i, h (x i)) *
        ENNReal.ofReal (Real.exp ((∑ j, η j * (∑ i, t j (x i))) - n * A)) := by
  rw [Finset.prod_mul_distrib, ← ENNReal.ofReal_prod_of_nonneg
    (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 3
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- L5 Theorem 3 on the actual product experiment: sums of the k canonical
statistics are sufficient for any measurable exponential family. The model
normalizations are verified by the given one-observation probability laws. -/
theorem exponentialFamily_sum_sufficient {Θ Ω : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    (ν : Measure Ω) [SigmaFinite ν] (P : Θ → Measure Ω)
    [∀ θ, IsProbabilityMeasure (P θ)] (θ₀ : Θ)
    {k : ℕ} (h : Ω → ℝ≥0∞) (hh : Measurable h)
    (t : Fin k → Ω → ℝ) (ht : ∀ j, Measurable (t j))
    (η : Θ → Fin k → ℝ) (A : Θ → ℝ)
    (hP : ∀ θ, ν.withDensity
      (fun x => h x * ENNReal.ofReal (Real.exp ((∑ j, η θ j * t j x) - A θ))) = P θ)
    (n : ℕ) :
    IsSufficientStatistic (fun θ => Measure.pi (fun _ : Fin n => P θ))
      (fun x : Fin n → Ω => fun j : Fin k => ∑ i, t j (x i)) := by
  let f (θ : Θ) (x : Ω) := h x * ENNReal.ofReal (Real.exp ((∑ j, η θ j * t j x) - A θ))
  have hf (θ : Θ) : Measurable (f θ) := by dsimp only [f]; fun_prop
  apply sufficient_of_density_factorization
    (P := fun θ => Measure.pi (fun _ : Fin n => P θ))
    (Measure.pi (fun _ : Fin n => ν)) θ₀ (fun θ x => ∏ i, f θ (x i))
    (by intro θ; fun_prop)
    (fun θ => (iid_product_withDensity ν (P θ) (f θ) (hf θ) (hP θ) n).symm)
    (by fun_prop)
    (fun θ s => ENNReal.ofReal (Real.exp
      ((∑ j, (η θ j - η θ₀ j) * s j) - n * (A θ - A θ₀))))
    (by intro θ; fun_prop)
  intro θ
  apply ae_of_all
  intro x
  dsimp only [f]
  rw [exponentialFamily_product_factorization, exponentialFamily_product_factorization,
    mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 3
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

end LectureNotes
