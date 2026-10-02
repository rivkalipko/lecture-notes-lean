import LectureNotes.BernoulliBinomialMoments
import Mathlib.Probability.Distributions.Binomial

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The finite count-space construction agrees with the binomial measure on
natural numbers used by Mathlib. -/
theorem binomialCountLaw_natCast (k : ℕ) (p : Icc (0 : ℝ) 1) :
    (binomialCountLaw k p).map (fun j : Fin (k + 1) => (j : ℕ)) = binomial k p := by
  have : IsProbabilityMeasure ((binomialCountLaw k p).map (fun j : Fin (k + 1) => (j : ℕ))) :=
    Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable)
  apply Measure.ext_of_measureReal_singleton
  intro j
  rw [map_measureReal_apply Measurable.of_discrete (measurableSet_singleton j),
    binomial_real_singleton]
  by_cases hj : j ≤ k
  · let i : Fin (k + 1) := ⟨j, by omega⟩
    have he : (fun j : Fin (k + 1) => (j : ℕ)) ⁻¹' {j} = {i} := by
      ext a
      simp only [mem_preimage, mem_singleton_iff]
      exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    rw [he, measureReal_def, binomialCountLaw_singleton,
      ENNReal.toReal_ofReal (binomialCountMass_nonneg k p i)]
    rfl
  · have he : (fun j : Fin (k + 1) => (j : ℕ)) ⁻¹' {j} = ∅ := by
      ext i
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro hi
      have := i.isLt
      omega
    simp [he, Nat.choose_eq_zero_of_lt (lt_of_not_ge hj)]

theorem binomialCountLaw_realCast (k : ℕ) (p : Icc (0 : ℝ) 1) :
    (binomialCountLaw k p).map (fun j : Fin (k + 1) => (j : ℝ)) =
      (binomial k p).map (fun j : ℕ => (j : ℝ)) := by
  rw [← binomialCountLaw_natCast k p, Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  rfl

theorem binomialCountLaw_one_real (p : Icc (0 : ℝ) 1) :
    (binomialCountLaw 1 p).map (fun j : Fin 2 => (j : ℝ)) = bernoulliRealLaw p := by
  rw [binomialCountLaw_realCast, binomial_one_eq_bernoulliMeasure, map_bernoulliMeasure]
  simp [bernoulliRealLaw]

/-- The actual sum of independent finite binomial counts has the binomial
law, with parameters multiplied by the number of observations. -/
theorem binomialSample_total_law (k n : ℕ) (p : Icc (0 : ℝ) 1) :
    (binomialSampleLaw k n p).map binomialSampleTotal = binomial (k * n) p := by
  have : IsProbabilityMeasure ((binomialSampleLaw k n p).map binomialSampleTotal) :=
    Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  apply Measure.ext_of_measureReal_singleton
  intro j
  rw [map_measureReal_apply Measurable.of_discrete (measurableSet_singleton j), binomial_real_singleton]
  exact binomialSample_total_mass k n j p

/-- L1: an IID sum of n real-valued Bernoulli(p) observations has the actual
Binomial(n,p) law, including p=0, p=1 and the empty sum. -/
theorem iid_bernoulli_sum_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (p : Icc (0 : ℝ) 1)
    (hX : ∀ i, HasLaw (X i) (bernoulliRealLaw p) P) (hind : iIndepFun X P) :
    HasLaw (fun ω => ∑ i, X i ω) ((binomial n p).map (fun j : ℕ => (j : ℝ))) P := by
  let C : (Fin n → Fin 2) → Fin n → ℝ := fun x i => (x i : ℝ)
  have hCm : Measurable C := Measurable.of_discrete
  have hpi : (binomialSampleLaw 1 n p).map C = Measure.pi (fun _ : Fin n => bernoulliRealLaw p) := by
    have (i : Fin n) : IsProbabilityMeasure ((binomialCountLaw 1 p).map (fun j : Fin 2 => (j : ℝ))) :=
      Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
    change (Measure.pi (fun _ : Fin n => binomialCountLaw 1 p)).map C = _
    dsimp only [C]
    exact (Measure.pi_map_pi (μ := fun _ : Fin n => binomialCountLaw 1 p)
      (f := fun _ : Fin n => fun j : Fin 2 => (j : ℝ))
      (fun _ => Measurable.of_discrete.aemeasurable)).trans (by
        congr 1
        funext i
        exact binomialCountLaw_one_real p)
  refine ⟨(Finset.measurable_sum _ (fun i _ => hXm i)).aemeasurable, ?_⟩
  have hj := (hind.hasLaw_pi hX).map_eq
  have hm : Measurable (fun x : Fin n → ℝ => ∑ i, x i) := by fun_prop
  calc
    P.map (fun ω => ∑ i, X i ω) =
        (P.map (fun ω i => X i ω)).map (fun x => ∑ i, x i) := by
      rw [Measure.map_map hm (measurable_pi_lambda _ hXm)]
      rfl
    _ = ((binomialSampleLaw 1 n p).map C).map (fun x => ∑ i, x i) := by rw [hj, hpi]
    _ = ((binomialSampleLaw 1 n p).map binomialSampleTotal).map (fun j : ℕ => (j : ℝ)) := by
      rw [Measure.map_map hm hCm,
        Measure.map_map Measurable.of_discrete Measurable.of_discrete]
      congr 1
      funext x
      simp [Function.comp_def, C, binomialSampleTotal, Nat.cast_sum]
    _ = _ := by rw [binomialSample_total_law, one_mul]

end LectureNotes
