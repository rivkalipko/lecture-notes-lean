import LectureNotes.RegularCramerRao

/-! L5 p10 and L6 Example 7: a concrete model checking the exponential-family,
score, and dominated-density definitions against Bernoulli probabilities. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- The Bernoulli PMF on the sample space `{0, 1}`. Parameters in `(0, 1)`
give the positive common support used by the regularity results. -/
def bernoulliMass (p : ℝ) (x : Fin 2) : ℝ := if x = 0 then 1 - p else p

/-- This explicitly inhabits the regular-density structure; its derivative
bounds hold on the entire open interval `(0, 1)`. -/
def bernoulliRegularDensity : RegularDensity (Measure.count : Measure (Fin 2)) where
  domain := Ioo 0 1
  isOpen_domain := isOpen_Ioo
  density := bernoulliMass
  first := fun _ x => if x = 0 then -1 else 1
  second := fun _ _ => 0
  boundFirst := fun _ => 1
  boundSecond := fun _ => 0
  density_measurable := fun _ _ => Measurable.of_discrete.aestronglyMeasurable
  first_measurable := fun _ _ => Measurable.of_discrete.aestronglyMeasurable
  second_measurable := fun _ _ => measurable_const.aestronglyMeasurable
  density_integrable := fun _ _ => Integrable.of_finite
  positive := fun p hp => ae_of_all _ (fun x => by
    fin_cases x <;> simp [bernoulliMass, hp.1, sub_pos.mpr hp.2])
  normalized := fun p _ => by simp [integral_count, Fin.sum_univ_two, bernoulliMass]
  first_derivative := ae_of_all _ (fun x p _ => by
    fin_cases x
    · simpa [bernoulliMass, Pi.sub_def] using! (hasDerivAt_const p 1).sub (hasDerivAt_id p)
    · simpa [bernoulliMass] using! hasDerivAt_id p)
  second_derivative := ae_of_all _ (fun x p _ => hasDerivAt_const p _)
  first_bound := ae_of_all _ (fun x _ _ => by fin_cases x <;> norm_num)
  second_bound := ae_of_all _ (fun _ _ _ => by simp)
  integrable_first_bound := Integrable.of_finite
  integrable_second_bound := Integrable.of_finite

/-- L5's exponential-family representation, including normalization. -/
theorem bernoulli_exponentialFamily :
    ExponentialFamily Measure.count
      (fun x (p : Ioo (0 : ℝ) 1) => bernoulliMass p x) 1 where
  integrable := fun _ => Integrable.of_finite
  nonneg := fun x p => by
    fin_cases x <;> simp [bernoulliMass, p.property.1.le, sub_nonneg.mpr p.property.2.le]
  normalized := fun p => by simp [integral_count, Fin.sum_univ_two, bernoulliMass]
  representation := by
    refine ⟨fun _ => 1, fun p => 1 - p.val,
      fun _ p => Real.log (p.val / (1 - p.val)), fun _ x => (x.val : ℝ),
      measurable_const, fun _ => Measurable.of_discrete,
      fun _ => by norm_num, fun p => sub_pos.mpr p.property.2, ?_⟩
    intro x p
    fin_cases x
    · simp [bernoulliMass]
    · simp only [bernoulliMass]
      norm_num
      rw [Real.exp_log (div_pos p.property.1 (sub_pos.mpr p.property.2))]
      field_simp [(sub_pos.mpr p.property.2).ne']

/-- Differentiation is in the parameter, with the observation held fixed. -/
theorem bernoulli_score {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (x : Fin 2) :
    Score (LogLikelihood (fun x p => bernoulliMass p x)) x p 1 =
      if x = 0 then -1 / (1 - p) else 1 / p := by
  change deriv (fun p => Real.log (bernoulliMass p x)) p = _
  fin_cases x
  · simpa [bernoulliMass] using
      (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).log (sub_pos.mpr hp.2).ne').deriv
  · simpa [bernoulliMass] using ((hasDerivAt_id p).log hp.1.ne').deriv

/-- L6 Example 7's information is calculated from the actual density. -/
theorem bernoulli_information {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    bernoulliRegularDensity.information p = 1 / (p * (1 - p)) := by
  simp only [RegularDensity.information, RegularDensity.score, bernoulliRegularDensity,
    integral_count, Fin.sum_univ_two, bernoulliMass]
  norm_num
  field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne']
  <;> ring

/-- The weighted density calculation is also Fisher information under the
induced probability measure, not an unrelated algebraic expression. -/
theorem bernoulli_model_fisherInformation {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    FisherInformation (bernoulliRegularDensity.model p) (bernoulliRegularDensity.score p) =
      1 / (p * (1 - p)) := by
  rw [bernoulliRegularDensity.model_fisherInformation hp, bernoulli_information hp]

theorem bernoulli_observation_unbiased {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    Unbiased (bernoulliRegularDensity.model p) (fun x : Fin 2 => (x.val : ℝ)) p := by
  let : IsProbabilityMeasure (bernoulliRegularDensity.model p) :=
    bernoulliRegularDensity.model_isProbabilityMeasure hp
  refine ⟨Integrable.of_finite, ?_⟩
  rw [bernoulliRegularDensity.integral_model hp]
  simp [bernoulliRegularDensity, bernoulliMass, integral_count, Fin.sum_univ_two]

/-- Applying the general unbiased bound to an explicit nonconstant estimator
checks that its regularity and unbiasedness hypotheses can hold together. -/
theorem bernoulli_cramerRao {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    p * (1 - p) ≤ Var[fun x : Fin 2 => (x.val : ℝ); bernoulliRegularDensity.model p] := by
  let : IsProbabilityMeasure (bernoulliRegularDensity.model p) :=
    bernoulliRegularDensity.model_isProbabilityMeasure hp
  have hI : 0 < bernoulliRegularDensity.information p := by
    rw [bernoulli_information hp]
    exact one_div_pos.mpr (mul_pos hp.1 (sub_pos.mpr hp.2))
  have h := bernoulliRegularDensity.cramer_rao_unbiased hp (fun x : Fin 2 => (x.val : ℝ))
    Measurable.of_discrete.aestronglyMeasurable Integrable.of_finite Integrable.of_finite
    MemLp.of_discrete MemLp.of_discrete hI (fun _ ht => bernoulli_observation_unbiased ht)
  simpa only [bernoulli_information hp, one_div_one_div] using h

end LectureNotes
