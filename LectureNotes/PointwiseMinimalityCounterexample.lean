import LectureNotes.MinimalSufficiency
import Mathlib.Probability.Distributions.Gaussian.Real

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- Two everywhere-positive density versions differing only at one null point. -/
def nullPointDensity (θ : Bool) (x : ℝ) : ℝ :=
  (if θ = true ∧ x = 0 then 2 else 1) * gaussianPDFReal 0 1 x

def nullPointStatistic (x : ℝ) : ℝ := if x = 0 then 1 else 0

theorem nullPointDensity_measurable (θ : Bool) : Measurable (nullPointDensity θ) := by
  unfold nullPointDensity
  apply Measurable.mul _ (by fun_prop)
  exact Measurable.ite
    ((MeasurableSet.const _).inter (measurableSet_eq_fun measurable_id measurable_const))
    measurable_const measurable_const

theorem nullPointDensity_pos (θ : Bool) (x : ℝ) : 0 < nullPointDensity θ x := by
  have hg := gaussianPDFReal_pos 0 1 x (by norm_num)
  unfold nullPointDensity
  split_ifs <;> positivity

/-- The two pointwise-different density versions represent exactly the same
standard Gaussian probability law. -/
theorem nullPointDensity_law (θ : Bool) :
    volume.withDensity (fun x => ENNReal.ofReal (nullPointDensity θ x)) = gaussianReal 0 1 := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num)]
  apply withDensity_congr_ae
  have ha : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simpa using (measure_singleton (0 : ℝ) (μ := volume))
  filter_upwards [ha] with x hx
  simp [nullPointDensity, hx, gaussianPDF_def]

/-- These density versions satisfy the lecture's literal pointwise
likelihood-ratio criterion for the statistic indicating the singleton {0}. -/
theorem nullPointDensity_ratio_criterion (x y : ℝ) :
    (∀ θ : Bool, nullPointDensity θ x / nullPointDensity θ y =
      nullPointDensity false x / nullPointDensity false y) ↔
        nullPointStatistic x = nullPointStatistic y := by
  have he : (∀ θ : Bool, nullPointDensity θ x / nullPointDensity θ y =
      nullPointDensity false x / nullPointDensity false y) ↔
      nullPointDensity true x / nullPointDensity true y =
        nullPointDensity false x / nullPointDensity false y := by
    constructor
    · intro h; exact h true
    · intro h θ; cases θ <;> simp only [h]
  rw [he]
  have hxg := gaussianPDFReal_pos 0 1 x (by norm_num)
  have hyg := gaussianPDFReal_pos 0 1 y (by norm_num)
  by_cases hx : x = 0 <;> by_cases hy : y = 0
  · subst x; subst y
    simp only [div_self (nullPointDensity_pos true 0).ne',
      div_self (nullPointDensity_pos false 0).ne']
  · subst x
    simp only [nullPointDensity, Bool.false_eq_true, and_self, hy,
      and_true, and_false, if_true, if_false, one_mul, nullPointStatistic]
    constructor
    · intro h
      field_simp [hyg.ne'] at h
      nlinarith
    · norm_num
  · subst y
    simp only [nullPointDensity, Bool.false_eq_true, and_self, hx,
      and_true, and_false, if_true, if_false, one_mul, nullPointStatistic]
    constructor
    · intro h
      field_simp [hyg.ne'] at h
      nlinarith
    · norm_num
  · simp [nullPointDensity, hx, hy, nullPointStatistic]

theorem nullPointStatistic_measurable : Measurable nullPointStatistic := by
  unfold nullPointStatistic
  exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
    measurable_const measurable_const

/-- Any measurable statistic is sufficient in an experiment in which every
parameter gives the same law: one actual conditional distribution works for all. -/
theorem constant_experiment_sufficient {Θ S : Type*} [MeasurableSpace S]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ → S} (hT : Measurable T) :
    IsSufficientStatistic (fun _ : Θ => μ) T := by
  refine ⟨hT, condDistrib id T μ, inferInstance, ?_⟩
  intro θ
  exact ae_of_all _ (fun _ => rfl)

/-- A constant sufficient statistic cannot recover the singleton indicator
pointwise, even though it recovers it almost surely. This is why minimality
in the project is formulated modulo the model's null sets. -/
theorem nullPointStatistic_not_pointwise_recoverable :
    ¬ ∃ r : Unit → ℝ, ∀ x : ℝ, r () = nullPointStatistic x := by
  rintro ⟨r, hr⟩
  have h0 := hr 0
  have h1 := hr 1
  norm_num [nullPointStatistic] at h0 h1
  linarith

theorem pointwise_minimality_criterion_counterexample :
    (∀ θ : Bool, volume.withDensity (fun x => ENNReal.ofReal (nullPointDensity θ x)) = gaussianReal 0 1) ∧
    (∀ x y, (∀ θ : Bool, nullPointDensity θ x / nullPointDensity θ y =
      nullPointDensity false x / nullPointDensity false y) ↔ nullPointStatistic x = nullPointStatistic y) ∧
    IsSufficientStatistic (fun _ : Bool => gaussianReal 0 1) nullPointStatistic ∧
    IsSufficientStatistic (fun _ : Bool => gaussianReal 0 1) (fun _ : ℝ => ()) ∧
    (¬ ∃ r : Unit → ℝ, ∀ x : ℝ, r () = nullPointStatistic x) :=
  ⟨nullPointDensity_law, nullPointDensity_ratio_criterion,
    constant_experiment_sufficient _ nullPointStatistic_measurable,
    constant_experiment_sufficient _ measurable_const, nullPointStatistic_not_pointwise_recoverable⟩

end LectureNotes
