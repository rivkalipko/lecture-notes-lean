import LectureNotes.PoissonLikelihood
import LectureNotes.Information

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

/-- The Poisson score for one count, at a positive rate. -/
def poissonScore (x : ℕ) (r : ℝ) : ℝ := (x : ℝ) / r - 1

/-- The score is the derivative of the actual log mass, with the parameter
extended using toNNReal only to obtain an ambient real differentiable function. -/
theorem poisson_actual_log_mass_derivative (x : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => Real.log ((poissonMeasure t.toNNReal).real {x}))
      (poissonScore x r) r := by
  have hd := poissonSampleLogLikelihood_derivative (fun _ : Fin 1 => x) hr
  simp only [Fin.sum_univ_one, Nat.cast_one, poissonScore] at hd ⊢
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hr] with t ht
  have hh := poissonSampleLikelihood_log (fun _ : Fin 1 => x) (Real.toNNReal_pos.mpr ht)
  simpa [poissonSampleLikelihood, Real.coe_toNNReal _ ht.le] using hh

theorem poissonScore_memLp_two {r : ℝ≥0} :
    MemLp (fun x => poissonScore x r) 2 (poissonMeasure r) := by
  simpa only [poissonScore, div_eq_mul_inv, Pi.sub_apply] using!
    ((poisson_memLp_two r).mul_const ((r : ℝ)⁻¹)).sub (memLp_const 1)

theorem poissonScore_mean {r : ℝ≥0} (hr : 0 < r) :
    (∫ x, poissonScore x r ∂poissonMeasure r) = 0 := by
  unfold poissonScore
  rw [integral_sub (((poisson_memLp_two r).integrable (by norm_num)).div_const _)
    (integrable_const _), integral_div, poisson_mean]
  simp [hr.ne']

/-- The actual score variance and Fisher information equal 1/r. -/
theorem poissonScore_variance {r : ℝ≥0} (hr : 0 < r) :
    Var[fun x => poissonScore x r; poissonMeasure r] = 1 / (r : ℝ) := by
  unfold poissonScore
  rw [variance_sub_const (by fun_prop)]
  simp only [div_eq_mul_inv]
  rw [variance_mul_const, poisson_variance]
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem poisson_fisherInformation {r : ℝ≥0} (hr : 0 < r) :
    FisherInformation (poissonMeasure r) (fun x => poissonScore x r) = 1 / (r : ℝ) := by
  rw [← poissonScore_variance hr]
  exact (variance_of_integral_eq_zero poissonScore_memLp_two.aemeasurable (poissonScore_mean hr)).symm

/-- Expected negative log-likelihood curvature yields the same information. -/
theorem poisson_expected_negative_curvature {r : ℝ≥0} (hr : 0 < r) :
    -(∫ x : ℕ, -(x : ℝ) / (r : ℝ) ^ 2 ∂poissonMeasure r) = 1 / (r : ℝ) := by
  rw [integral_div, integral_neg, poisson_mean]
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem poissonSampleExperiment_eval_hasLaw (n : ℕ) (r : ℝ≥0) (i : Fin n) :
    HasLaw (fun x : Fin n → ℕ => x i) (poissonMeasure r) (poissonSampleExperiment n r) :=
  ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _ : Fin n => poissonMeasure r) i).map_eq⟩

/-- Independent Poisson observations have total information n/r. -/
theorem poisson_sample_fisherInformation (n : ℕ) {r : ℝ≥0} (hr : 0 < r) :
    FisherInformation (poissonSampleExperiment n r)
      (fun x => (∑ i, (x i : ℝ)) / r - n) = n / (r : ℝ) := by
  let S (i : Fin n) (x : Fin n → ℕ) := poissonScore (x i) r
  have hm : Measurable (fun x : ℕ => poissonScore x r) := by fun_prop
  have hl i : HasLaw (S i) ((poissonMeasure r).map (fun x => poissonScore x r))
      (poissonSampleExperiment n r) :=
    (HasLaw.mk hm.aemeasurable rfl).comp (poissonSampleExperiment_eval_hasLaw n r i)
  have hd i : IdentDistrib (S i) (fun x => poissonScore x r)
      (poissonSampleExperiment n r) (poissonMeasure r) := by
    exact ⟨(hl i).aemeasurable, hm.aemeasurable, (hl i).map_eq⟩
  have hS i : MemLp (S i) 2 (poissonSampleExperiment n r) :=
    (hd i).memLp_iff.mpr poissonScore_memLp_two
  have hi : iIndepFun S (poissonSampleExperiment n r) :=
    iIndepFun_pi (fun _ => hm.aemeasurable)
  have he : (fun x : Fin n → ℕ => (∑ i, (x i : ℝ)) / r - n) =
      fun x => ∑ i, S i x := by
    funext x
    simp only [S, poissonScore, Finset.sum_sub_distrib, ← Finset.sum_div,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [he, fisherInformation_sum _ hS
    (fun i => (hd i).integral_eq.trans (poissonScore_mean hr)) (fun _ _ hij => hi.indepFun hij)]
  have hI i : FisherInformation (poissonSampleExperiment n r) (S i) = 1 / (r : ℝ) := by
    rw [FisherInformation, (hd i).sq.integral_eq]
    exact poisson_fisherInformation hr
  simp [hI, div_eq_mul_inv]

end LectureNotes
