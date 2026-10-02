import LectureNotes.BernoulliScoreTests
import LectureNotes.BinomialSum

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

/-- The full-sample Bernoulli score on its actual finite observation space. -/
def bernoulliSampleScore {n : ℕ} (x : Fin n → Fin 2) (p : ℝ) : ℝ :=
  ((∑ i, (x i : ℝ)) - n * p) / (p * (1 - p))

theorem binomial_one_mass_eq_bernoulliMass (p : Icc (0 : ℝ) 1) (x : Fin 2) :
    binomialCountMass 1 p x = bernoulliMass p x := by
  fin_cases x <;> simp [binomialCountMass, bernoulliMass]

/-- Integration in the genuine IID sample experiment is a finite weighted sum. -/
theorem bernoulli_sample_integral {n : ℕ} (p : Icc (0 : ℝ) 1)
    (T : (Fin n → Fin 2) → ℝ) :
    (∫ x, T x ∂binomialSampleLaw 1 n p) =
      ∑ x, T x * (∏ i, bernoulliMass p (x i)) := by
  have hmass0 (j : Fin 2) : 0 ≤ bernoulliMass p j := by
    rw [← binomial_one_mass_eq_bernoulliMass p j]
    exact binomialCountMass_nonneg 1 p j
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro x _
  simp only [measureReal_def, binomialSampleLaw, Measure.pi_singleton, binomialCountLaw_singleton,
    ENNReal.toReal_prod, ENNReal.toReal_ofReal (binomialCountMass_nonneg 1 p _),
    binomial_one_mass_eq_bernoulliMass, ENNReal.toReal_ofReal (hmass0 _), smul_eq_mul, mul_comm]

/-- Actual independent sample coordinates, transported to the real Bernoulli law. -/
theorem bernoulli_sample_coordinate_law {n : ℕ} (p : Icc (0 : ℝ) 1) (i : Fin n) :
    HasLaw (fun x : Fin n → Fin 2 => (x i : ℝ)) (bernoulliRealLaw p)
      (binomialSampleLaw 1 n p) := by
  have he : HasLaw (fun x : Fin n → Fin 2 => x i) (binomialCountLaw 1 p)
      (binomialSampleLaw 1 n p) :=
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval
      (fun _ : Fin n => binomialCountLaw 1 p) i).map_eq⟩
  exact (show HasLaw (fun j : Fin 2 => (j : ℝ)) (bernoulliRealLaw p) (binomialCountLaw 1 p) from
    ⟨Measurable.of_discrete.aemeasurable, binomialCountLaw_one_real p⟩).comp he

theorem bernoulli_sampleMean_moments {n : ℕ} (hn : 0 < n) (p : Icc (0 : ℝ) 1) :
    (∫ x, sampleMean (fun i => (x i : ℝ)) ∂binomialSampleLaw 1 n p) = p ∧
      Var[fun x => sampleMean (fun i => (x i : ℝ)); binomialSampleLaw 1 n p] =
        (p : ℝ) * (1 - p) / n := by
  have hL := bernoulli_sample_coordinate_law (n := n) p
  have h₂ i := ((hL i).identDistrib HasLaw.id).memLp_iff.mpr (bernoulliRealLaw_memLp_two p)
  constructor
  · exact sampleMean_expectation hn (fun i => (h₂ i).integrable (by norm_num))
      (fun i => (hL i).integral_eq.trans (bernoulliRealLaw_mean p))
  · apply sampleMean_variance hn h₂
    · intro i j hij
      exact (iIndepFun_pi (fun _ : Fin n =>
        (Measurable.of_discrete : Measurable (fun j : Fin 2 => (j : ℝ))).aemeasurable)).indepFun hij
    · intro i
      exact (hL i).variance_eq.trans (bernoulliRealLaw_variance p)

theorem bernoulliSampleScore_eq_centeredMean {n : ℕ} (hn : 0 < n)
    (x : Fin n → Fin 2) (p : ℝ) :
    bernoulliSampleScore x p = ((n : ℝ) / (p * (1 - p))) *
      (sampleMean (fun i => (x i : ℝ)) - p) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold bernoulliSampleScore sampleMean
  simp only [Fintype.card_fin]
  field_simp

/-- The score mean is zero for the actual product law. -/
theorem bernoulliSampleScore_mean {n : ℕ} (hn : 0 < n) (p : Icc (0 : ℝ) 1) :
    (∫ x, bernoulliSampleScore x p ∂binomialSampleLaw 1 n p) = 0 := by
  simp_rw [bernoulliSampleScore_eq_centeredMean hn]
  rw [integral_const_mul, integral_sub Integrable.of_finite (integrable_const _),
    (bernoulli_sampleMean_moments hn p).1]
  simp

/-- L6 Example 8: the true sample squared-score expectation is n/[p(1−p)]. -/
theorem bernoulliSampleScore_information {n : ℕ} (hn : 0 < n)
    {p : Icc (0 : ℝ) 1} (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1) :
    FisherInformation (binomialSampleLaw 1 n p) (fun x => bernoulliSampleScore x p) =
      (n : ℝ) / ((p : ℝ) * (1 - p)) := by
  unfold FisherInformation
  rw [← variance_of_integral_eq_zero Measurable.of_discrete.aemeasurable
    (bernoulliSampleScore_mean hn p)]
  simp_rw [bernoulliSampleScore_eq_centeredMean hn]
  rw [variance_const_mul, variance_sub_const Measurable.of_discrete.aestronglyMeasurable,
    (bernoulli_sampleMean_moments hn p).2]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne']

/-- The derivative of the genuine product mass is density times score. -/
theorem bernoulli_product_mass_derivative {n : ℕ} (x : Fin n → Fin 2)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q => ∏ i, bernoulliMass q (x i))
      ((∏ i, bernoulliMass p (x i)) * bernoulliSampleScore x p) p := by
  have hs : (bernoulliSuccessCount x : ℝ) = ∑ i, (x i : ℝ) := by
    rw [bernoulliSuccessCount_eq_sum]
    push_cast
    rfl
  have hsum : (bernoulliSuccessCount x : ℝ) + bernoulliFailureCount x = n := by
    exact_mod_cast bernoulli_counts_sum x
  have hscore : (bernoulliSuccessCount x : ℝ) / p -
      (bernoulliFailureCount x : ℝ) / (1 - p) = bernoulliSampleScore x p := by
    unfold bernoulliSampleScore
    rw [← hs]
    field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne']
    nlinarith [congrArg (fun r : ℝ => p * r) hsum]
  have hd := (bernoulliCountLikelihood_log_derivative
    (bernoulliSuccessCount x) (bernoulliFailureCount x) hp).exp
  rw [Real.exp_log (bernoulliCountLikelihood_pos hp), hscore, ← bernoulli_product_likelihood] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hp.1 hp.2] with q hq
  rw [Real.exp_log (bernoulliCountLikelihood_pos hq), bernoulli_product_likelihood]

end LectureNotes
