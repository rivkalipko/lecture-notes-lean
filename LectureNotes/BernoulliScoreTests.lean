import LectureNotes.BernoulliOdds
import LectureNotes.BernoulliLikelihoodRatio
import LectureNotes.PoissonTests

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal

/-- The Bernoulli score statistic uses information at the tested probability. -/
def bernoulliLM (n m p : ℝ) : ℝ := n * (m - p) ^ 2 / (p * (1 - p))

/-- The derivative is taken from the actual count likelihood on the open model. -/
theorem bernoulliCountLikelihood_log_derivative (s f : ℕ) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q => log (bernoulliCountLikelihood s f q))
      ((s : ℝ) / p - (f : ℝ) / (1 - p)) p := by
  have hd := (((hasDerivAt_id p).log hp.1.ne').const_mul (s : ℝ)).add
    ((((hasDerivAt_const p 1).sub (hasDerivAt_id p)).log (sub_pos.mpr hp.2).ne').const_mul (f : ℝ))
  have hd' : HasDerivAt (fun q => (s : ℝ) * log q + (f : ℝ) * log (1 - q))
      ((s : ℝ) / p - (f : ℝ) / (1 - p)) p := by
    convert! hd using 1 <;> simp only [id_eq, Pi.sub_apply, zero_sub] <;> ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hp.1 hp.2] with q hq
  exact bernoulliCountLikelihood_log hq

/-- The displayed LM formula follows from actual log-likelihood differentiation
and the actual Bernoulli Fisher information. -/
theorem bernoulli_count_score_statistic {s f : ℕ} (hn : 0 < s + f)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    scalarScoreStatistic (deriv (fun q => log (bernoulliCountLikelihood s f q)) p)
      (((s : ℝ) + f) * bernoulliRegularDensity.information p) =
        bernoulliLM ((s : ℝ) + f) (bernoulliCountMLE s f) p := by
  rw [(bernoulliCountLikelihood_log_derivative s f hp).deriv, bernoulli_information hp]
  have hnR : (s : ℝ) + f ≠ 0 := by exact_mod_cast hn.ne'
  unfold scalarScoreStatistic bernoulliLM bernoulliCountMLE
  field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne']
  <;> ring

/-- The same identity for the ordered product of Bernoulli masses. -/
theorem bernoulli_product_score_statistic {n : ℕ} (hn : 0 < n)
    (x : Fin n → Fin 2) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    scalarScoreStatistic (deriv (fun q => log (∏ i, bernoulliMass q (x i))) p)
      ((n : ℝ) * bernoulliRegularDensity.information p) =
        bernoulliLM n (sampleMean (fun i => (x i : ℝ))) p := by
  have hc := bernoulli_counts_sum x
  have hn' : 0 < bernoulliSuccessCount x + bernoulliFailureCount x := by rwa [hc]
  have hm : bernoulliCountMLE (bernoulliSuccessCount x) (bernoulliFailureCount x) =
      sampleMean (fun i => (x i : ℝ)) := by
    rw [bernoulliCountMLE, ← Nat.cast_add, hc, bernoulliSuccessCount_eq_sum]
    simp only [Nat.cast_sum, sampleMean, Fintype.card_fin]
    ring
  have hh := bernoulli_count_score_statistic hn' hp
  rw [hm, ← Nat.cast_add, hc] at hh
  simpa only [bernoulli_product_likelihood] using hh

/-- Score inversion is an exact quadratic set, retaining both tails. -/
theorem bernoulliLM_quadratic (n s p c : ℝ) (hn : 0 < n)
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    bernoulliLM n (s / n) p ≤ c ↔
      (n ^ 2 + c * n) * p ^ 2 - (2 * n * s + c * n) * p + s ^ 2 ≤ 0 := by
  have hd : 0 < n * p * (1 - p) := mul_pos (mul_pos hn hp.1) (sub_pos.mpr hp.2)
  have he : bernoulliLM n (s / n) p = (s - n * p) ^ 2 / (n * p * (1 - p)) := by
    unfold bernoulliLM
    field_simp
  rw [he, div_le_iff₀ hd]
  constructor <;> intro h <;> nlinarith [h]

/-- The score confidence set is the inversion of the actual score statistic. -/
def bernoulliScoreConfidenceSet {n : ℕ} (x : Fin n → ℝ) (c : ℝ) : Set ℝ :=
  {p | p ∈ Ioo (0 : ℝ) 1 ∧ bernoulliLM n (sampleMean x) p ≤ c}

theorem bernoulliScoreConfidenceSet_quadratic {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (c : ℝ) :
    bernoulliScoreConfidenceSet x c =
      {p | p ∈ Ioo (0 : ℝ) 1 ∧
        ((n : ℝ) ^ 2 + c * n) * p ^ 2 -
          (2 * n * (∑ i, x i) + c * n) * p + (∑ i, x i) ^ 2 ≤ 0} := by
  ext p
  simp only [bernoulliScoreConfidenceSet, mem_setOf_eq]
  apply and_congr_right
  intro hp
  have hm : sampleMean x = (∑ i, x i) / n := by simp [sampleMean, div_eq_mul_inv, mul_comm]
  rw [hm]
  exact bernoulliLM_quadratic n _ p c (by exact_mod_cast hn) hp

section IID
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {p : Icc (0 : ℝ) 1}

/-- The actual IID Bernoulli score statistic has the chi-square-one limit.
Observed all-zero and all-one samples are retained; only the true null
probability must be interior. -/
theorem bernoulliLM_limit (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hX : ∀ i, HasLaw (X i) (bernoulliRealLaw p) P) (hind : iIndepFun X P) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => bernoulliLM ((n : ℝ) + 1) (bernoulliProportion X n ω) p)
      (fun z => z ^ 2) := by
  have hv : 0 < (p : ℝ) * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  have hh := (bernoulliProportion_clt hp hX hind).continuous_comp
    (g := fun z : ℝ => z ^ 2 / ((p : ℝ) * (1 - p))) (by fun_prop)
  apply TendstoInDistribution.congr _ _ hh
  · intro n
    apply ae_of_all
    intro ω
    simp only [bernoulliLM, Function.comp_apply, mul_pow,
      Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)]
  · apply ae_of_all
    intro z
    simp only [Function.comp_apply, mul_pow, Real.sq_sqrt hv.le]
    field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne']

/-- Exact asymptotic null rejection probability of the score test. -/
theorem bernoulliLM_null_size (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (bernoulliRealLaw p) P) (hind : iIndepFun X P)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => P.real {ω | distributionQuantile (chiSquared 1) (1 - α) <
      bernoulliLM ((n : ℝ) + 1) (bernoulliProportion X n ω) p}) atTop (𝓝 α) := by
  apply chiSquared_one_limit_rejection_size _ (bernoulliLM_limit hp hX hind) hα
  intro n
  exact ((((bernoulliProportion_measurable hXm n).sub_const _).pow_const 2).const_mul _).div_const _

/-- L11's score-set inversion has actual asymptotic coverage 1−α under the
IID Bernoulli model. The set includes the correct squared, two-sided condition. -/
theorem bernoulliScoreConfidenceSet_coverage (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hX : ∀ i, HasLaw (X i) (bernoulliRealLaw p) P) (hind : iIndepFun X P)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω | (p : ℝ) ∈ bernoulliScoreConfidenceSet
      (fun i : Fin (n + 1) => X i ω) (distributionQuantile (chiSquared 1) (1 - α))})
      atTop (𝓝 (1 - α)) := by
  have hq : 1 - α ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hh := chiSquared_weak_limit_coverage (by norm_num : 0 < (1 : ℕ))
    (bernoulliLM_limit hp hX hind)
    (standard_normal_square (show HasLaw id (gaussianReal 0 1) (gaussianReal 0 1) from HasLaw.id)) hq
  simpa only [bernoulliScoreConfidenceSet, mem_setOf_eq, hp, true_and,
    bernoulliProportion, Nat.cast_add, Nat.cast_one] using hh

end IID
end LectureNotes
