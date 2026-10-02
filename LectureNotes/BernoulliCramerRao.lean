import LectureNotes.BernoulliSampleInformation

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

/-- In a finite Bernoulli sample, differentiation of an arbitrary estimator's
expectation is justified by a finite sum of derivatives of actual masses. -/
theorem bernoulli_sample_score_identity {n : ℕ} (T : (Fin n → Fin 2) → ℝ)
    {p : Icc (0 : ℝ) 1} (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q : ℝ => ∑ x, T x * (∏ i, bernoulliMass q (x i)))
      (∫ x, T x * bernoulliSampleScore x p ∂binomialSampleLaw 1 n p) p := by
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun (x : Fin n → Fin 2) _ => (bernoulli_product_mass_derivative x hp).const_mul (T x))
  convert! hd using 1
  · funext q
    simp
  · rw [bernoulli_sample_integral]
    apply Finset.sum_congr rfl
    intro x _
    ring

/-- L6 Example 8: every estimator unbiased throughout the Bernoulli family
has variance at least p(1−p)/n at each interior parameter. No differentiation
or score-moment identity is assumed. -/
theorem bernoulli_sample_cramerRao {n : ℕ} (hn : 0 < n)
    (T : (Fin n → Fin 2) → ℝ)
    (hT : ∀ q : Icc (0 : ℝ) 1, (q : ℝ) ∈ Ioo (0 : ℝ) 1 →
      Unbiased (binomialSampleLaw 1 n q) T q)
    {p : Icc (0 : ℝ) 1} (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1) :
    (p : ℝ) * (1 - p) / n ≤ Var[T; binomialSampleLaw 1 n p] := by
  have he : (fun q : ℝ => q) =ᶠ[𝓝 (p : ℝ)]
      (fun q : ℝ => ∑ x, T x * (∏ i, bernoulliMass q (x i))) := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with q hq
    have hu := (hT ⟨q, hq.1.le, hq.2.le⟩ hq).2
    rw [bernoulli_sample_integral] at hu
    exact hu.symm
  have hd := (bernoulli_sample_score_identity T hp).congr_of_eventuallyEq he
  have hI : 0 < FisherInformation (binomialSampleLaw 1 n p) (fun x => bernoulliSampleScore x p) := by
    rw [bernoulliSampleScore_information hn hp]
    exact div_pos (by exact_mod_cast hn) (mul_pos hp.1 (sub_pos.mpr hp.2))
  have hh := cramer_rao_unbiased_from_score_identity (binomialSampleLaw 1 n p)
    (MemLp.of_discrete : MemLp T 2 _) (MemLp.of_discrete : MemLp (fun x => bernoulliSampleScore x p) 2 _)
    (bernoulliSampleScore_mean hn p) hI hd
  rw [bernoulliSampleScore_information hn hp, one_div_div] at hh
  exact hh

/-- The sample mean attains the Cramér–Rao value and is unbiased in the full
closed Bernoulli family, including the degenerate endpoints. -/
theorem bernoulli_sampleMean_attains_bound {n : ℕ} (hn : 0 < n) (p : Icc (0 : ℝ) 1) :
    Unbiased (binomialSampleLaw 1 n p) (fun x => sampleMean (fun i => (x i : ℝ))) p ∧
      Var[fun x => sampleMean (fun i => (x i : ℝ)); binomialSampleLaw 1 n p] =
        (p : ℝ) * (1 - p) / n := by
  exact ⟨⟨Integrable.of_finite, (bernoulli_sampleMean_moments hn p).1⟩,
    (bernoulli_sampleMean_moments hn p).2⟩

/-- The actual sample mean is uniformly minimum-variance unbiased: one
parameter-free estimator is unbiased everywhere and dominates in variance
every other estimator that is unbiased everywhere. Endpoints are included. -/
theorem bernoulli_sampleMean_UMVU {n : ℕ} (hn : 0 < n) :
    (∀ p : Icc (0 : ℝ) 1, Unbiased (binomialSampleLaw 1 n p)
      (fun x => sampleMean (fun i => (x i : ℝ))) p) ∧
    ∀ T : (Fin n → Fin 2) → ℝ,
      (∀ p : Icc (0 : ℝ) 1, Unbiased (binomialSampleLaw 1 n p) T p) →
      ∀ p : Icc (0 : ℝ) 1,
        Var[fun x => sampleMean (fun i => (x i : ℝ)); binomialSampleLaw 1 n p] ≤
          Var[T; binomialSampleLaw 1 n p] := by
  refine ⟨fun p => (bernoulli_sampleMean_attains_bound hn p).1, ?_⟩
  intro T hT p
  rw [(bernoulli_sampleMean_moments hn p).2]
  by_cases hp0 : (p : ℝ) = 0
  · simp only [hp0, zero_mul, zero_div]
    exact variance_nonneg _ _
  by_cases hp1 : (p : ℝ) = 1
  · simp only [hp1, sub_self, mul_zero, zero_div]
    exact variance_nonneg _ _
  exact bernoulli_sample_cramerRao hn T (fun q _ => hT q)
    ⟨lt_of_le_of_ne p.property.1 (Ne.symm hp0), lt_of_le_of_ne p.property.2 hp1⟩

end LectureNotes
