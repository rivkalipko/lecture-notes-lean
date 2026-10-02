import LectureNotes.Bootstrap
import LectureNotes.NormalVarianceRisk
import Mathlib.Probability.ProbabilityMassFunction.Integrals

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

variable {n : ℕ} [NeZero n]

/-- Integrating against the empirical distribution averages the transformed
observations, with repeated observations counted according to multiplicity. -/
theorem empiricalLaw_integral (x : Fin n → ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ y, f y ∂empiricalLaw x) = (∑ i, f (x i)) / n := by
  rw [empiricalLaw, integral_map (Measurable.of_discrete.aemeasurable)
    hf.aestronglyMeasurable, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, div_eq_mul_inv]
  rw [← Finset.mul_sum, mul_comm]

theorem empiricalLaw_memLp (x : Fin n → ℝ) (p : ℝ≥0∞) :
    MemLp id p (empiricalLaw x) := by
  rw [empiricalLaw]
  apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (Measurable.of_discrete.aemeasurable)).mpr
  exact ⟨Measurable.of_discrete.aestronglyMeasurable, eLpNorm_lt_top_of_finite⟩

theorem empiricalLaw_mean (x : Fin n → ℝ) :
    (∫ y, y ∂empiricalLaw x) = sampleMean x := by
  have h := empiricalLaw_integral x measurable_id
  simp only [id_eq] at h
  rw [h]
  simp [sampleMean, div_eq_mul_inv, mul_comm]

theorem empiricalLaw_variance (x : Fin n → ℝ) :
    Var[id; empiricalLaw x] = empiricalVariance x := by
  rw [variance_eq_integral measurable_id.aemeasurable]
  simp only [id_eq]
  rw [empiricalLaw_mean]
  exact empiricalLaw_integral x (by fun_prop)

theorem bootstrapLaw_isProbabilityMeasure (x : Fin n → ℝ) :
    IsProbabilityMeasure (bootstrapLaw x) := by unfold bootstrapLaw; infer_instance

/-- Conditional on the original sample, the bootstrap mean is centered at the
observed mean. The probability measure is the actual IID resampling law. -/
theorem bootstrap_sampleMean_expectation (x : Fin n → ℝ) :
    (∫ b, sampleMean b ∂bootstrapLaw x) = sampleMean x := by
  letI := bootstrapLaw_isProbabilityMeasure x
  have hLaw i : HasLaw (fun b : Fin n → ℝ => b i) (empiricalLaw x) (bootstrapLaw x) :=
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval
      (fun _ : Fin n => empiricalLaw x) i).map_eq⟩
  exact sampleMean_expectation (Nat.pos_of_ne_zero (NeZero.ne n))
    (fun i => (((hLaw i).identDistrib HasLaw.id).memLp_iff.mpr (empiricalLaw_memLp x 2)).integrable (by norm_num))
    (fun i => by rw [(hLaw i).integral_eq, empiricalLaw_mean])

/-- The conditional bootstrap variance of the sample mean is the empirical
variance divided by sample size; its denominator inside the empirical variance
is n, not n-1. -/
theorem bootstrap_sampleMean_variance (x : Fin n → ℝ) :
    Var[sampleMean; bootstrapLaw x] = empiricalVariance x / n := by
  letI := bootstrapLaw_isProbabilityMeasure x
  have hLaw i : HasLaw (fun b : Fin n → ℝ => b i) (empiricalLaw x) (bootstrapLaw x) :=
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval
      (fun _ : Fin n => empiricalLaw x) i).map_eq⟩
  apply sampleMean_variance (Nat.pos_of_ne_zero (NeZero.ne n))
    (fun i => ((hLaw i).identDistrib HasLaw.id).memLp_iff.mpr (empiricalLaw_memLp x 2))
    (fun _ _ hij => (iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)).indepFun hij)
  intro i
  rw [(hLaw i).variance_eq, empiricalLaw_variance]

/-- The empirical central second moment is the second raw sample moment
minus the square of the sample mean. -/
theorem empiricalVariance_eq_secondMoment_sub_sq {k : ℕ} (x : Fin k → ℝ) :
    empiricalVariance x = sampleMean (fun i => x i ^ 2) - sampleMean x ^ 2 := by
  by_cases hk : k = 0
  · subst k
    simp [empiricalVariance, sampleMean]
  letI : NeZero k := ⟨hk⟩
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [empiricalVariance, sum_centered_sq_sampleMean]
  simp only [sampleMean, Fintype.card_fin]
  field_simp [hk']

/-- Finite second moments suffice for strong consistency of the empirical
variance; fourth moments are not needed. -/
theorem empiricalVariance_strong_consistency {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ConvergesAlmostSurely P (fun k ω => empiricalVariance (fun i : Fin k => X i ω))
      (fun _ => Var[X 0; P]) := by
  have hmean := strong_law_of_large_numbers (hX.integrable (by norm_num)) (fun _ _ hij => hind.indepFun hij) hident
  have hsq := strong_law_of_large_numbers hX.integrable_sq
    (fun _ _ hij => (hind.comp (fun _ x => x ^ 2) (fun _ => by fun_prop)).indepFun hij)
    (fun i => (hident i).comp (by fun_prop : Measurable (fun x : ℝ => x ^ 2)))
  filter_upwards [hmean, hsq] with ω hm hs
  have hh := hs.sub (hm.pow 2)
  simp only [Function.comp_def] at hh
  rw [← variance_eq_second_moment_sub_mean_sq P hX] at hh
  convert! hh using 1
  funext k
  rw [empiricalVariance_eq_secondMoment_sub_sq]
  simp only [sampleMean, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => X i ω ^ 2) k,
    Fin.sum_univ_eq_sum_range (fun i => X i ω) k]
  ring

theorem empiricalVariance_consistency {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ConvergesInProbability P (fun k ω => empiricalVariance (fun i : Fin k => X i ω))
      (fun _ => Var[X 0; P]) := by
  apply almost_sure_implies_probability _
    (empiricalVariance_strong_consistency hXm hX hind hident)
  intro k
  have hm : Measurable (fun ω => sampleMean (fun i : Fin k => X i ω)) := by
    unfold sampleMean
    fun_prop
  have hs : Measurable (fun ω => sampleMean (fun i : Fin k => X i ω ^ 2)) := by
    unfold sampleMean
    fun_prop
  simpa only [empiricalVariance_eq_secondMoment_sub_sq, Pi.sub_apply] using! (hs.sub (hm.pow_const 2)).aemeasurable

/-- The bootstrap estimate of the asymptotic variance of the mean is strongly
consistent. Samples use k+1 observations so every empirical law is defined. -/
theorem bootstrap_mean_asymptotic_variance_consistent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ConvergesAlmostSurely P
      (fun k ω => (k + 1 : ℕ) * Var[sampleMean;
        bootstrapLaw (fun i : Fin (k + 1) => X i ω)])
      (fun _ => Var[X 0; P]) := by
  filter_upwards [empiricalVariance_strong_consistency hXm hX hind hident] with ω hω
  convert! hω.comp (tendsto_add_atTop_nat 1) using 1
  funext k
  simp only [Function.comp_apply]
  rw [bootstrap_sampleMean_variance]
  field_simp

end LectureNotes
