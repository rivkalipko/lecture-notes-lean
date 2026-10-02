import LectureNotes.BootstrapMoments

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {n : ℕ} [NeZero n]

/-- Applying a measurable statistic commutes with the empirical law. -/
theorem empiricalLaw_map_statistic (x : Fin n → ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    (empiricalLaw x).map f = empiricalLaw (fun i => f (x i)) := by
  rw [empiricalLaw, Measure.map_map hf (show Measurable x from Measurable.of_discrete)]
  rfl

/-- Coordinatewise transformation commutes with IID empirical resampling. -/
theorem bootstrapLaw_map_statistic (x : Fin n → ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    (bootstrapLaw x).map (fun b : Fin n → ℝ => fun i => f (b i)) =
      bootstrapLaw (fun i => f (x i)) := by
  unfold bootstrapLaw
  rw [Measure.pi_map_pi (μ := fun _ : Fin n => empiricalLaw x)
    (f := fun _ : Fin n => f) (fun _ => hf.aemeasurable)]
  simp only [empiricalLaw_map_statistic x hf]

/-- Every transformed bootstrap sample mean is square integrable: the
conditional empirical support is finite. -/
theorem bootstrap_transformed_sampleMean_memLp (x : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) :
    MemLp (fun b => sampleMean (fun i => f (b i))) 2 (bootstrapLaw x) := by
  have : IsProbabilityMeasure (bootstrapLaw x) := bootstrapLaw_isProbabilityMeasure x
  apply sampleMean_memLp
  intro i
  have hi : HasLaw (fun b : Fin n → ℝ => b i) (empiricalLaw x) (bootstrapLaw x) :=
    ⟨(measurable_pi_apply i).aemeasurable,
      (measurePreserving_eval (fun _ : Fin n => empiricalLaw x) i).map_eq⟩
  have hfLaw : HasLaw f (empiricalLaw (fun j => f (x j))) (empiricalLaw x) :=
    ⟨hf.aemeasurable, empiricalLaw_map_statistic x hf⟩
  exact (((hfLaw.comp hi).identDistrib HasLaw.id).memLp_iff).mpr
    (empiricalLaw_memLp (fun j => f (x j)) 2)

theorem bootstrap_sampleMean_memLp (x : Fin n → ℝ) :
    MemLp (sampleMean : (Fin n → ℝ) → ℝ) 2 (bootstrapLaw x) := by
  simpa only [id_eq] using bootstrap_transformed_sampleMean_memLp x measurable_id

/-- Exact conditional squared error of the bootstrap sample mean. -/
theorem bootstrap_sampleMean_mse (x : Fin n → ℝ) :
    (∫ b, (sampleMean b - sampleMean x) ^ 2 ∂bootstrapLaw x) = empiricalVariance x / n := by
  have hm : Measurable (sampleMean : (Fin n → ℝ) → ℝ) := by unfold sampleMean; fun_prop
  have h := variance_eq_integral (μ := bootstrapLaw x) hm.aemeasurable
  rw [bootstrap_sampleMean_expectation] at h
  exact h.symm.trans (bootstrap_sampleMean_variance x)

/-- Exact conditional squared error of a transformed bootstrap sample mean. -/
theorem bootstrap_transformed_sampleMean_mse (x : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ b, (sampleMean (fun i => f (b i)) - sampleMean (fun i => f (x i))) ^ 2 ∂bootstrapLaw x) =
      empiricalVariance (fun i => f (x i)) / n := by
  have hm : Measurable (fun b : Fin n → ℝ => fun i => f (b i)) :=
    measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i))
  have hlaw : HasLaw (fun b : Fin n → ℝ => fun i => f (b i))
      (bootstrapLaw (fun i => f (x i))) (bootstrapLaw x) :=
    ⟨hm.aemeasurable, bootstrapLaw_map_statistic x hf⟩
  have h := hlaw.integral_comp (show AEStronglyMeasurable
    (fun b : Fin n → ℝ => (sampleMean b - sampleMean (fun i => f (x i))) ^ 2)
    (bootstrapLaw (fun i => f (x i))) from (by unfold sampleMean; fun_prop : Measurable _).aestronglyMeasurable)
  exact h.trans (bootstrap_sampleMean_mse (fun i => f (x i)))

/-- The bootstrap second raw sample moment has conditional squared error
bounded by the empirical fourth moment divided by the resample size. -/
theorem bootstrap_secondMoment_mse_le (x : Fin n → ℝ) :
    (∫ b, (sampleMean (fun i => b i ^ 2) - sampleMean (fun i => x i ^ 2)) ^ 2 ∂bootstrapLaw x) ≤
      sampleMean (fun i => x i ^ 4) / n := by
  rw [bootstrap_transformed_sampleMean_mse x (by fun_prop : Measurable (fun y : ℝ => y ^ 2)),
    empiricalVariance_eq_secondMoment_sub_sq]
  have he : (fun i => (x i ^ 2) ^ 2) = (fun i => x i ^ 4) := by funext i; ring
  rw [he]
  exact div_le_div_of_nonneg_right (sub_le_self _ (sq_nonneg _)) (Nat.cast_nonneg n)

end LectureNotes
