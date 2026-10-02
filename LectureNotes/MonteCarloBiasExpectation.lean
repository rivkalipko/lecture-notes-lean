import LectureNotes.BootstrapBiasCorrection
import LectureNotes.BootstrapBiasMonteCarloAsymptotics

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

/-- A positive finite number of independent replicates preserves the expectation
of every integrable statistic. -/
theorem monteCarlo_sampleMean_expectation {Γ : Type*} [MeasurableSpace Γ]
    (Q : Measure Γ) [IsProbabilityMeasure Q] {Y : Γ → ℝ}
    (hY : Integrable Y Q) {B : ℕ} [NeZero B] :
    Integrable (fun z : Fin B → Γ => sampleMean (fun j => Y (z j)))
        (Measure.pi (fun _ : Fin B => Q)) ∧
      (∫ z, sampleMean (fun j : Fin B => Y (z j))
        ∂Measure.pi (fun _ : Fin B => Q)) = ∫ γ, Y γ ∂Q := by
  have hi (j : Fin B) : Integrable (fun z : Fin B → Γ => Y (z j))
      (Measure.pi (fun _ : Fin B => Q)) :=
    (measurePreserving_eval (fun _ : Fin B => Q) j).integrable_comp_of_integrable hY
  refine ⟨?_, sampleMean_expectation (Nat.pos_of_ne_zero (NeZero.ne B)) hi ?_⟩
  · unfold sampleMean
    exact (integrable_finsetSum _ (fun j _ => hi j)).const_mul _
  · intro j
    exact (measurePreserving_eval (fun _ : Fin B => Q) j).hasLaw.integral_comp
      hY.aestronglyMeasurable

/-- The simulated conditional bias is unbiased for the exact conditional bias,
for every positive replicate count. -/
theorem simulatedBootstrapBias_expectation {n B : ℕ} [NeZero n] [NeZero B]
    (x : Fin n → ℝ) {g : ℝ → ℝ}
    (hg : Integrable (fun b => g (sampleMean b)) (bootstrapLaw x)) :
    (∫ b, simulatedBootstrapBias g x b
      ∂Measure.pi (fun _ : Fin B => bootstrapLaw x)) = bootstrapBias g x := by
  let := bootstrapLaw_isProbabilityMeasure x
  have h := monteCarlo_sampleMean_expectation (B := B) (bootstrapLaw x) hg
  unfold simulatedBootstrapBias bootstrapBias
  rw [integral_sub h.1 (integrable_const _), h.2]
  simp

/-- Conditional expected correction agrees exactly with the correction based on
the full bootstrap distribution. -/
theorem simulatedBootstrapBiasCorrected_expectation {n B : ℕ} [NeZero n] [NeZero B]
    (x : Fin n → ℝ) {g : ℝ → ℝ}
    (hg : Integrable (fun b => g (sampleMean b)) (bootstrapLaw x)) :
    (∫ b, simulatedBootstrapBiasCorrected g x b
      ∂Measure.pi (fun _ : Fin B => bootstrapLaw x)) = bootstrapBiasCorrected g x := by
  let := bootstrapLaw_isProbabilityMeasure x
  have h := monteCarlo_sampleMean_expectation (B := B) (bootstrapLaw x) hg
  have hi : Integrable (simulatedBootstrapBias g x)
      (Measure.pi (fun _ : Fin B => bootstrapLaw x)) := h.1.sub (integrable_const _)
  unfold simulatedBootstrapBiasCorrected bootstrapBiasCorrected
  rw [integral_sub (integrable_const _) hi, simulatedBootstrapBias_expectation x hg]
  simp

/-- Uniform index arrays implement the same conditional expectation. Their
finite state space makes every finite-valued resampling statistic integrable. -/
theorem simulatedBootstrapBiasCorrected_index_expectation {n B : ℕ}
    [NeZero n] [NeZero B] (x : Fin n → ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    (∫ z : Fin B → (Fin n → Fin n),
      simulatedBootstrapBiasCorrected g x (fun j => bootstrapSample x (z j))
      ∂Measure.pi (fun _ : Fin B => bootstrapIndexLaw n)) = bootstrapBiasCorrected g x := by
  have : IsProbabilityMeasure (bootstrapIndexLaw n) := by unfold bootstrapIndexLaw; infer_instance
  have hi : Integrable (fun b : Fin n → Fin n => g (sampleMean (bootstrapSample x b))) (bootstrapIndexLaw n) :=
    (MemLp.of_discrete : MemLp _ 1 _).integrable le_rfl
  have h := monteCarlo_sampleMean_expectation (B := B) (bootstrapIndexLaw n) hi
  have hm : Measurable (sampleMean : (Fin n → ℝ) → ℝ) := by unfold sampleMean; fun_prop
  have he : (∫ b : Fin n → Fin n, g (sampleMean (bootstrapSample x b)) ∂bootstrapIndexLaw n) =
      ∫ b, g (sampleMean b) ∂bootstrapLaw x := by
    simpa only [Function.comp_def] using!
      (bootstrapSample_hasLaw x).integral_comp (hg.comp hm).aestronglyMeasurable
  simp_rw [simulatedBootstrapBiasCorrected_eq]
  rw [integral_sub (integrable_const _) h.1, h.2]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [he]
  unfold bootstrapBiasCorrected bootstrapBias
  ring

/-- Fubini turns conditional unbiasedness into equality of the actual joint
expectations. The integrability hypothesis is on the simulated estimator under
the data and independent index-array experiment. -/
theorem simulatedBootstrapBiasCorrected_joint_expectation {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n B : ℕ} [NeZero n] [NeZero B]
    (X : Ω → (Fin n → ℝ)) {g : ℝ → ℝ} (hg : Measurable g)
    (hi : Integrable (fun z : Ω × (Fin B → (Fin n → Fin n)) =>
      simulatedBootstrapBiasCorrected g (X z.1) (fun j => bootstrapSample (X z.1) (z.2 j)))
      (P.prod (Measure.pi (fun _ : Fin B => bootstrapIndexLaw n)))) :
    (∫ z, simulatedBootstrapBiasCorrected g (X z.1)
        (fun j => bootstrapSample (X z.1) (z.2 j))
        ∂P.prod (Measure.pi (fun _ : Fin B => bootstrapIndexLaw n))) =
      ∫ ω, bootstrapBiasCorrected g (X ω) ∂P := by
  have : IsProbabilityMeasure (bootstrapIndexLaw n) := by unfold bootstrapIndexLaw; infer_instance
  rw [integral_prod _ hi]
  congr 1
  funext ω
  exact simulatedBootstrapBiasCorrected_index_expectation (B := B) (X ω) hg

private theorem abs_sampleMean_le_bound {n : ℕ} [NeZero n] {x : Fin n → ℝ} {M : ℝ}
    (hx : ∀ i, |x i| ≤ M) : |sampleMean x| ≤ M := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  calc
    |sampleMean x| = (n : ℝ)⁻¹ * |∑ i, x i| := by
      simp [sampleMean, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n) : 0 ≤ (n : ℝ)⁻¹)]
    _ ≤ (n : ℝ)⁻¹ * ∑ i, |x i| := mul_le_mul_of_nonneg_left
      (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, M := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => hx i)) (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ = M := by simp [hn]

/-- Bounded observations and a continuous transform give joint integrability of
the finite-replicate corrected estimator. No derivative or replicate growth
condition is needed for this finite-sample assertion. -/
theorem simulatedBootstrapBiasCorrected_joint_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n B : ℕ} [NeZero n] [NeZero B]
    {X : Ω → (Fin n → ℝ)} (hX : Measurable X) {M : ℝ}
    (hbound : ∀ᵐ ω ∂P, ∀ i, |X ω i| ≤ M)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun z : Ω × (Fin B → (Fin n → Fin n)) =>
      simulatedBootstrapBiasCorrected g (X z.1) (fun j => bootstrapSample (X z.1) (z.2 j)))
      (P.prod (Measure.pi (fun _ : Fin B => bootstrapIndexLaw n))) := by
  have : IsProbabilityMeasure (bootstrapIndexLaw n) := by unfold bootstrapIndexLaw; infer_instance
  let Q := Measure.pi (fun _ : Fin B => bootstrapIndexLaw n)
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-M) M) hg.continuousOn
  have hb (j : Fin B) : Measurable (fun z : Ω × (Fin B → (Fin n → Fin n)) =>
      bootstrapSample (X z.1) (z.2 j)) :=
    measurable_bootstrapSample_pair.comp ((hX.comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd))
  have hm : Measurable (sampleMean : (Fin n → ℝ) → ℝ) := by unfold sampleMean; fun_prop
  have hsim : Measurable (fun z : Ω × (Fin B → (Fin n → Fin n)) =>
      simulatedBootstrapBiasCorrected g (X z.1) (fun j => bootstrapSample (X z.1) (z.2 j))) := by
    simp only [simulatedBootstrapBiasCorrected_eq]
    unfold sampleMean
    fun_prop
  apply (integrable_const (3 * K)).mono' hsim.aestronglyMeasurable
  have hdata : ∀ᵐ z : Ω × (Fin B → (Fin n → Fin n)) ∂P.prod Q,
      ∀ i, |X z.1 i| ≤ M :=
    (measurePreserving_fst (μ := P) (ν := Q)).quasiMeasurePreserving.ae hbound
  filter_upwards [hdata] with z hz
  have hobs : |g (sampleMean (X z.1))| ≤ K :=
    hK _ (abs_le.mp (abs_sampleMean_le_bound hz))
  have hrep (j : Fin B) : |g (sampleMean (bootstrapSample (X z.1) (z.2 j)))| ≤ K :=
    hK _ (abs_le.mp (abs_sampleMean_le_bound (fun i => hz ((z.2 j) i))))
  rw [simulatedBootstrapBiasCorrected_eq, Real.norm_eq_abs]
  calc
    |2 * g (sampleMean (X z.1)) - sampleMean (fun j =>
        g (sampleMean (bootstrapSample (X z.1) (z.2 j))))| ≤
      |2 * g (sampleMean (X z.1))| + |sampleMean (fun j =>
        g (sampleMean (bootstrapSample (X z.1) (z.2 j))))| := abs_sub _ _
    _ ≤ 3 * K := by
      have hh := abs_sampleMean_le_bound hrep
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith

/-- Finite simulation has exactly the same expected correction as the full
bootstrap law for bounded data and every continuous transform. -/
theorem simulatedBootstrapBiasCorrected_joint_expectation_of_bounded
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n B : ℕ} [NeZero n] [NeZero B] {X : Ω → (Fin n → ℝ)}
    (hX : Measurable X) {M : ℝ} (hbound : ∀ᵐ ω ∂P, ∀ i, |X ω i| ≤ M)
    {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ z, simulatedBootstrapBiasCorrected g (X z.1)
        (fun j => bootstrapSample (X z.1) (z.2 j))
        ∂P.prod (Measure.pi (fun _ : Fin B => bootstrapIndexLaw n))) =
      ∫ ω, bootstrapBiasCorrected g (X ω) ∂P :=
  simulatedBootstrapBiasCorrected_joint_expectation X hg.measurable
    (simulatedBootstrapBiasCorrected_joint_integrable hX hbound hg)

/-- The actually simulated correction has bias o(1/n) under the proved
expectation-level bootstrap correction assumptions. Any positive finite number
of replicates in each row suffices, including a constant number of replicates. -/
theorem iid_simulatedBootstrapBiasCorrected_bias_limit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ ω ∂P, ∀ i, |X i ω| ≤ M)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) {C₂ C₃ : ℝ}
    (hC₂ : ∀ y, |iteratedDeriv 2 g y| ≤ C₂)
    (hC₃ : ∀ y, |iteratedDeriv 3 g y| ≤ C₃)
    (B : ℕ → ℕ) [∀ n, NeZero (B n)] :
    Tendsto (fun n => (n + 1 : ℕ) *
      ((∫ z, simulatedBootstrapBiasCorrected g (fun i : Fin (n + 1) => X i z.1)
          (fun j => bootstrapSample (fun i : Fin (n + 1) => X i z.1) (z.2 j))
          ∂bootstrapMonteCarloJointLaw P B n) - g (∫ ω, X 0 ω ∂P))) atTop (𝓝 0) := by
  have he (n : ℕ) := simulatedBootstrapBiasCorrected_joint_expectation_of_bounded
    (B := B n) (measurable_pi_lambda _ (fun i : Fin (n + 1) => hXm i))
    (hbound.mono (fun ω hω i => hω i)) hg.continuous
  simp only [bootstrapMonteCarloJointLaw, he]
  exact iid_bootstrapBiasCorrected_bias_limit hXm hind hident hM hbound hg hC₂ hC₃

end LectureNotes
