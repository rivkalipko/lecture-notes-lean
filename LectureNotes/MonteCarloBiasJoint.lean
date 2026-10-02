import LectureNotes.MonteCarloBias
import LectureNotes.MonteCarloBootstrapIntervals

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

/-- Conditional errors converging to zero almost surely in the data also
converge under the actual joint data/seed experiment. -/
theorem conditional_probability_zero_joint {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Γ : ℕ → Type*}
    [∀ n, MeasurableSpace (Γ n)] (Q : ∀ n, Measure (Γ n))
    [∀ n, IsProbabilityMeasure (Q n)] (E : ∀ n, Ω × Γ n → ℝ)
    (hE : ∀ n, Measurable (E n))
    (hcond : ∀ᵐ ω ∂P, ∀ ε > 0, Tendsto
      (fun n => (Q n).real {γ | ε ≤ |E n (ω, γ)|}) atTop (𝓝 0)) :
    RowProbabilityZero (fun n => P.prod (Q n)) E := by
  intro ε hε
  let A n : Set (Ω × Γ n) := {z | ε ≤ ‖E n z‖}
  have hA n : MeasurableSet (A n) := measurableSet_le measurable_const (hE n).norm
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => (Q n).real (Prod.mk ω ⁻¹' A n)) atTop (𝓝 0) := by
    filter_upwards [hcond] with ω hω
    simpa only [A, Real.norm_eq_abs] using! hω ε hε
  have hc := tendsto_integral_of_dominated_convergence (μ := P) (fun _ => (1 : ℝ))
    (fun n => (measurable_measure_prodMk_left (hA n)).ennreal_toReal.aestronglyMeasurable)
    (integrable_const 1)
    (fun n => ae_of_all _ fun ω => by
      change ‖(Q n).real (Prod.mk ω ⁻¹' A n)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one (μ := Q n)) hlim
  simp only [integral_zero] at hc
  change Tendsto (fun n => ∫ ω, (Q n).real (Prod.mk ω ⁻¹' A n) ∂P) atTop (𝓝 0) at hc
  have he n := measureReal_prod_event P (Q n) (hA n)
  change Tendsto (fun n => (P.prod (Q n)).real (A n)) atTop (𝓝 0)
  simpa only [← he] using hc

/-- The exact conditional bias is measurable in the observed finite sample;
this follows from the genuine fixed-index representation of resampling. -/
theorem measurable_bootstrapBias {n : ℕ} [NeZero n] {g : ℝ → ℝ}
    (hg : Measurable g) : Measurable (bootstrapBias (n := n) g) := by
  have : IsProbabilityMeasure (bootstrapIndexLaw n) := by unfold bootstrapIndexLaw; infer_instance
  have hm : Measurable (sampleMean : (Fin n → ℝ) → ℝ) := by unfold sampleMean; fun_prop
  have hJ : Measurable (fun z : (Fin n → ℝ) × (Fin n → Fin n) =>
      g (sampleMean (bootstrapSample z.1 z.2))) := hg.comp (hm.comp measurable_bootstrapSample_pair)
  have he (x : Fin n → ℝ) : bootstrapBias g x =
      (∫ b, g (sampleMean (bootstrapSample x b)) ∂bootstrapIndexLaw n) - g (sampleMean x) := by
    unfold bootstrapBias
    congr 1
    simpa only [Function.comp_def] using!
      ((bootstrapSample_hasLaw x).integral_comp (hg.comp hm).aestronglyMeasurable).symm
  simp_rw [show bootstrapBias (n := n) g = (fun x =>
    (∫ b, g (sampleMean (bootstrapSample x b)) ∂bootstrapIndexLaw n) - g (sampleMean x))
      from funext he]
  exact hJ.stronglyMeasurable.integral_prod_right'.measurable.sub (hg.comp hm)

/-- B independent uniform index vectors generate B independent full
bootstrap samples, with their actual conditional product law. -/
theorem bootstrap_replicates_index_hasLaw {n B : ℕ} [NeZero n] (x : Fin n → ℝ) :
    HasLaw (fun z : Fin B → (Fin n → Fin n) => fun j => bootstrapSample x (z j))
      (Measure.pi (fun _ : Fin B => bootstrapLaw x))
      (Measure.pi (fun _ : Fin B => bootstrapIndexLaw n)) := by
  have : IsProbabilityMeasure (bootstrapIndexLaw n) := by unfold bootstrapIndexLaw; infer_instance
  have hm : AEMeasurable (fun b : Fin n → Fin n => bootstrapSample x b) (bootstrapIndexLaw n) :=
    (bootstrapSample_hasLaw x).aemeasurable
  apply (iIndepFun_pi (μ := fun _ : Fin B => bootstrapIndexLaw n) (fun _ => hm)).hasLaw_pi
  intro j
  exact (bootstrapSample_hasLaw x).comp (measurePreserving_eval
    (fun _ : Fin B => bootstrapIndexLaw n) j).hasLaw

/-- Conditional control of Monte Carlo bias error transfers to the joint law
of actual observations and independent index arrays, with no extra data moment
or domination assumption. -/
theorem simulatedBootstrapBias_joint_probability_of_conditional {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) {g : ℝ → ℝ} (hg : Measurable g)
    {B : ℕ → ℕ} [∀ n, NeZero (B n)]
    (hcond : ∀ᵐ ω ∂P, ∀ ε > 0, Tendsto (fun n =>
      (Measure.pi (fun _ : Fin (B n) => bootstrapLaw (fun i : Fin (n + 1) => X i ω))).real
      {z | ε ≤ |(n + 1 : ℕ) * (simulatedBootstrapBias g (fun i : Fin (n + 1) => X i ω) z -
        bootstrapBias g (fun i : Fin (n + 1) => X i ω))|}) atTop (𝓝 0)) :
    RowProbabilityZero (bootstrapMonteCarloJointLaw P B)
      (fun n z => (n + 1 : ℕ) * (simulatedBootstrapBias g (fun i : Fin (n + 1) => X i z.1)
        (fun j => bootstrapSample (fun i : Fin (n + 1) => X i z.1) (z.2 j)) -
          bootstrapBias g (fun i : Fin (n + 1) => X i z.1))) := by
  let Q n := Measure.pi (fun _ : Fin (B n) => bootstrapIndexLaw (n + 1))
  have hQ n : IsProbabilityMeasure (Q n) := by dsimp [Q, bootstrapIndexLaw]; infer_instance
  let E (n : ℕ) (z : Ω × (Fin (B n) → (Fin (n + 1) → Fin (n + 1)))) :=
    (n + 1 : ℕ) * (simulatedBootstrapBias g (fun i : Fin (n + 1) => X i z.1)
      (fun j => bootstrapSample (fun i : Fin (n + 1) => X i z.1) (z.2 j)) -
        bootstrapBias g (fun i : Fin (n + 1) => X i z.1))
  have hdata n : Measurable (fun ω => fun i : Fin (n + 1) => X i ω) :=
    measurable_pi_lambda _ (fun i => hXm i)
  have hE n : Measurable (E n) := by
    have hb (j : Fin (B n)) : Measurable (fun z : Ω × (Fin (B n) → (Fin (n + 1) → Fin (n + 1))) =>
        bootstrapSample (fun i : Fin (n + 1) => X i z.1) (z.2 j)) :=
      measurable_bootstrapSample_pair.comp (((hdata n).comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd))
    have hm : Measurable (sampleMean : (Fin (n + 1) → ℝ) → ℝ) := by unfold sampleMean; fun_prop
    have hsim : Measurable (fun z : Ω × (Fin (B n) → (Fin (n + 1) → Fin (n + 1))) =>
        sampleMean (fun j => g (sampleMean (bootstrapSample (fun i : Fin (n + 1) => X i z.1) (z.2 j))))) := by
      unfold sampleMean
      fun_prop
    exact measurable_const.mul ((hsim.sub ((hg.comp hm).comp ((hdata n).comp measurable_fst))).sub
      ((measurable_bootstrapBias hg).comp ((hdata n).comp measurable_fst)))
  apply conditional_probability_zero_joint P Q E hE
  filter_upwards [hcond] with ω hω
  intro ε hε
  have he n : (Q n).real {z | ε ≤ |E n (ω, z)|} =
      (Measure.pi (fun _ : Fin (B n) => bootstrapLaw (fun i : Fin (n + 1) => X i ω))).real
      {z | ε ≤ |(n + 1 : ℕ) * (simulatedBootstrapBias g (fun i : Fin (n + 1) => X i ω) z -
        bootstrapBias g (fun i : Fin (n + 1) => X i ω))|} := by
    have hm : Measurable (fun z : Fin (B n) → (Fin (n + 1) → ℝ) =>
        (n + 1 : ℕ) * (simulatedBootstrapBias g (fun i : Fin (n + 1) => X i ω) z -
          bootstrapBias g (fun i : Fin (n + 1) => X i ω))) := by
      unfold simulatedBootstrapBias sampleMean
      fun_prop
    have hh := (bootstrap_replicates_index_hasLaw (B := B n) (fun i : Fin (n + 1) => X i ω)).measureReal_eq
      (measurableSet_le (measurable_const (a := ε)) hm.abs)
    simpa only [Q, E] using! hh
  simpa only [he] using hω ε hε

/-- For IID square-integrable observations and a Lipschitz transform, taking
B(n)/n to infinity makes the simulated bias accurate on the bias's 1/n scale
under the actual joint data and resampling-index experiment. -/
theorem iid_simulatedBootstrapBias_joint_scaled_probability {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {g : ℝ → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {B : ℕ → ℕ} [∀ n, NeZero (B n)]
    (hB : Tendsto (fun n => (n + 1 : ℕ) / (B n : ℝ)) atTop (𝓝 0)) :
    RowProbabilityZero (bootstrapMonteCarloJointLaw P B)
      (fun n z => (n + 1 : ℕ) * (simulatedBootstrapBias g (fun i : Fin (n + 1) => X i z.1)
        (fun j => bootstrapSample (fun i : Fin (n + 1) => X i z.1) (z.2 j)) -
          bootstrapBias g (fun i : Fin (n + 1) => X i z.1))) :=
  simulatedBootstrapBias_joint_probability_of_conditional hXm hg.continuous.measurable
    (iid_simulatedBootstrapBias_scaled_probability hXm hX hind hident hg hB)

end LectureNotes
