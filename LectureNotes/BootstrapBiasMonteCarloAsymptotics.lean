import LectureNotes.BootstrapBiasAsymptotics
import LectureNotes.MonteCarloBiasJoint

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

/-- The bias-corrected estimator computed from finitely many complete bootstrap resamples. -/
def simulatedBootstrapBiasCorrected {n B : ℕ} (g : ℝ → ℝ) (x : Fin n → ℝ)
    (b : Fin B → (Fin n → ℝ)) : ℝ :=
  g (sampleMean x) - simulatedBootstrapBias g x b

/-- The simulation algorithm subtracts the replicate average from twice the plug-in estimator. -/
theorem simulatedBootstrapBiasCorrected_eq {n B : ℕ} (g : ℝ → ℝ) (x : Fin n → ℝ)
    (b : Fin B → (Fin n → ℝ)) :
    simulatedBootstrapBiasCorrected g x b =
      2 * g (sampleMean x) - sampleMean (fun j => g (sampleMean (b j))) := by
  unfold simulatedBootstrapBiasCorrected simulatedBootstrapBias
  ring

/-- An almost-sure data error remains negligible in joint experiments with
an arbitrary independent seed space in each row. -/
theorem data_ae_zero_joint_row_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Γ : ℕ → Type*}
    [∀ n, MeasurableSpace (Γ n)] (Q : ∀ n, Measure (Γ n))
    [∀ n, IsProbabilityMeasure (Q n)] {E : ℕ → Ω → ℝ}
    (hE : ∀ n, Measurable (E n)) (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => E n ω) atTop (𝓝 0)) :
    RowProbabilityZero (fun n => P.prod (Q n)) (fun n z => E n z.1) := by
  apply conditional_probability_zero_joint P Q (fun n z => E n z.1)
    (fun n => (hE n).comp measurable_fst)
  filter_upwards [hlim] with ω hω
  intro ε hε
  have he : ∀ᶠ n in atTop, |E n ω| < ε := by
    exact hω.abs.eventually (gt_mem_nhds (by simpa using hε))
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with n hn
  have hs : {γ : Γ n | ε ≤ |E n ω|} = ∅ := by
    ext γ
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    exact not_le.mpr hn
  simp only [hs, measureReal_empty]

/-- Under actual finite-fourth-moment IID sampling and actual independent
resampling indices, the Monte Carlo bootstrap bias estimates the actual
sampling bias to error smaller than 1/n. The simulation count must satisfy
n/B(n)→0, and the transform is C³ with bounded third derivative and Lipschitz. -/
theorem iid_simulatedBootstrapBias_minus_samplingBias {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 3 g y| ≤ C) {L : ℝ≥0} (hL : LipschitzWith L g)
    {B : ℕ → ℕ} [∀ n, NeZero (B n)]
    (hB : Tendsto (fun n => (n + 1 : ℕ) / (B n : ℝ)) atTop (𝓝 0)) :
    RowProbabilityZero (bootstrapMonteCarloJointLaw P B)
      (fun n z => (n + 1 : ℕ) *
        (simulatedBootstrapBias g (fun i : Fin (n + 1) => X i z.1)
          (fun j => bootstrapSample (fun i : Fin (n + 1) => X i z.1) (z.2 j)) -
          ((∫ ω, g (sampleMean (fun i : Fin (n + 1) => X i ω)) ∂P) - g (∫ ω, X 0 ω ∂P)))) := by
  have hMC := iid_simulatedBootstrapBias_joint_scaled_probability hXm
    (hX.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)) hind hident hL hB
  let E n ω := (n + 1 : ℕ) * (bootstrapBias g (fun i : Fin (n + 1) => X i ω) -
    ((∫ ω', g (sampleMean (fun i : Fin (n + 1) => X i ω')) ∂P) - g (∫ ω', X 0 ω' ∂P)))
  have hE n : Measurable (E n) :=
    (((measurable_bootstrapBias hg.continuous.measurable).comp
      (measurable_pi_lambda _ (fun i => hXm i))).sub measurable_const).const_mul _
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => E n ω) atTop (𝓝 0) :=
    iid_bootstrapBias_minus_samplingBias hXm hX hind hident hg hC
  let Q n := Measure.pi (fun _ : Fin (B n) => bootstrapIndexLaw (n + 1))
  have hQ n : IsProbabilityMeasure (Q n) := by dsimp [Q, bootstrapIndexLaw]; infer_instance
  have hE' := data_ae_zero_joint_row_probability P Q hE hlim
  apply (hMC.add hE').congr
  exact Eventually.of_forall (fun n z => by dsimp [E]; ring)

end LectureNotes
