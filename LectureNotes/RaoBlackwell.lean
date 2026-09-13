import LectureNotes.ConditionalExpectation
import LectureNotes.Estimation

/-! L5 Theorem 5: one parameter-independent Rao–Blackwell estimator.
Sufficiency means that one Markov kernel is a regular conditional law of
the data given the statistic under every measure in the statistical model. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory

section Definitions
variable {Θ Ω S : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [MeasurableSpace S] (P : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (P θ)]

/-- A common conditional distribution of the data given a statistic. -/
def IsSufficientKernel (T : Ω → S) (K : Kernel S Ω) : Prop :=
  ∀ θ, ∀ᵐ ω ∂P θ, condDistrib id T (P θ) (T ω) = K (T ω)

/-- The conditional distribution of the data given `T` does not depend on the
parameter, up to the null sets appropriate to each model measure. -/
def IsSufficientStatistic (T : Ω → S) : Prop :=
  Measurable T ∧ ∃ K : Kernel S Ω, IsMarkovKernel K ∧ IsSufficientKernel P T K

end Definitions

/-- Integrating against the common conditional kernel gives a function of the
statistic alone. There is no parameter argument in this estimator. -/
def raoBlackwellEstimator {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (K : Kernel S Ω) (U : Ω → ℝ) (s : S) : ℝ := ∫ ω, U ω ∂K s

theorem raoBlackwellEstimator_measurable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (K : Kernel S Ω) [IsMarkovKernel K] {U : Ω → ℝ} (hU : Measurable U) :
    Measurable (raoBlackwellEstimator K U) :=
  hU.stronglyMeasurable.integral_kernel.measurable

section Model
variable {Θ Ω S : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [mS : MeasurableSpace S] {P : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (P θ)]
  {T : Ω → S} {K : Kernel S Ω}

/-- A common disintegration of the joint law gives a sufficient conditional
kernel. This criterion uses equality of measures, including on continuous fibers. -/
theorem sufficientKernel_of_disintegration (hT : Measurable T) [IsMarkovKernel K]
    (hK : ∀ θ, (P θ).map (fun ω => (T ω, ω)) = (P θ).map T ⊗ₘ K) :
    IsSufficientKernel P T K := by
  intro θ
  have hc := condDistrib_ae_eq_of_measure_eq_compProd T
    (Y := id) (μ := P θ) aemeasurable_id (hK θ)
  exact hc.comp_tendsto (Measure.tendsto_ae_map hT.aemeasurable)

/-- The same kernel integral is a conditional expectation under every parameter. -/
theorem sufficientKernel_condExp (hT : Measurable T) (hK : IsSufficientKernel P T K)
    {U : Ω → ℝ} (θ : Θ) (hU : Integrable U (P θ)) :
    (P θ)[U | mS.comap T] =ᵐ[P θ] (fun ω => raoBlackwellEstimator K U (T ω)) := by
  have hc := condExp_ae_eq_integral_condDistrib_id hT hU
  filter_upwards [hc, hK θ] with ω hω hKω
  simpa only [raoBlackwellEstimator, hKω] using hω

/-- L5 Theorem 5: construct one measurable function of the sufficient statistic
that preserves the estimator's mean and improves squared-error risk for every
parameter. Square integrability is proved for the constructed estimator. -/
theorem rao_blackwell_sufficient (hT : IsSufficientStatistic P T)
    {U : Ω → ℝ} (hUm : Measurable U) (hU : ∀ θ, MemLp U 2 (P θ)) (target : Θ → ℝ) :
    ∃ g : S → ℝ, Measurable g ∧ ∀ θ,
      MemLp (fun ω => g (T ω)) 2 (P θ) ∧
      (∫ ω, g (T ω) ∂P θ) = (∫ ω, U ω ∂P θ) ∧
      mse (P θ) (fun ω => g (T ω)) (target θ) ≤ mse (P θ) U (target θ) := by
  obtain ⟨hTm, K, hKM, hK⟩ := hT
  let : IsMarkovKernel K := hKM
  refine ⟨raoBlackwellEstimator K U, raoBlackwellEstimator_measurable K hUm, ?_⟩
  intro θ
  have hc := sufficientKernel_condExp hTm hK θ ((hU θ).integrable (by norm_num))
  have hLp := (memLp_congr_ae hc).mp
    ((hU θ).condExp (m := mS.comap T) (by norm_num : (1 : ENNReal) ≤ 2))
  refine ⟨hLp, ?_, ?_⟩
  · exact (integral_congr_ae hc.symm).trans (integral_condExp hTm.comap_le)
  · calc
      mse (P θ) (fun ω => raoBlackwellEstimator K U (T ω)) (target θ) =
          mse (P θ) ((P θ)[U | mS.comap T]) (target θ) := by
        apply integral_congr_ae
        filter_upwards [hc] with ω hω
        rw [hω]
      _ ≤ mse (P θ) U (target θ) := rao_blackwell_mse (P θ) hTm.comap_le (hU θ) (target θ)

/-- The same unbiased estimator has no larger MSE or variance throughout the
parameter family. -/
theorem rao_blackwell_unbiased_sufficient (hT : IsSufficientStatistic P T)
    {U : Ω → ℝ} (hUm : Measurable U) (hU : ∀ θ, MemLp U 2 (P θ)) (target : Θ → ℝ)
    (hunbiased : ∀ θ, Unbiased (P θ) U (target θ)) :
    ∃ g : S → ℝ, Measurable g ∧ ∀ θ,
      Unbiased (P θ) (fun ω => g (T ω)) (target θ) ∧
      mse (P θ) (fun ω => g (T ω)) (target θ) ≤ mse (P θ) U (target θ) ∧
      Var[fun ω => g (T ω); P θ] ≤ Var[U; P θ] := by
  obtain ⟨g, hgm, hg⟩ := rao_blackwell_sufficient hT hUm hU target
  refine ⟨g, hgm, fun θ => ?_⟩
  refine ⟨⟨(hg θ).1.integrable (by norm_num), (hg θ).2.1.trans (hunbiased θ).2⟩, (hg θ).2.2, ?_⟩
  have hrisk := (hg θ).2.2
  rw [mse_eq_variance_add_bias_sq (P θ) (hg θ).1,
    mse_eq_variance_add_bias_sq (P θ) (hU θ)] at hrisk
  simpa [bias, (hg θ).2.1, (hunbiased θ).2] using hrisk

end Model
end LectureNotes
