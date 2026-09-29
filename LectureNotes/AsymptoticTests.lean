import LectureNotes.DeltaMethod
import LectureNotes.GaussianQuadraticForms

set_option autoImplicit false

/-! L7/L10: the limit arguments for score-root estimators and scalar Wald,
score, and likelihood-ratio tests. Analytic expansions and convergence of
curvature must be verified for each model; they are explicit hypotheses here. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

theorem standard_normal_square {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) Q) :
    HasLaw (fun ω => Z ω ^ 2) (chiSquared 1) Q := by
  simpa using chiSquared_sum (Z := fun _ : Fin 1 => Z) (fun _ => hZ)
    iIndepFun.of_subsingleton

/-- A standardized asymptotically normal statistic gives a chi-square test. -/
theorem asymptotic_normal_square {T : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hT : ConvergesInDistribution P Q T Z) (hZ : HasLaw Z (gaussianReal 0 1) Q) :
    ConvergesInDistribution P Q (fun n ω => T n ω ^ 2) (fun ω => Z ω ^ 2) ∧
      HasLaw (fun ω => Z ω ^ 2) (chiSquared 1) Q :=
  ⟨continuous_mapping_distribution (g := fun x => x ^ 2) (by fun_prop) hT,
    standard_normal_square hZ⟩

/-- L10's scalar Wald argument, with a strictly positive limiting standard
error. The exact limiting law is obtained by dividing the original limit. -/
theorem studentization {T S : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {σ : ℝ}
    (hσ : 0 < σ) (hT : ConvergesInDistribution P Q T Z)
    (hS : ConvergesInProbability P S (fun _ => σ))
    (hSm : ∀ n, AEMeasurable (S n) P)
    (hZ : HasLaw Z (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) Q) :
    ConvergesInDistribution P Q (fun n ω => T n ω / S n ω) (fun ω => Z ω / σ) ∧
      HasLaw (fun ω => Z ω / σ) (gaussianReal 0 1) Q := by
  refine ⟨slutsky_div hσ.ne' hT hS hSm, ?_⟩
  have h := gaussianReal_div_const hZ σ
  convert! h using 1
  simp only [zero_div]
  congr 1
  apply Subtype.ext
  change 1 = σ ^ 2 / σ ^ 2
  exact (div_self (pow_ne_zero 2 hσ.ne')).symm

/-- The probabilistic step of L7's score expansion. `S` is the normalized
score and `H` the negative normalized curvature; an actual expansion says
`H * E = S`, where `E` is the normalized estimation error. -/
theorem score_root_limit {S H E : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {I : ℝ}
    (hI : 0 < I) (hS : ConvergesInDistribution P Q S Z)
    (hH : ConvergesInProbability P H (fun _ => I))
    (hHm : ∀ n, AEMeasurable (H n) P)
    (hroot : ∀ n, ∀ᵐ ω ∂P, H n ω * E n ω = S n ω)
    (hne : ∀ n, ∀ᵐ ω ∂P, H n ω ≠ 0) :
    ConvergesInDistribution P Q E (fun ω => Z ω / I) := by
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl))
    (slutsky_div hI.ne' hS hH hHm)
  intro n
  filter_upwards [hroot n, hne n] with ω hω hn
  exact (div_eq_iff hn).mpr (by linarith)

/-- L10's scalar Wilks limit, once the likelihood expansion and normalized
curvature convergence have been established. `E` is the standardized MLE error. -/
theorem wilks_from_quadratic_expansion {E H LR : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hE : ConvergesInDistribution P Q E Z) (hZ : HasLaw Z (gaussianReal 0 1) Q)
    (hH : ConvergesInProbability P H (fun _ => 1))
    (hHm : ∀ n, AEMeasurable (H n) P)
    (hexp : ∀ n, ∀ᵐ ω ∂P, LR n ω = E n ω ^ 2 * H n ω) :
    ConvergesInDistribution P Q LR (fun ω => Z ω ^ 2) ∧
      HasLaw (fun ω => Z ω ^ 2) (chiSquared 1) Q := by
  refine ⟨?_, standard_normal_square hZ⟩
  have h := slutsky_mul (continuous_mapping_distribution (by fun_prop :
    Continuous (fun x : ℝ => x ^ 2)) hE) hH hHm
  exact TendstoInDistribution.congr (fun n => (hexp n).mono (fun _ h => h.symm))
    (ae_of_all _ (fun _ => mul_one _)) h

/-- Equal first-order curvature implies equivalent quadratic test statistics.
This is the stochastic-product step used to compare LR, Wald, and score tests. -/
theorem quadratic_statistics_equivalent {E D : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hE : ConvergesInDistribution P Q E Z)
    (hD : ConvergesInProbability P D (fun _ => 0))
    (hDm : ∀ n, AEMeasurable (D n) P) :
    ConvergesInProbability P (fun n ω => E n ω ^ 2 * D n ω) (fun _ => 0) :=
  slutsky_mul_zero (continuous_mapping_distribution (g := fun x => x ^ 2)
    (by fun_prop) hE) hD hDm

/-- Weak convergence gives convergence of rejection probabilities at a region
whose boundary has zero limiting probability. This is what turns a distributional
limit into asymptotic test size. -/
theorem asymptotic_rejection_probability {T : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hT : ConvergesInDistribution P Q T Z) (R : Set ℝ) (hR : MeasurableSet R)
    (hboundary : Q.map Z (frontier R) = 0) :
    Tendsto (fun n => P.real {ω | T n ω ∈ R}) atTop
      (𝓝 (Q.real {ω | Z ω ∈ R})) := by
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hT.tendsto hboundary
  simp only [ProbabilityMeasure.coe_mk] at ht
  have hr := (ENNReal.continuousAt_toReal (measure_ne_top (Q.map Z) R)).tendsto.comp ht
  simpa only [Function.comp_def, Measure.map_apply_of_aemeasurable
    (hT.forall_aemeasurable _) hR,
    Measure.map_apply_of_aemeasurable hT.aemeasurable_limit hR, measureReal_def,
    Set.preimage, Set.setOf_mem_eq] using hr

end LectureNotes
