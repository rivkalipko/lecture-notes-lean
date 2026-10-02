import LectureNotes.BootstrapMomentLinearization
import LectureNotes.MeanVarianceAsymptotics

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
attribute [local instance] bootstrapLaw_isProbabilityMeasure

/-- IID sampling supplies all moment limits needed for the conditional
mean/variance linearization, on one almost-sure event. -/
theorem iid_bootstrap_meanVariance_linear_conditions {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => (sampleMean (fun i : Fin (n + 1) => X i ω),
        sampleVariance (fun i : Fin (n + 1) => X i ω))) atTop (𝓝 (P[X 0], Var[X 0; P])) ∧
      Tendsto (fun n => empiricalVariance (fun i : Fin (n + 1) => X i ω)) atTop (𝓝 (Var[X 0; P])) ∧
      Tendsto (fun n => empiricalVariance
        (fun i : Fin (n + 1) => (X i ω - P[X 0]) ^ 2)) atTop
          (𝓝 (Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P])) ∧
      ∀ ε > 0, Tendsto (fun n => (bootstrapLaw (fun i : Fin (n + 1) => X i ω)).real {b : Fin (n + 1) → ℝ |
        ε ≤ |Real.sqrt ((n : ℝ) + 1) *
          (sampleVariance b - sampleVariance (fun i : Fin (n + 1) => X i ω)) -
          Real.sqrt ((n : ℝ) + 1) *
            (sampleMean (fun i => (b i - P[X 0]) ^ 2) -
              sampleMean (fun i : Fin (n + 1) => (X i ω - P[X 0]) ^ 2))|}) atTop (𝓝 0) := by
  have h₂ : MemLp (X 0) 2 P := hX.mono_exponent (by norm_num)
  let g : ℝ → ℝ := fun x => (x - P[X 0]) ^ 2
  have hg : Measurable g := by dsimp only [g]; fun_prop
  let Y : ℕ → Ω → ℝ := fun i ω => g (X i ω)
  have hYm i : Measurable (Y i) := hg.comp (hXm i)
  have hY : MemLp (Y 0) 2 P := by
    apply (memLp_two_iff_integrable_sq (hYm 0).aestronglyMeasurable).mpr
    simpa only [Y, g, Function.comp_def, Pi.pow_apply, Pi.sub_apply, Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by norm_num,
      pow_mul, sq_abs] using (hX.sub (memLp_const (P[X 0]))).integrable_norm_pow' (p := 4)
  have hmeans := iid_sampleMean_succ_ae (h₂.integrable (by norm_num)) hind hident
  have hvars := iid_mean_variance_strong_consistency hXm h₂ hind hident
  have hemp := empiricalVariance_strong_consistency hXm h₂ hind hident
  have hYi : iIndepFun Y P := hind.comp (fun _ => g) (fun _ => hg)
  have hYd i : IdentDistrib (Y i) (Y 0) P P := (hident i).comp hg
  have hsq := empiricalVariance_strong_consistency hYm hY hYi hYd
  filter_upwards [hmeans, hvars, hemp, hsq] with ω hm hv he hs
  have hmv : Tendsto (fun n => (sampleMean (fun i : Fin (n + 1) => X i ω),
      sampleVariance (fun i : Fin (n + 1) => X i ω))) atTop (𝓝 (P[X 0], Var[X 0; P])) :=
    hv.comp (tendsto_add_atTop_nat 1)
  have he' : Tendsto (fun n => empiricalVariance (fun i : Fin (n + 1) => X i ω))
      atTop (𝓝 (Var[X 0; P])) := he.comp (tendsto_add_atTop_nat 1)
  have hs' : Tendsto (fun n => empiricalVariance (fun i : Fin (n + 1) => (X i ω - P[X 0]) ^ 2))
      atTop (𝓝 (Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P])) := hs.comp (tendsto_add_atTop_nat 1)
  refine ⟨hmv, he', hs', ?_⟩
  have hrbase := bootstrap_sampleVariance_linear_remainder_probability
    (fun (n : ℕ) (i : Fin (n + 1)) => X i ω) (P[X 0]) (Var[X 0; P])
    (Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P])
  have hrM := hrbase hm
  have hrV := hrM he'
  have hrW := hrV hs'
  exact hrW

end LectureNotes
