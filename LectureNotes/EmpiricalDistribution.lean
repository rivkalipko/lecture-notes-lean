import LectureNotes.Concentration
import LectureNotes.SamplingMoments
import LectureNotes.ProbabilityLaws
import LectureNotes.Convergence

/-! L4 pointwise empirical-CDF moments and strong consistency. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Finset
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def cdfIndicator (t x : ℝ) : ℝ := if x ≤ t then 1 else 0

theorem measurable_cdfIndicator (t : ℝ) : Measurable (cdfIndicator t) := by
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

theorem cdfIndicator_memLp {X : Ω → ℝ} (hX : Measurable X) (t : ℝ) :
    MemLp (fun ω => cdfIndicator t (X ω)) 2 P := by
  have h := MemLp.indicator
    (measurableSet_le hX (measurable_const : Measurable (fun _ : Ω => t)))
    (memLp_const (μ := P) (p := 2) (1 : ℝ))
  convert! h using 1

theorem cdfIndicator_mean {X : Ω → ℝ} (hX : Measurable X) (t : ℝ) :
    P[fun ω => cdfIndicator t (X ω)] = P.real {ω | X ω ≤ t} := by
  simpa only [indicator, mem_setOf_eq, Pi.one_apply, cdfIndicator] using
    (integral_indicator_one (μ := P) (measurableSet_le hX measurable_const))

theorem cdfIndicator_variance {X : Ω → ℝ} (hX : Measurable X) (t : ℝ) :
    Var[fun ω => cdfIndicator t (X ω); P] =
      P.real {ω | X ω ≤ t} * (1 - P.real {ω | X ω ≤ t}) := by
  rw [variance_eq_second_moment_sub_mean_sq P (cdfIndicator_memLp hX t),
    cdfIndicator_mean hX t]
  have hsq : (∫ ω, cdfIndicator t (X ω) ^ 2 ∂P) =
      P[fun ω => cdfIndicator t (X ω)] := by
    congr 1; funext ω; dsimp [cdfIndicator]; split <;> norm_num
  rw [hsq, cdfIndicator_mean hX t]
  ring

theorem empiricalCDF_eq_sampleMean {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    empiricalCDF x t = sampleMean (fun i => cdfIndicator t (x i)) := by
  simp [empiricalCDF, sampleMean, cdfIndicator, div_eq_mul_inv, mul_comm]

theorem empiricalCDF_unbiased {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) {t p : ℝ}
    (hF : ∀ i, P.real {ω | X i ω ≤ t} = p) :
    P[fun ω => empiricalCDF (fun i => X i ω) t] = p := by
  simp_rw [empiricalCDF_eq_sampleMean]
  exact sampleMean_expectation hn
    (fun i => (cdfIndicator_memLp (hX i) t).integrable (by norm_num))
    (fun i => (cdfIndicator_mean (hX i) t).trans (hF i))

theorem empiricalCDF_variance {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) {t p : ℝ}
    (hF : ∀ i, P.real {ω | X i ω ≤ t} = p) :
    Var[fun ω => empiricalCDF (fun i => X i ω) t; P] = p * (1 - p) / n := by
  simp_rw [empiricalCDF_eq_sampleMean]
  apply sampleMean_variance hn (fun i => cdfIndicator_memLp (hX i) t)
  · intro i j hij
    exact (hind.comp (fun _ => cdfIndicator t) (fun _ => measurable_cdfIndicator t)).indepFun hij
  · intro i
    rw [cdfIndicator_variance (hX i) t, hF i]

/-- L4 pointwise convergence: the strong law applied to bounded indicators. -/
theorem empiricalCDF_strong_consistency {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (t : ℝ) :
    ConvergesAlmostSurely P
      (fun n ω => (∑ i ∈ range n, cdfIndicator t (X i ω)) / n)
      (fun _ => P.real {ω | X 0 ω ≤ t}) := by
  have h := strong_law_of_large_numbers (X := fun i ω => cdfIndicator t (X i ω))
    ((cdfIndicator_memLp (hX 0) t).integrable (by norm_num))
    (fun _ _ hij =>
      (hind.comp (fun _ => cdfIndicator t) (fun _ => measurable_cdfIndicator t)).indepFun hij)
    (fun i => (hident i).comp (measurable_cdfIndicator t))
  simpa only [Function.comp_def, cdfIndicator_mean (hX 0) t] using h

theorem empiricalCDF_consistency {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (t : ℝ) :
    ConvergesInProbability P
      (fun n ω => empiricalCDF (fun i : Fin n => X i ω) t)
      (fun _ => P.real {ω | X 0 ω ≤ t}) := by
  have h := almost_sure_implies_probability
    (fun n => ((Finset.measurable_sum _ (fun i _ =>
      (measurable_cdfIndicator t).comp (hX i))).div_const (n : ℝ)).aemeasurable)
    (empiricalCDF_strong_consistency hX hind hident t)
  simpa only [empiricalCDF, ← Fin.sum_univ_eq_sum_range, Function.comp_def, cdfIndicator] using h

/-- The pointwise exponential bound. This does not assert a uniform DKW bound. -/
theorem empiricalCDF_pointwise_concentration {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    {t p : ℝ} (hF : ∀ i, P.real {ω | X i ω ≤ t} = p) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |empiricalCDF (fun i => X i ω) t - p|} ≤
      2 * Real.exp (-2 * n * ε ^ 2) := by
  simp_rw [empiricalCDF_eq_sampleMean]
  have h := hoeffding_sampleMean hn (X := fun i ω => cdfIndicator t (X i ω))
    (a := 0) (b := 1) (by norm_num)
    (fun i => (cdfIndicator_memLp (hX i) t).integrable (by norm_num))
    (fun i => ae_of_all _ (fun ω => by dsimp [cdfIndicator]; split <;> simp))
    (fun i => (cdfIndicator_mean (hX i) t).trans (hF i))
    (hind.comp (fun _ => cdfIndicator t) (fun _ => measurable_cdfIndicator t)) hε
  simpa using h
end LectureNotes
