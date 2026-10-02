import LectureNotes.PoissonInformation
import LectureNotes.PoissonDeviance
import LectureNotes.BootstrapMeanIntervals
import LectureNotes.ConstrainedScoreTests

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

/-- The actual Poisson MLE on n+1 observed counts, viewed as a real number. -/
def poissonMLESequence {Ω : Type*} (X : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) : ℝ :=
  poissonSampleMLE (fun i : Fin (n + 1) => X i ω)

theorem poissonMLESequence_eq_sampleMean {Ω : Type*} (X : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) :
    poissonMLESequence X n ω = sampleMean (fun i : Fin (n + 1) => (X i ω : ℝ)) :=
  poissonSampleMLE_coe _

theorem poissonMLESequence_measurable {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℕ} (hm : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (poissonMLESequence X n) := by
  have he : poissonMLESequence X n = (fun ω => sampleMean (fun i : Fin (n + 1) => (X i ω : ℝ))) :=
    funext (fun ω => poissonMLESequence_eq_sampleMean X n ω)
  rw [he]
  unfold sampleMean
  fun_prop

section IID
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℕ} {r : ℝ≥0}

/-- Count-valued IID observations inherit the actual Poisson real moments. -/
theorem poisson_iid_real_conditions
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P) :
    MemLp (fun ω => (X 0 ω : ℝ)) 2 P ∧
    iIndepFun (fun i ω => (X i ω : ℝ)) P ∧
    (∀ i, IdentDistrib (fun ω => (X i ω : ℝ)) (fun ω => (X 0 ω : ℝ)) P P) ∧
    (∫ ω, (X 0 ω : ℝ) ∂P) = r ∧ Var[fun ω => (X 0 ω : ℝ); P] = r := by
  have hm : Measurable (fun k : ℕ => (k : ℝ)) := by fun_prop
  have hd : IdentDistrib (fun ω => (X 0 ω : ℝ)) (fun k : ℕ => (k : ℝ)) P
      (poissonMeasure r) := ((hX 0).identDistrib HasLaw.id).comp hm
  exact ⟨hd.memLp_iff.mpr (poisson_memLp_two r), hind.comp (fun _ k => (k : ℝ)) (fun _ => hm),
    fun i => ((hX i).identDistrib (hX 0)).comp hm,
    hd.integral_eq.trans (poisson_mean r), hd.variance_eq.trans (poisson_variance r)⟩

theorem poissonMLE_strong_consistency
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P) :
    ConvergesAlmostSurely P (poissonMLESequence X) (fun _ => (r : ℝ)) := by
  obtain ⟨h₂, hi, hid, hm, hv⟩ := poisson_iid_real_conditions hX hind
  unfold ConvergesAlmostSurely
  simpa only [poissonMLESequence_eq_sampleMean, hm] using
    iid_sampleMean_succ_ae (h₂.integrable (by norm_num)) hi hid

theorem poissonMLE_consistency (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P) :
    ConvergesInProbability P (poissonMLESequence X) (fun _ => (r : ℝ)) :=
  almost_sure_implies_probability (fun n => (poissonMLESequence_measurable hXm n).aemeasurable)
    (poissonMLE_strong_consistency hX hind)

/-- Positive population rate gives the normalized MLE CLT. Finite-sample
zero estimates remain in the actual statistic. -/
theorem poissonMLE_standardized_clt (hr : 0 < r)
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => Real.sqrt ((n : ℝ) + 1) / Real.sqrt r *
        (poissonMLESequence X n ω - r)) id := by
  obtain ⟨h₂, hi, hid, hm, hv⟩ := poisson_iid_real_conditions hX hind
  have hrR : (0 : ℝ) < r := hr
  simpa only [poissonMLESequence_eq_sampleMean, hm] using
    iid_sampleMean_standardized_clt h₂ hi hid (Real.sqrt r) (Real.sqrt_pos.mpr hrR)
      (by rw [Real.sq_sqrt hrR.le]; exact hv)

/-- Plug-in information is consistent at each strictly positive true rate.
The totalized value at a zero estimate does not affect this limit. -/
theorem poisson_plugin_information_consistency (hr : 0 < r)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P) :
    ConvergesInProbability P (fun n ω => 1 / poissonMLESequence X n ω)
      (fun _ => 1 / (r : ℝ)) := by
  apply continuous_mapping_probability_const _ (poissonMLE_consistency hXm hX hind)
  exact continuousAt_const.div continuousAt_id (show (r : ℝ) ≠ 0 from ne_of_gt hr)

/-- The score statistic has its chi-square limit from the actual Poisson CLT. -/
theorem poissonLM_limit (hr : 0 < r)
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => poissonLM ((n : ℝ) + 1) (poissonMLESequence X n ω) r)
      (fun z => z ^ 2) := by
  have h := (poissonMLE_standardized_clt hr hX hind).continuous_comp
    (g := fun z : ℝ => z ^ 2) (by fun_prop)
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl)) h
  intro n
  apply ae_of_all
  intro ω
  simp only [Function.comp_apply, poissonLM, div_pow, mul_pow,
    Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity), Real.sq_sqrt r.coe_nonneg]
  ring

/-- The Wald statistic uses estimated information. Its totalized value on
all-zero samples is retained, and the positive-rate asymptotic law is derived. -/
theorem poissonWald_limit (hr : 0 < r) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => poissonWald ((n : ℝ) + 1) (poissonMLESequence X n ω) r)
      (fun z => z ^ 2) := by
  have hrR : (r : ℝ) ≠ 0 := ne_of_gt hr
  have hc : ConvergesInProbability P
      (fun n ω => (r : ℝ) / poissonMLESequence X n ω) (fun _ => 1) := by
    simpa only [div_self hrR] using continuous_mapping_probability_const
      (g := fun m : ℝ => (r : ℝ) / m) (continuousAt_const.div continuousAt_id hrR)
      (poissonMLE_consistency hXm hX hind)
  have hh := slutsky_mul (poissonLM_limit hr hX hind) hc
    (fun n => (measurable_const.div (poissonMLESequence_measurable hXm n)).aemeasurable)
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun z => mul_one (z ^ 2))) hh
  intro n
  apply ae_of_all
  intro ω
  unfold poissonLM poissonWald
  field_simp

/-- The Poisson likelihood-ratio limit follows from the actual likelihood
identity and a proved removable quadratic coefficient, with no expansion premise. -/
theorem poissonLR_limit (hr : 0 < r) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (poissonMeasure r) P) (hind : iIndepFun X P) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => poissonLR ((n : ℝ) + 1) (poissonMLESequence X n ω) r)
      (fun z => z ^ 2) := by
  have hrR : (0 : ℝ) < r := hr
  have hc : ConvergesInProbability P
      (fun n ω => 2 * (r : ℝ) * poissonDevianceCoefficient r (poissonMLESequence X n ω))
      (fun _ => 1) := by
    have h := continuous_mapping_probability_const
      ((poissonDevianceCoefficient_continuousAt hrR).const_mul (2 * (r : ℝ)))
      (poissonMLE_consistency hXm hX hind)
    have he : 2 * (r : ℝ) * poissonDevianceCoefficient r r = 1 := by
      simp only [poissonDevianceCoefficient, Function.update_self]
      field_simp
    simpa only [he] using h
  have hm n : Measurable (fun ω => 2 * (r : ℝ) *
      poissonDevianceCoefficient r (poissonMLESequence X n ω)) :=
    ((poissonDevianceCoefficient_measurable r).comp
      (poissonMLESequence_measurable hXm n)).const_mul _
  have hh := slutsky_mul (poissonLM_limit hr hX hind) hc (fun n => (hm n).aemeasurable)
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun z => mul_one (z ^ 2))) hh
  intro n
  apply ae_of_all
  intro ω
  change poissonLM _ _ _ * _ = 2 * ((n : ℝ) + 1) * poissonDeviance r _
  rw [poissonDeviance_factorization hrR]
  unfold poissonLM
  field_simp
  <;> ring

end IID
end LectureNotes
