import LectureNotes.MeasurableDeltaMethod
import LectureNotes.BernoulliBinomialMoments
import LectureNotes.BootstrapStudentizedIntervals
import LectureNotes.MonteCarlo
import LectureNotes.NormalHighestDensity

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- Odds on the interior parameter space. Lean's total division assigns zero
at one; the interval theorem allows this convention on vanishing boundary events. -/
def bernoulliOdds (p : ℝ) : ℝ := p / (1 - p)

def bernoulliOddsVariance (p : ℝ) : ℝ := p / (1 - p) ^ 3

def bernoulliProportion {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sampleMean (fun i : Fin (n + 1) => X i ω)

theorem bernoulliOdds_measurable : Measurable bernoulliOdds := by
  unfold bernoulliOdds
  fun_prop

theorem bernoulliOdds_hasDerivAt {p : ℝ} (hp : p ≠ 1) :
    HasDerivAt bernoulliOdds (1 / (1 - p) ^ 2) p := by
  have hd : HasDerivAt (fun x : ℝ => x / (1 - x))
      ((1 * (1 - p) - p * (0 - 1)) / (1 - p) ^ 2) p :=
    (hasDerivAt_id p).div ((hasDerivAt_const p 1).sub (hasDerivAt_id p))
      (sub_ne_zero.mpr (Ne.symm hp))
  unfold bernoulliOdds
  convert hd using 1
  ring

theorem bernoulliOddsVariance_pos {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 < bernoulliOddsVariance p := div_pos hp.1 (pow_pos (sub_pos.mpr hp.2) 3)

theorem bernoulliProportion_measurable {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (bernoulliProportion X n) := by
  unfold bernoulliProportion sampleMean
  fun_prop

section IID
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {p : Icc (0 : ℝ) 1}

theorem bernoulliProportion_strong_consistency
    (_hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (bernoulliRealLaw p) P) (hind : iIndepFun X P) :
    ConvergesAlmostSurely P (bernoulliProportion X) (fun _ => (p : ℝ)) := by
  have h₂ := ((hX 0).identDistrib HasLaw.id).memLp_iff.mpr (bernoulliRealLaw_memLp_two p)
  have hμ : P[X 0] = (p : ℝ) := (hX 0).integral_eq.trans (bernoulliRealLaw_mean p)
  have hh := monteCarlo_mean_strong_consistency (h₂.integrable (by norm_num)) hind
    (fun i => (hX i).identDistrib (hX 0))
  filter_upwards [hh] with ω hω
  simpa only [bernoulliProportion, hμ, Function.comp_apply] using! hω.comp (tendsto_add_atTop_nat 1)

theorem bernoulliProportion_consistent (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (bernoulliRealLaw p) P) (hind : iIndepFun X P) :
    ConvergesInProbability P (bernoulliProportion X) (fun _ => (p : ℝ)) :=
  almost_sure_implies_probability (fun n => (bernoulliProportion_measurable hXm n).aemeasurable)
    (bernoulliProportion_strong_consistency hXm hX hind)

theorem bernoulliProportion_clt (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hX : ∀ i, HasLaw (X i) (bernoulliRealLaw p) P) (hind : iIndepFun X P) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => Real.sqrt ((n : ℝ) + 1) * (bernoulliProportion X n ω - p))
      (fun z => Real.sqrt ((p : ℝ) * (1 - p)) * z) := by
  have h₂ := ((hX 0).identDistrib HasLaw.id).memLp_iff.mpr (bernoulliRealLaw_memLp_two p)
  have hμ : P[X 0] = (p : ℝ) := (hX 0).integral_eq.trans (bernoulliRealLaw_mean p)
  have hv : Var[X 0; P] = (p : ℝ) * (1 - p) :=
    (hX 0).variance_eq.trans (bernoulliRealLaw_variance p)
  have hvp : 0 < (p : ℝ) * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  have hs : 0 < Real.sqrt ((p : ℝ) * (1 - p)) := Real.sqrt_pos.2 hvp
  have hh := iid_sampleMean_standardized_clt h₂ hind (fun i => (hX i).identDistrib (hX 0))
    (Real.sqrt ((p : ℝ) * (1 - p))) hs (by rw [Real.sq_sqrt hvp.le]; exact hv)
  rw [hμ] at hh
  have hc := hh.continuous_comp (g := fun z : ℝ => Real.sqrt ((p : ℝ) * (1 - p)) * z) (by fun_prop)
  apply TendstoInDistribution.congr _ (ae_of_all _ fun _ => rfl) hc
  intro n
  apply ae_of_all
  intro ω
  dsimp only [bernoulliProportion, Function.comp_apply, id_eq]
  field_simp

/-- L11 Example 4: actual IID Bernoulli odds have the displayed delta-method
limit. The singular empirical boundary is allowed at every finite sample size. -/
theorem bernoulliOdds_clt (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (bernoulliRealLaw p) P) (hind : iIndepFun X P) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => Real.sqrt ((n : ℝ) + 1) *
        (bernoulliOdds (bernoulliProportion X n ω) - bernoulliOdds p))
      (fun z => (1 / (1 - (p : ℝ)) ^ 2) * (Real.sqrt ((p : ℝ) * (1 - p)) * z)) := by
  have hd := (bernoulliOdds_hasDerivAt (ne_of_lt hp.2)).hasFDerivAt
  have hh := normed_delta_method_of_measurable
    (fun n => (bernoulliProportion_measurable hXm n).aemeasurable)
    (bernoulliProportion_consistent hXm hX hind) (bernoulliProportion_clt hp hX hind)
    bernoulliOdds_measurable hd
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
    using! hh

theorem bernoulliOdds_limit_law (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1) :
    HasLaw (fun z : ℝ => (1 / (1 - (p : ℝ)) ^ 2) * (Real.sqrt ((p : ℝ) * (1 - p)) * z))
      (gaussianReal 0 (bernoulliOddsVariance p).toNNReal) (gaussianReal 0 1) := by
  have hp1 : 1 - (p : ℝ) ≠ 0 := (sub_pos.mpr hp.2).ne'
  have hv : 0 ≤ (p : ℝ) * (1 - p) := mul_nonneg hp.1.le (sub_nonneg.mpr hp.2.le)
  have he : ((1 / (1 - (p : ℝ)) ^ 2) * Real.sqrt ((p : ℝ) * (1 - p))) ^ 2 =
      bernoulliOddsVariance p := by
    rw [mul_pow, Real.sq_sqrt hv]
    unfold bernoulliOddsVariance
    field_simp
  have hh := gaussianReal_const_mul (show HasLaw id (gaussianReal 0 1) (gaussianReal 0 1) from HasLaw.id)
    ((1 / (1 - (p : ℝ)) ^ 2) * Real.sqrt ((p : ℝ) * (1 - p)))
  convert! hh using 1
  · funext z
    simp only [id_eq]
    ring
  · simp only [mul_zero, mul_one]
    congr 1
    apply NNReal.coe_injective
    simp only [NNReal.coe_mk, Real.coe_toNNReal _ (bernoulliOddsVariance_pos hp).le, he]

theorem bernoulliOdds_plugin_variance_consistent (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (bernoulliRealLaw p) P) (hind : iIndepFun X P) :
    ConvergesInProbability P (fun n ω => bernoulliOddsVariance (bernoulliProportion X n ω))
      (fun _ => bernoulliOddsVariance p) := by
  apply continuous_mapping_probability_const _ (bernoulliProportion_consistent hXm hX hind)
  unfold bernoulliOddsVariance
  exact continuousAt_id.div ((continuousAt_const.sub continuousAt_id).pow 3)
    (pow_ne_zero _ (sub_pos.mpr hp.2).ne')

/-- The displayed plug-in odds interval has pointwise asymptotic coverage.
Finite samples with empirical proportion zero or one are retained with total
division; their probability vanishes for every fixed interior parameter. -/
theorem bernoulliOdds_interval_coverage (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (bernoulliRealLaw p) P) (hind : iIndepFun X P)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => P.real {ω | bernoulliOdds p ∈ Icc
      (bernoulliOdds (bernoulliProportion X n ω) - distributionQuantile (gaussianReal 0 1) b *
        Real.sqrt (bernoulliOddsVariance (bernoulliProportion X n ω) / ((n : ℝ) + 1)))
      (bernoulliOdds (bernoulliProportion X n ω) - distributionQuantile (gaussianReal 0 1) a *
        Real.sqrt (bernoulliOddsVariance (bernoulliProportion X n ω) / ((n : ℝ) + 1)))})
      atTop (𝓝 (b - a)) := by
  let S n ω := Real.sqrt (bernoulliOddsVariance (bernoulliProportion X n ω))
  let σ := Real.sqrt (bernoulliOddsVariance p)
  have hv : 0 < bernoulliOddsVariance p := bernoulliOddsVariance_pos hp
  have hσ : 0 < σ := Real.sqrt_pos.2 hv
  have hSm n : Measurable (S n) := by
    dsimp [S, bernoulliOddsVariance]
    exact Real.continuous_sqrt.measurable.comp
      ((bernoulliProportion_measurable hXm n).div
        ((measurable_const.sub (bernoulliProportion_measurable hXm n)).pow_const 3))
  have hS : ConvergesInProbability P S (fun _ => σ) :=
    continuous_mapping_probability_const Real.continuous_sqrt.continuousAt
      (bernoulliOdds_plugin_variance_consistent hp hXm hX hind)
  have hT := slutsky_div hσ.ne' (bernoulliOdds_clt hp hXm hX hind) hS
    (fun n => (hSm n).aemeasurable)
  have hvNN : 0 < (bernoulliOddsVariance p).toNNReal := Real.toNNReal_pos.mpr hv
  have hZ := normal_standardize hvNN (bernoulliOdds_limit_law hp)
  simp only [sub_zero, Real.coe_toNNReal _ hv.le] at hZ
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hcov := asymptotic_quantile_coverage hT hZ ha hb hab
  have hbad : Tendsto (fun n => P.real {ω | S n ω ≤ 0}) atTop (𝓝 0) := by
    have hh := tendstoInMeasure_iff_measureReal_norm.mp hS σ hσ
    apply squeeze_zero (fun _ => measureReal_nonneg) _ hh
    intro n
    refine measureReal_mono (μ := P) ?_ (measure_ne_top P _)
    intro ω hω
    change σ ≤ ‖S n ω - σ‖
    rw [Real.norm_eq_abs]
    have hh := neg_le_abs (S n ω - σ)
    change S n ω ≤ 0 at hω
    linarith
  apply probability_limit_of_agree_off_rare_event P _ _ _ hcov hbad
  intro n ω hω
  have hs : 0 < S n ω := lt_of_not_ge hω
  have hvr : 0 < bernoulliOddsVariance (bernoulliProportion X n ω) := Real.sqrt_pos.mp hs
  have hn : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hr : 0 < Real.sqrt (bernoulliOddsVariance (bernoulliProportion X n ω) / ((n : ℝ) + 1)) :=
    Real.sqrt_pos.2 (div_pos hvr (by positivity))
  have he : Real.sqrt (bernoulliOddsVariance (bernoulliProportion X n ω) / ((n : ℝ) + 1)) =
      S n ω / Real.sqrt ((n : ℝ) + 1) := Real.sqrt_div hvr.le _
  have hid : (bernoulliOdds (bernoulliProportion X n ω) - bernoulliOdds p) /
      Real.sqrt (bernoulliOddsVariance (bernoulliProportion X n ω) / ((n : ℝ) + 1)) =
      Real.sqrt ((n : ℝ) + 1) * (bernoulliOdds (bernoulliProportion X n ω) - bernoulliOdds p) /
        S n ω := by
    rw [he, div_div_eq_mul_div]
    ring
  change bernoulliOdds p ∈ Icc _ _ ↔ _ ∈ Icc _ _
  rw [← hid]
  exact (location_pivot_inversion _ _ _ _ _ hr).symm

theorem bernoulliOdds_equalTailed_interval_coverage (hp : (p : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (bernoulliRealLaw p) P) (hind : iIndepFun X P)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω | bernoulliOdds p ∈ Icc
      (bernoulliOdds (bernoulliProportion X n ω) + distributionQuantile (gaussianReal 0 1) (α / 2) *
        Real.sqrt (bernoulliOddsVariance (bernoulliProportion X n ω) / ((n : ℝ) + 1)))
      (bernoulliOdds (bernoulliProportion X n ω) + distributionQuantile (gaussianReal 0 1) (1 - α / 2) *
        Real.sqrt (bernoulliOddsVariance (bernoulliProportion X n ω) / ((n : ℝ) + 1)))})
      atTop (𝓝 (1 - α)) := by
  have ha : α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hb : 1 - α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hsym : distributionQuantile (gaussianReal 0 1) (α / 2) =
      -distributionQuantile (gaussianReal 0 1) (1 - α / 2) := by
    have hh := standardNormal_quantile_symmetry ha
    linarith
  have hh := bernoulliOdds_interval_coverage hp hXm hX hind ha hb (by linarith [hα.2])
  have he : 1 - α / 2 - α / 2 = 1 - α := by ring
  rw [he] at hh
  simpa only [hsym, neg_mul, sub_neg_eq_add, sub_eq_add_neg, neg_neg] using hh

end IID
end LectureNotes
