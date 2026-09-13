import LectureNotes.LargeSample

/-! L3 relationships between stochastic convergence and continuous mapping. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

theorem almost_sure_implies_probability {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEMeasurable (X n) P) (h : ConvergesAlmostSurely P X Y) :
    ConvergesInProbability P X Y :=
  tendstoInMeasure_of_tendsto_ae (fun n => (hX n).aestronglyMeasurable) h

theorem probability_implies_distribution {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEMeasurable (X n) P) (h : ConvergesInProbability P X Y) :
    ConvergesInDistribution P P X Y :=
  TendstoInMeasure.tendstoInDistribution h hX

theorem continuous_mapping_almost_sure {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    {g : ℝ → ℝ} (hg : Continuous g) (h : ConvergesAlmostSurely P X Y) :
    ConvergesAlmostSurely P (fun n ω => g (X n ω)) (fun ω => g (Y ω)) := by
  filter_upwards [h] with ω hω
  exact (hg.tendsto (Y ω)).comp hω

theorem continuous_mapping_distribution {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    {g : ℝ → ℝ} (hg : Continuous g) (h : ConvergesInDistribution P Q X Y) :
    ConvergesInDistribution P Q (fun n ω => g (X n ω)) (fun ω => g (Y ω)) :=
  TendstoInDistribution.continuous_comp hg h

theorem slutsky_add {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {c : ℝ}
    (hX : ConvergesInDistribution P Q X Z)
    (hY : ConvergesInProbability P Y (fun _ => c))
    (hYm : ∀ n, AEMeasurable (Y n) P) :
    ConvergesInDistribution P Q (fun n ω => X n ω + Y n ω) (fun ω => Z ω + c) :=
  TendstoInDistribution.add_of_tendstoInMeasure_const hX hY hYm

theorem slutsky_mul {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {c : ℝ}
    (hX : ConvergesInDistribution P Q X Z)
    (hY : ConvergesInProbability P Y (fun _ => c))
    (hYm : ∀ n, AEMeasurable (Y n) P) :
    ConvergesInDistribution P Q (fun n ω => X n ω * Y n ω) (fun ω => Z ω * c) :=
  TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun z : ℝ × ℝ => z.1 * z.2) (by fun_prop) hX hY hYm

theorem mean_implies_probability {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (h : ConvergesInMean P X Y) : ConvergesInProbability P X Y := by
  rw [ConvergesInProbability, tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hb (n : ℕ) : P.real {ω | ε ≤ ‖X n ω - Y ω‖} ≤
      (∫ ω, |X n ω - Y ω| ∂P) / ε := by
    have hmark := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall (fun ω => abs_nonneg (X n ω - Y ω)))
      (h.1 n).abs ε
    simpa only [Real.norm_eq_abs] using
      (le_div_iff₀ hε).2 (show P.real {ω | ε ≤ |X n ω - Y ω|} * ε ≤
        (∫ ω, |X n ω - Y ω| ∂P) by linarith)
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
    (by simpa using h.2.div_const ε)

/-- L3 Theorem 7(1), using nonnegativity of the variance of the absolute error. -/
theorem mean_square_implies_mean {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (h : ConvergesInMeanSquare P X Y) : ConvergesInMean P X Y := by
  refine ⟨fun n => (h.1 n).integrable (by norm_num), ?_⟩
  have hb (n) : (∫ ω, |X n ω - Y ω| ∂P) ^ 2 ≤
      ∫ ω, |X n ω - Y ω| ^ 2 ∂P := by
    have hv := variance_eq_sub (h.1 n).abs
    have hn := variance_nonneg (fun ω => |X n ω - Y ω|) P
    change Var[(fun ω => |X n ω - Y ω|); P] =
      (∫ ω, |X n ω - Y ω| ^ 2 ∂P) - (∫ ω, |X n ω - Y ω| ∂P) ^ 2 at hv
    linarith
  have hs := squeeze_zero (fun n => sq_nonneg (∫ ω, |X n ω - Y ω| ∂P)) hb h.2
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _)), Real.sqrt_zero] using ht

theorem mean_square_implies_probability {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (h : ConvergesInMeanSquare P X Y) : ConvergesInProbability P X Y :=
  mean_implies_probability (mean_square_implies_mean h)

theorem continuous_mapping_probability {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    {g : ℝ → ℝ} (hg : Continuous g) (hXm : ∀ n, AEMeasurable (X n) P)
    (h : ConvergesInProbability P X Y) :
    ConvergesInProbability P (fun n ω => g (X n ω)) (fun ω => g (Y ω)) := by
  rw [ConvergesInProbability, tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, _, hms⟩ := (TendstoInMeasure.comp h hns).exists_seq_tendsto_ae
  have hae : ConvergesAlmostSurely P (fun n ω => g (X (ns (ms n)) ω))
      (fun ω => g (Y ω)) :=
    continuous_mapping_almost_sure hg hms
  have hp := almost_sure_implies_probability
    (fun n => hg.measurable.comp_aemeasurable (hXm _)) hae
  exact ⟨ms, tendstoInMeasure_iff_measureReal_norm.mp hp ε hε⟩

/-- Mapping at a constant limit only needs continuity at that constant. -/
theorem continuous_mapping_probability_const {X : ℕ → Ω → ℝ} {c : ℝ}
    {g : ℝ → ℝ} (hg : ContinuousAt g c)
    (h : ConvergesInProbability P X (fun _ => c)) :
    ConvergesInProbability P (fun n ω => g (X n ω)) (fun _ => g c) := by
  rw [ConvergesInProbability, tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Metric.continuousAt_iff.mp hg ε hε
  have hb (n) : P.real {ω | ε ≤ dist (g (X n ω)) (g c)} ≤
      P.real {ω | δ ≤ dist (X n ω) c} := by
    refine measureReal_mono ?_ (measure_ne_top P _)
    intro ω hω
    by_contra hsmall
    exact (not_lt_of_ge hω) (hbound (lt_of_not_ge hsmall))
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
    (tendstoInMeasure_iff_measureReal_dist.mp h δ hδ)

theorem slutsky_div {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {c : ℝ}
    (hc : c ≠ 0) (hX : ConvergesInDistribution P Q X Z)
    (hY : ConvergesInProbability P Y (fun _ => c))
    (hYm : ∀ n, AEMeasurable (Y n) P) :
    ConvergesInDistribution P Q (fun n ω => X n ω / Y n ω) (fun ω => Z ω / c) := by
  have hi := continuous_mapping_probability_const (continuousAt_inv₀ hc) hY
  simpa only [div_eq_mul_inv] using slutsky_mul hX hi (fun n => (hYm n).inv)

/-- L3 Definition 5, with absolute values on deterministic scale sequences.
The source indexes from one; use `n + 1` for power scales in Lean's zero-based
sequences so that every scale is nonzero. -/
def StochasticLittleO (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) : Prop :=
  (∀ n, a n ≠ 0) ∧ ConvergesInProbability P (fun n ω => X n ω / a n) (fun _ => 0)
def StochasticBigO (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) : Prop :=
  (∀ n, a n ≠ 0) ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n, P.real {ω | C * |a n| < |X n ω|} < ε

end LectureNotes
