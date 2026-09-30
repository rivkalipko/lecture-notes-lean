import LectureNotes.GaussianReflection
import LectureNotes.NormalMinimax

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- For any measurable multiplier invariant under reflection, replacing its
negative part by zero cannot increase normal-means risk. Tonelli makes this
valid even when one of the risks is infinite. -/
theorem normal_positive_part_risk_le {p : ℕ} (v : ℝ≥0) (hv : 0 < v)
    (c : (Fin p → ℝ) → ℝ) (hc : Measurable c) (heven : ∀ y, c (-y) = c y)
    (θ : Fin p → ℝ) :
    normalMeansSquaredRisk v (fun y i => max 0 (c y) * y i) θ ≤
      normalMeansSquaredRisk v (fun y i => c y * y i) θ := by
  let f := fun y : Fin p → ℝ => ENNReal.ofReal
    (normalDensityReal θ v y * ∑ i, (max 0 (c y) * y i - θ i) ^ 2)
  let g := fun y : Fin p → ℝ => ENNReal.ofReal
    (normalDensityReal θ v y * ∑ i, (c y * y i - θ i) ^ 2)
  have hf : Measurable f := by dsimp [f]; unfold normalDensityReal; fun_prop
  have hg : Measurable g := by dsimp [g]; unfold normalDensityReal; fun_prop
  have hpair (y : Fin p → ℝ) : f y + f (-y) ≤ g y + g (-y) := by
    have hd₁ := normalDensityReal_nonneg θ v y
    have hd₂ := normalDensityReal_nonneg θ v (-y)
    dsimp [f, g]
    rw [heven]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (normal_reflected_positive_part_loss θ y v hv (c y))
  have hi := lintegral_mono hpair (μ := (volume : Measure (Fin p → ℝ)))
  rw [lintegral_add_left hf, lintegral_add_left hg,
    lintegral_neg_eq_self, lintegral_neg_eq_self] at hi
  rw [normal_risk_density v hv.ne' _ (by fun_prop),
    normal_risk_density v hv.ne' _ (by fun_prop)]
  apply (ENNReal.mul_le_mul_iff_left (c := 2) (by norm_num) (by norm_num)).mp
  simpa only [mul_two, f, g] using hi

theorem positivePartJamesStein_measurable {p : ℕ} (v : ℝ) :
    Measurable (positivePartJamesStein (p := p) v) := by
  unfold positivePartJamesStein
  fun_prop

theorem positivePartJamesStein_risk_le {p : ℕ} (v : ℝ≥0) (hv : 0 < v) (θ : Fin p → ℝ) :
    normalMeansSquaredRisk v (positivePartJamesStein v) θ ≤
      normalMeansSquaredRisk v (jamesStein v) θ := by
  apply normal_positive_part_risk_le v hv _ (by fun_prop)
  intro y
  simp only [Pi.neg_apply, neg_sq]

theorem positivePartJamesStein_minimax {p : ℕ} (v : ℝ≥0) (hv : 0 < v) (hp : 3 ≤ p) :
    IsMinimax (fun (δ : NormalMeansRule p) => normalMeansSquaredRisk v δ.1)
      ⟨positivePartJamesStein v, positivePartJamesStein_measurable v⟩ := by
  apply minimax_of_pointwise_le (jamesStein_minimax v hv hp)
  exact positivePartJamesStein_risk_le v hv

/-- At the zero mean, truncation improves loss pointwise. -/
theorem positivePartJamesStein_zero_loss_le {p : ℕ} (v : ℝ) (y : Fin p → ℝ) :
    (∑ i, (positivePartJamesStein v y i) ^ 2) ≤ ∑ i, (jamesStein v y i) ^ 2 := by
  unfold positivePartJamesStein jamesStein
  by_cases h : 0 ≤ 1 - ((p : ℝ) - 2) * v / (∑ i, y i ^ 2)
  · simp [max_eq_right h]
  · rw [max_eq_left (le_of_not_ge h)]
    simp only [zero_mul, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- The improvement is strict on the nonempty open annulus `0 < ‖y‖² < (p-2)v`. -/
theorem positivePartJamesStein_zero_loss_lt {p : ℕ} (v : ℝ) (y : Fin p → ℝ)
    (hS : 0 < ∑ i, y i ^ 2) (ha : (∑ i, y i ^ 2) < ((p : ℝ) - 2) * v) :
    (∑ i, (positivePartJamesStein v y i) ^ 2) < ∑ i, (jamesStein v y i) ^ 2 := by
  have hc : 1 - ((p : ℝ) - 2) * v / (∑ i, y i ^ 2) < 0 := by
    have h : (1 : ℝ) < ((p : ℝ) - 2) * v / (∑ i, y i ^ 2) :=
      (lt_div_iff₀ hS).mpr (by simpa only [one_mul] using ha)
    linarith
  unfold positivePartJamesStein jamesStein
  rw [max_eq_left hc.le]
  simp only [zero_mul, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero, mul_pow,
    ← Finset.mul_sum]
  exact mul_pos (sq_pos_of_ne_zero hc.ne) hS

/-- Positive-part James–Stein has strictly lower risk at the zero mean. -/
theorem positivePartJamesStein_risk_strict_zero {p : ℕ} (v : ℝ≥0) (hv : 0 < v) (hp : 3 ≤ p) :
    normalMeansSquaredRisk v (positivePartJamesStein (p := p) v) 0 <
      normalMeansSquaredRisk v (jamesStein (p := p) v) 0 := by
  let P := Measure.pi (fun _ : Fin p => gaussianReal 0 v)
  let a : ℝ := ((p : ℝ) - 2) * v
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have ha : 0 < a := by
    have : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by omega)
    dsimp [a]
    positivity
  let s : Set (Fin p → ℝ) := {y | 0 < (∑ i, y i ^ 2) ∧ (∑ i, y i ^ 2) < a}
  have hsopen : IsOpen s := by
    change IsOpen ({y : Fin p → ℝ | 0 < ∑ i, y i ^ 2} ∩ {y | (∑ i, y i ^ 2) < a})
    exact (isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt (by fun_prop) continuous_const)
  have hsne : s.Nonempty := by
    refine ⟨fun _ => Real.sqrt (a / (2 * p)), ?_⟩
    have he : (∑ _i : Fin p, (Real.sqrt (a / (2 * p))) ^ 2) = a / 2 := by
      rw [Real.sq_sqrt (by positivity)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    change 0 < (∑ _i : Fin p, (Real.sqrt (a / (2 * p))) ^ 2) ∧
      (∑ _i : Fin p, (Real.sqrt (a / (2 * p))) ^ 2) < a
    rw [he]
    constructor <;> linarith
  have hac : (volume : Measure (Fin p → ℝ)) ≪ P := by
    dsimp [P]
    rw [normal_pi_withDensity (fun _ => 0) v hv.ne']
    apply withDensity_absolutelyContinuous'
      (show Measurable (fun y : Fin p → ℝ => ∏ i, gaussianPDF 0 v (y i)) by fun_prop).aemeasurable
    exact ae_of_all _ (fun y => Finset.prod_ne_zero_iff.mpr
      (fun i _ => (gaussianPDF_pos 0 hv.ne' (y i)).ne'))
  have hs : P s ≠ 0 := fun h => (hsopen.measure_pos volume hsne).ne' (hac h)
  have hfin : normalMeansSquaredRisk v (positivePartJamesStein (p := p) v) 0 ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (positivePartJamesStein_risk_le v hv 0)
    rw [normalMeansSquaredRisk_eq v _ 0 (jamesStein_loss_integrable 0 v hv hp)]
    exact ENNReal.ofReal_lt_top
  change (∫⁻ y, ENNReal.ofReal (∑ i, (positivePartJamesStein v y i - (0 : Fin p → ℝ) i) ^ 2) ∂P) <
    ∫⁻ y, ENNReal.ofReal (∑ i, (jamesStein v y i - (0 : Fin p → ℝ) i) ^ 2) ∂P
  simp only [Pi.zero_apply, sub_zero]
  apply lintegral_strict_mono_of_ae_le_of_ae_lt_on (by unfold jamesStein; fun_prop)
    (by simpa only [normalMeansSquaredRisk, risk, Pi.zero_apply, sub_zero] using hfin)
    (ae_of_all _ (fun y => ENNReal.ofReal_le_ofReal (positivePartJamesStein_zero_loss_le v y))) hs
  apply ae_of_all
  intro y hy
  have hlt := positivePartJamesStein_zero_loss_lt v y hy.1 hy.2
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hlt)).mpr hlt

theorem positivePartJamesStein_dominates {p : ℕ} (v : ℝ≥0) (hv : 0 < v) (hp : 3 ≤ p) :
    Dominates (normalMeansSquaredRisk (p := p) v) (positivePartJamesStein v) (jamesStein v) :=
  ⟨positivePartJamesStein_risk_le v hv, ⟨0, positivePartJamesStein_risk_strict_zero v hv hp⟩⟩

theorem jamesStein_inadmissible {p : ℕ} (v : ℝ≥0) (hv : 0 < v) (hp : 3 ≤ p) :
    ¬ Admissible (normalMeansSquaredRisk (p := p) v) (jamesStein v) := by
  intro h
  exact h ⟨positivePartJamesStein v, positivePartJamesStein_dominates v hv hp⟩

theorem jamesStein_inadmissible_measurable {p : ℕ} (v : ℝ≥0) (hv : 0 < v) (hp : 3 ≤ p) :
    ¬ Admissible (fun δ : NormalMeansRule p => normalMeansSquaredRisk v δ.1)
      ⟨jamesStein v, jamesStein_measurable v⟩ := by
  intro h
  exact h ⟨⟨positivePartJamesStein v, positivePartJamesStein_measurable v⟩,
    positivePartJamesStein_dominates v hv hp⟩

theorem positivePartJamesStein_worstRisk {p : ℕ} (v : ℝ≥0) (hv : 0 < v) (hp : 3 ≤ p) :
    worstRisk (normalMeansSquaredRisk v) (positivePartJamesStein (p := p) v) =
      ENNReal.ofReal (p * (v : ℝ)) :=
  normal_worstRisk_eq_of_le_identity v hv _ (positivePartJamesStein_measurable v)
    (fun θ => (positivePartJamesStein_risk_le v hv θ).trans
      (jamesStein_extended_risk_strict v hv hp θ).le)

end LectureNotes
