import LectureNotes.RegularizedStein
import LectureNotes.NormalSteinRisk
set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem integrable_of_nonnegative_limit_bounded {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : ℕ → Ω → ℝ} {f : Ω → ℝ} {C : ℝ}
    (hU : ∀ n, Integrable (U n) P) (hU0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ U n ω)
    (hf : AEStronglyMeasurable f P) (hf0 : ∀ᵐ ω ∂P, 0 ≤ f ω)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => U n ω) atTop (𝓝 (f ω)))
    (hbound : ∀ n, (∫ ω, U n ω ∂P) ≤ C) : Integrable f P := by
  have hfat : (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) ≤
      liminf (fun n => ∫⁻ ω, ENNReal.ofReal (U n ω) ∂P) atTop := by
    have he : (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) =
        ∫⁻ ω, liminf (fun n => ENNReal.ofReal (U n ω)) atTop ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hlim] with ω hω
      exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hω).liminf_eq.symm
    rw [he]
    exact lintegral_liminf_le' (fun n => (hU n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hb : liminf (fun n => ∫⁻ ω, ENNReal.ofReal (U n ω) ∂P) atTop ≤ ENNReal.ofReal C := by
    apply liminf_le_of_frequently_le'
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hU n) (hU0 n)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  apply (lintegral_ofReal_ne_top_iff_integrable hf hf0).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hfat.trans hb)

/-- The regularized inverse-radius expression is bounded for each positive ε. -/
theorem integrable_regularized_inverse {p : ℕ} (P : Measure (Fin p → ℝ))
    [IsProbabilityMeasure P] {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun y => normalSquareNorm y / (normalSquareNorm y + ε) ^ 2) P ∧
      Integrable (fun y => 1 / (normalSquareNorm y + ε) ^ 2) P := by
  have hsm : Measurable (normalSquareNorm (p := p)) := by unfold normalSquareNorm; fun_prop
  constructor
  · apply (integrable_const (1 / ε : ℝ)).mono' (hsm.div ((hsm.add_const ε).pow_const 2)).aestronglyMeasurable
    apply ae_of_all
    intro y
    have hS := normalSquareNorm_nonneg y
    have hden : 0 < normalSquareNorm y + ε := by positivity
    simp only [Real.norm_eq_abs, Pi.div_apply, Pi.pow_apply]
    rw [abs_of_nonneg (div_nonneg hS (sq_nonneg (normalSquareNorm y + ε)))]
    calc
      normalSquareNorm y / (normalSquareNorm y + ε) ^ 2 ≤
          (normalSquareNorm y + ε) / (normalSquareNorm y + ε) ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = 1 / (normalSquareNorm y + ε) := by field_simp
      _ ≤ 1 / ε := one_div_le_one_div_of_le hε (by linarith)
  · apply (integrable_const (1 / ε ^ 2 : ℝ)).mono' (measurable_const.div ((hsm.add_const ε).pow_const 2)).aestronglyMeasurable
    apply ae_of_all
    intro y
    have hS := normalSquareNorm_nonneg y
    simp only [Real.norm_eq_abs, Pi.div_apply, Pi.pow_apply]
    rw [abs_of_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg (normalSquareNorm y + ε)))]
    exact one_div_le_one_div_of_le (sq_pos_of_pos hε) (by nlinarith [sq_nonneg (normalSquareNorm y)])

theorem regularized_stein_risk {n : ℕ} (θ : Fin (n + 1) → ℝ)
    (v : ℝ≥0) (hv : v ≠ 0) (a ε : ℝ) (hε : 0 < ε) :
    (∫ y, ∑ i, (y i + regularizedSteinCorrection a ε y i - θ i) ^ 2
      ∂Measure.pi (fun j => gaussianReal (θ j) v)) =
    (n + 1 : ℕ) * (v : ℝ) +
      (a ^ 2 - 2 * a * v * (((n + 1 : ℕ) : ℝ) - 2)) *
        (∫ y, normalSquareNorm y / (normalSquareNorm y + ε) ^ 2
          ∂Measure.pi (fun j => gaussianReal (θ j) v)) -
      2 * a * (n + 1 : ℕ) * v * ε *
        (∫ y, 1 / (normalSquareNorm y + ε) ^ 2
          ∂Measure.pi (fun j => gaussianReal (θ j) v)) := by
  rw [normal_stein_risk θ v hv (regularizedSteinCorrection a ε) (regularizedSteinDerivative a ε)
    (regularizedSteinCorrection_measurable a ε) (regularizedSteinDerivative_measurable a ε)
    (regularizedSteinCorrection_hasDerivAt a ε hε)
    (regularizedSteinCorrection_bound a ε hε) (regularizedSteinDerivative_bound a ε hε)]
  simp_rw [regularizedStein_risk_integrand]
  obtain ⟨hi, hj⟩ := integrable_regularized_inverse
    (Measure.pi (fun j => gaussianReal (θ j) v)) hε
  have he (y : Fin (n + 1) → ℝ) : (a ^ 2 - 2 * a * v * (((n + 1 : ℕ) : ℝ) - 2)) * normalSquareNorm y /
        (normalSquareNorm y + ε) ^ 2 - 2 * a * (n + 1 : ℕ) * v * ε / (normalSquareNorm y + ε) ^ 2 =
      (a ^ 2 - 2 * a * v * (((n + 1 : ℕ) : ℝ) - 2)) *
        (normalSquareNorm y / (normalSquareNorm y + ε) ^ 2) -
      (2 * a * (n + 1 : ℕ) * v * ε) * (1 / (normalSquareNorm y + ε) ^ 2) := by ring
  simp_rw [he]
  rw [integral_sub (hi.const_mul _) (hj.const_mul _), integral_const_mul, integral_const_mul]
  ring


/-- In dimension at least three, the regularized risk bound proves inverse
squared-radius integrability by Fatou. No polar-coordinate assumption is used. -/
theorem normal_inverse_square_integrable {n : ℕ} (θ : Fin (n + 1) → ℝ)
    (v : ℝ≥0) (hv : 0 < v) (hn : 3 ≤ n + 1) :
    Integrable (fun y => 1 / normalSquareNorm y)
      (Measure.pi (fun j => gaussianReal (θ j) v)) := by
  let P := Measure.pi (fun j => gaussianReal (θ j) v)
  let a : ℝ := (((n + 1 : ℕ) : ℝ) - 2) * v
  have hp : (2 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast hn
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have ha : 0 < a := mul_pos (sub_pos.mpr hp) hv'
  have hb {ε : ℝ} (hε : 0 < ε) :
      (∫ y, normalSquareNorm y / (normalSquareNorm y + ε) ^ 2 ∂P) ≤
        ((n + 1 : ℕ) * (v : ℝ)) / a ^ 2 := by
    have hr := regularized_stein_risk θ v hv.ne' a ε hε
    have hcoef : a ^ 2 - 2 * a * v * (((n + 1 : ℕ) : ℝ) - 2) = -a ^ 2 := by
      dsimp [a]
      ring
    rw [hcoef] at hr
    have hnonneg : 0 ≤ ∫ y, ∑ i, (y i + regularizedSteinCorrection a ε y i - θ i) ^ 2 ∂P :=
      integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hlast : 0 ≤ 2 * a * (n + 1 : ℕ) * v * ε *
        (∫ y, 1 / (normalSquareNorm y + ε) ^ 2 ∂P) := by
      have hi : 0 ≤ ∫ y, 1 / (normalSquareNorm y + ε) ^ 2 ∂P :=
        integral_nonneg (fun _ => by positivity)
      positivity
    rw [le_div_iff₀ (sq_pos_of_pos ha)]
    change _ = _ at hr
    change 0 ≤ _ at hnonneg
    dsimp [P] at hnonneg hlast ⊢
    nlinarith
  let eps (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have heps k : 0 < eps k := by dsimp [eps]; positivity
  have helim : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply integrable_of_nonnegative_limit_bounded
    (U := fun k y => normalSquareNorm y / (normalSquareNorm y + eps k) ^ 2)
    (C := ((n + 1 : ℕ) * (v : ℝ)) / a ^ 2)
    (fun k => (integrable_regularized_inverse P (heps k)).1)
    (fun k => ae_of_all _ (fun y => div_nonneg (normalSquareNorm_nonneg y) (sq_nonneg _)))
    ((show Measurable (fun y : Fin (n + 1) → ℝ => 1 / normalSquareNorm y) from by
      unfold normalSquareNorm
      fun_prop).aestronglyMeasurable)
    (ae_of_all _ (fun y => div_nonneg (by norm_num) (normalSquareNorm_nonneg y)))
  · apply ae_of_all
    intro y
    by_cases hz : normalSquareNorm y = 0
    · simpa [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · have hh : normalSquareNorm y / (normalSquareNorm y) ^ 2 = 1 / normalSquareNorm y := by field_simp
      rw [← hh]
      exact tendsto_const_nhds.div (by simpa only [add_zero] using
        (tendsto_const_nhds.add helim).pow 2) (pow_ne_zero 2 hz)
  · intro k
    exact hb (heps k)

end LectureNotes
