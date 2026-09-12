import LectureNotes.Foundations

/-! L1 conditional expectation and best prediction; L5 Rao–Blackwell.
Equalities involving conditional expectations are almost-everywhere equalities.
Conditioning uses a sub-σ-algebra, so no density on a null fiber is introduced. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω}
variable (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
include hm

/-- L1 Theorem 5: law of iterated expectations. -/
theorem iterated_expectations (Y : Ω → ℝ) (_hY : Integrable Y P) :
    (∫ ω, P[Y | m] ω ∂P) = P[Y] := integral_condExp hm

/-- Conditioning preserves means, hence preserves unbiasedness. -/
theorem rao_blackwell_mean {T : Ω → ℝ} {θ : ℝ}
    (_hTi : Integrable T P) (hT : P[T] = θ) :
    P[P[T | m]] = θ := (integral_condExp hm).trans hT

/-- Squared-norm contraction, used for prediction and Rao–Blackwell. -/
theorem conditional_square_contraction {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    (∫ ω, (P[Y | m] ω) ^ 2 ∂P) ≤ ∫ ω, Y ω ^ 2 ∂P := by
  have hi : Integrable (fun ω => ‖Y ω‖ ^ (2 : ℝ)) P := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hY.integrable_sq
  simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using
    integral_norm_condExp_rpow_le (m := m) (by norm_num : (1 : ℝ) ≤ 2) hi

/-- L1 Theorem 6. The competing predictor is square integrable and measurable
with respect to the information being conditioned on. -/
theorem conditional_expectation_best_predictor {Y g : Ω → ℝ}
    (hY : MemLp Y 2 P) (hg : MemLp g 2 P) (hgm : StronglyMeasurable[m] g) :
    (∫ ω, (Y ω - P[Y | m] ω) ^ 2 ∂P) ≤
      ∫ ω, (Y ω - g ω) ^ 2 ∂P := by
  have hCE := hY.condExp (m := m) (by norm_num : (1 : ENNReal) ≤ 2)
  have hres : MemLp (fun ω => Y ω - P[Y | m] ω) 2 P := hY.sub hCE
  have hdiff : MemLp (fun ω => P[Y | m] ω - g ω) 2 P := hCE.sub hg
  have hdiffm : StronglyMeasurable[m] (fun ω => P[Y | m] ω - g ω) :=
    stronglyMeasurable_condExp.sub hgm
  have hc : P[(fun ω => Y ω - P[Y | m] ω) | m] =ᵐ[P] 0 := by
    have ht := condExp_sub (hY.integrable (by norm_num))
      (integrable_condExp (μ := P) (m := m) (f := Y)) m
    rw [condExp_of_stronglyMeasurable hm stronglyMeasurable_condExp
      integrable_condExp] at ht
    simpa only [Pi.sub_def, sub_self] using ht
  have hpull := condExp_mul_of_stronglyMeasurable_right hdiffm
    (hres.integrable_mul hdiff) (hres.integrable (by norm_num))
  simp only [Pi.mul_def] at hpull
  have hcross : (∫ ω, (Y ω - P[Y | m] ω) * (P[Y | m] ω - g ω) ∂P) = 0 := by
    rw [← integral_condExp hm]
    calc
      _ = ∫ ω, (0 : ℝ) ∂P := by
        apply integral_congr_ae
        filter_upwards [hpull, hc] with ω hω hhω
        simpa [hhω] using hω
      _ = 0 := by simp
  have hid : (∫ ω, (Y ω - g ω) ^ 2 ∂P) =
      (∫ ω, (Y ω - P[Y | m] ω) ^ 2 ∂P) +
      2 * (∫ ω, (Y ω - P[Y | m] ω) * (P[Y | m] ω - g ω) ∂P) +
      ∫ ω, (P[Y | m] ω - g ω) ^ 2 ∂P := by
    calc
      _ = ∫ ω, ((Y ω - P[Y | m] ω) ^ 2 +
          2 * ((Y ω - P[Y | m] ω) * (P[Y | m] ω - g ω))) +
          (P[Y | m] ω - g ω) ^ 2 ∂P := by
        congr 1; funext ω; ring
      _ = _ := by
        have hci : Integrable (fun ω =>
            2 * ((Y ω - P[Y | m] ω) * (P[Y | m] ω - g ω))) P :=
          (hres.integrable_mul hdiff).const_mul 2
        have hsi : Integrable (fun ω => (Y ω - P[Y | m] ω) ^ 2 +
            2 * ((Y ω - P[Y | m] ω) * (P[Y | m] ω - g ω))) P :=
          hres.integrable_sq.add hci
        rw [integral_add hsi hdiff.integrable_sq,
          integral_add hres.integrable_sq hci,
          integral_const_mul]
  rw [hcross] at hid
  have hnonneg : 0 ≤ ∫ ω, (P[Y | m] ω - g ω) ^ 2 ∂P :=
    integral_nonneg (fun _ => sq_nonneg _)
  linarith

/-- L5 Theorem 5: the risk part of Rao–Blackwell. For a statistical model,
sufficiency supplies a single conditional version that works for every θ. -/
theorem rao_blackwell_mse {T : Ω → ℝ} (hT : MemLp T 2 P) (θ : ℝ) :
    mse P (P[T | m]) θ ≤ mse P T θ := by
  have hr : MemLp (fun ω => T ω - θ) 2 P := hT.sub (memLp_const θ)
  have hc : P[(fun ω => T ω - θ) | m] =ᵐ[P] (fun ω => P[T | m] ω - θ) := by
    have ht := condExp_sub (hT.integrable (by norm_num)) (integrable_const θ) m
    rw [condExp_const hm θ] at ht
    simpa only [Pi.sub_def] using ht
  have h := conditional_square_contraction P hm hr
  have heq : (∫ ω, (P[(fun ω => T ω - θ) | m] ω) ^ 2 ∂P) =
      mse P (P[T | m]) θ := by
    apply integral_congr_ae
    filter_upwards [hc] with ω hω
    simp [hω]
  rw [heq] at h
  exact h
end LectureNotes
