import LectureNotes.LindebergAnalytic

set_option autoImplicit false

/-! Truncated-moment estimates underlying the non-identical CLT. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def truncSecondMoment (P : Measure Ω) (X : Ω → ℝ) (δ : ℝ) : ℝ :=
  ∫ ω, if δ < |X ω| then X ω ^ 2 else 0 ∂P

theorem truncSecondMoment_nonneg (X : Ω → ℝ) (δ : ℝ) :
    0 ≤ truncSecondMoment P X δ := by
  apply integral_nonneg
  intro ω
  dsimp only
  split_ifs <;> positivity

theorem integrable_truncSecondMoment {X : Ω → ℝ} (hXm : Measurable X)
    (hX : MemLp X 2 P) (δ : ℝ) :
    Integrable (fun ω => if δ < |X ω| then X ω ^ 2 else 0) P := by
  exact hX.integrable_sq.indicator (measurableSet_lt measurable_const hXm.abs)

theorem secondMoment_le_truncation {X : Ω → ℝ} (hXm : Measurable X)
    (hX : MemLp X 2 P) {δ : ℝ} (hδ : 0 < δ) :
    (∫ ω, X ω ^ 2 ∂P) ≤ δ ^ 2 + truncSecondMoment P X δ := by
  calc
    _ ≤ ∫ ω, δ ^ 2 + (if δ < |X ω| then X ω ^ 2 else 0) ∂P := by
      apply integral_mono hX.integrable_sq
        ((integrable_const _).add (integrable_truncSecondMoment hXm hX δ))
      intro ω
      dsimp only [Pi.add_apply]
      split_ifs with hx
      · nlinarith [sq_nonneg δ]
      · have hab := le_of_not_gt hx
        have hs : |X ω| ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hab 2
        simpa only [sq_abs, add_zero] using hs
    _ = _ := by rw [integral_add (integrable_const _) (integrable_truncSecondMoment hXm hX δ)]; simp [truncSecondMoment]

theorem integrable_characteristicRemainder {X : Ω → ℝ} (hXm : Measurable X)
    (hX : MemLp X 2 P) (t : ℝ) :
    Integrable (fun ω => characteristicRemainder (t * X ω)) P := by
  refine ((hX.const_mul t).integrable_sq.const_mul 2).mono' ?_ ?_
  · exact (show Measurable (fun ω => characteristicRemainder (t * X ω)) by
      unfold characteristicRemainder
      fun_prop).aestronglyMeasurable
  · exact .of_forall (fun ω => characteristicRemainder_quadratic_bound (t * X ω))

theorem integral_characteristicRemainder_bound {X : Ω → ℝ} (hXm : Measurable X)
    (hX : MemLp X 2 P) (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ‖∫ ω, characteristicRemainder (t * X ω) ∂P‖ ≤
      |t| ^ 3 * δ * (∫ ω, X ω ^ 2 ∂P) + 2 * t ^ 2 * truncSecondMoment P X δ := by
  calc
    _ ≤ ∫ ω, ‖characteristicRemainder (t * X ω)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |t| ^ 3 * δ * X ω ^ 2 +
        2 * t ^ 2 * (if δ < |X ω| then X ω ^ 2 else 0) ∂P := by
      apply integral_mono (integrable_characteristicRemainder hXm hX t).norm
        ((hX.integrable_sq.const_mul _).add ((integrable_truncSecondMoment hXm hX δ).const_mul _))
      exact fun ω => characteristicRemainder_truncation_bound t (X ω) hδ
    _ = _ := by
      rw [integral_add (hX.integrable_sq.const_mul _)
        ((integrable_truncSecondMoment hXm hX δ).const_mul _), integral_const_mul,
        integral_const_mul]
      rfl

theorem integral_characteristicRemainder {X : Ω → ℝ} (hXm : Measurable X)
    (hX : MemLp X 2 P) (hmean : (∫ ω, X ω ∂P) = 0) (t : ℝ) :
    (∫ ω, characteristicRemainder (t * X ω) ∂P) =
      charFun (P.map X) t - 1 + (t : ℂ) ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2 := by
  have hint : Integrable (fun ω => Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I)) P := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact .of_forall (fun ω => by rw [Complex.norm_exp_ofReal_mul_I])
  have hlin : Integrable (fun ω => ((t * X ω : ℝ) : ℂ) * Complex.I) P :=
    ((hX.integrable (by norm_num)).const_mul t).ofReal.mul_const _
  have hsq : Integrable (fun ω => ((t * X ω : ℝ) : ℂ) ^ 2 / 2) P := by
    convert! ((hX.const_mul t).integrable_sq.ofReal.div_const (2 : ℂ)) using 1
    funext ω
    simp
  have hc : charFun (P.map X) t =
      ∫ ω, Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) ∂P := by
    rw [charFun_apply_real, integral_map hXm.aemeasurable (by fun_prop)]
    congr 1
    funext ω
    push_cast
    rfl
  have hfirst : Integrable (fun ω => Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) - 1) P := by
    simpa only [Pi.sub_apply] using! hint.sub (integrable_const (1 : ℂ))
  have hsub : Integrable (fun ω =>
      Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) - 1 - ((t * X ω : ℝ) : ℂ) * Complex.I) P := by
    simpa only [Pi.sub_apply] using! hfirst.sub hlin
  unfold characteristicRemainder
  rw [integral_add hsub hsq, integral_sub hfirst hlin, integral_sub hint (integrable_const (1 : ℂ))]
  rw [← hc]
  simp only [integral_const, probReal_univ, one_smul]
  have hzero : (∫ ω, ((t * X ω : ℝ) : ℂ) * Complex.I ∂P) = 0 := by
    rw [integral_mul_const, integral_complex_ofReal, integral_const_mul, hmean]
    simp
  rw [hzero, sub_zero, integral_div]
  have he : (∫ ω, ((t * X ω : ℝ) : ℂ) ^ 2 ∂P) =
      (t : ℂ) ^ 2 * (∫ ω, X ω ^ 2 ∂P) := by
    simp_rw [← Complex.ofReal_pow, mul_pow]
    rw [integral_complex_ofReal, integral_const_mul]
    push_cast
    rfl
  rw [he]

theorem charFun_gaussian_error_bound {X : Ω → ℝ} (hXm : Measurable X)
    (hX : MemLp X 2 P) (hmean : (∫ ω, X ω ∂P) = 0) (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ‖charFun (P.map X) t - Complex.exp (-(t : ℂ) ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2)‖ ≤
      |t| ^ 3 * δ * (∫ ω, X ω ^ 2 ∂P) + 2 * t ^ 2 * truncSecondMoment P X δ +
        t ^ 4 * (∫ ω, X ω ^ 2 ∂P) ^ 2 := by
  let v := ∫ ω, X ω ^ 2 ∂P
  have hv : 0 ≤ v := integral_nonneg (fun ω => sq_nonneg _)
  let a := t ^ 2 * v / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have happrox : ‖(1 - (a : ℂ)) - Complex.exp (-(a : ℂ))‖ ≤ a ^ 2 := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ = |-(Real.exp (-a) - 1 + a)| := by congr 1; ring
      _ = |Real.exp (-a) - 1 + a| := abs_neg _
      _ ≤ _ := exp_neg_first_remainder_bound ha
  have herr := integral_characteristicRemainder_bound hXm hX t hδ
  rw [integral_characteristicRemainder hXm hX hmean t] at herr
  have he : (t : ℂ) ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2 = (a : ℂ) := by
    dsimp [a, v]
    push_cast
    rfl
  rw [he] at herr
  have hexp : -(t : ℂ) ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2 = -(a : ℂ) := by rw [← he]; ring
  rw [hexp]
  have h := norm_add_le (charFun (P.map X) t - (1 - (a : ℂ)))
    ((1 - (a : ℂ)) - Complex.exp (-(a : ℂ)))
  rw [sub_add_sub_cancel] at h
  have herr' : ‖charFun (P.map X) t - (1 - (a : ℂ))‖ ≤
      |t| ^ 3 * δ * v + 2 * t ^ 2 * truncSecondMoment P X δ := by
    rw [show charFun (P.map X) t - (1 - (a : ℂ)) =
      charFun (P.map X) t - 1 + (a : ℂ) by ring]
    exact herr
  have ha' : a ^ 2 ≤ t ^ 4 * v ^ 2 := by dsimp [a]; nlinarith [sq_nonneg (t ^ 2 * v)]
  exact h.trans (add_le_add herr' (happrox.trans ha'))

end LectureNotes
