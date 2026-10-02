import LectureNotes.Information

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- Correlation is covariance divided by the product of standard deviations.
Its probabilistic interpretation below requires both variances positive. -/
def correlation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  cov[X, Y; P] / Real.sqrt (Var[X; P] * Var[Y; P])

theorem covariance_congr_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[P] X') (hY : Y =ᵐ[P] Y') :
    cov[X, Y; P] = cov[X', Y'; P] := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  apply integral_congr_ae
  filter_upwards [hX, hY] with ω hx hy
  rw [hx, hy]

theorem correlation_comm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) : correlation P X Y = correlation P Y X := by
  unfold correlation
  rw [covariance_comm X Y, mul_comm]

theorem correlation_abs_le_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hvX : 0 < Var[X; P]) (hvY : 0 < Var[Y; P]) :
    |correlation P X Y| ≤ 1 := by
  have hd : 0 < Real.sqrt (Var[X; P] * Var[Y; P]) := Real.sqrt_pos.mpr (mul_pos hvX hvY)
  have hc : |cov[X, Y; P]| ≤ Real.sqrt (Var[X; P] * Var[Y; P]) :=
    Real.le_sqrt_of_sq_le (by simpa only [sq_abs] using covariance_sq_le_variances P hX hY)
  rw [correlation, abs_div, abs_of_pos hd]
  exact (div_le_one hd).mpr hc

/-- Equality in the covariance bound is equivalent to affine dependence
almost surely, provided the regressor has positive variance. -/
theorem covariance_equality_iff_affine {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (hvY : 0 < Var[Y; P]) :
    cov[X, Y; P] ^ 2 = Var[X; P] * Var[Y; P] ↔
      ∃ a b : ℝ, X =ᵐ[P] (fun ω => a + b * Y ω) := by
  constructor
  · intro heq
    let Z : Ω → ℝ := fun ω => Var[Y; P] * X ω - cov[X, Y; P] * Y ω
    have hZ : MemLp Z 2 P := (hX.const_mul _).sub (hY.const_mul _)
    have hz : Var[Z; P] = 0 := by
      rw [show Z = (fun ω => Var[Y; P] * X ω - cov[X, Y; P] * Y ω) from rfl,
        variance_fun_sub (hX.const_mul _) (hY.const_mul _), variance_const_mul,
        variance_const_mul, covariance_const_mul_left, covariance_const_mul_right]
      calc
        _ = Var[Y; P] * (Var[X; P] * Var[Y; P] - cov[X, Y; P] ^ 2) := by ring
        _ = 0 := by rw [← heq, sub_self, mul_zero]
    have hconst := ae_eq_integral_of_variance_eq_zero hZ hz
    refine ⟨(∫ ω, Z ω ∂P) / Var[Y; P], cov[X, Y; P] / Var[Y; P], ?_⟩
    filter_upwards [hconst] with ω hω
    change Var[Y; P] * X ω - cov[X, Y; P] * Y ω = (∫ ω, Z ω ∂P) at hω
    field_simp [hvY.ne']
    nlinarith
  · rintro ⟨a, b, heq⟩
    have hc : cov[X, Y; P] = b * Var[Y; P] := by
      rw [covariance_congr_ae heq (EventuallyEq.rfl),
        covariance_const_add_left ((hY.const_mul b).integrable (by norm_num)) a,
        covariance_const_mul_left, covariance_self hY.aemeasurable]
    have hv : Var[X; P] = b ^ 2 * Var[Y; P] := by
      rw [variance_congr heq, variance_const_add (hY.const_mul b).aestronglyMeasurable a,
        variance_const_mul]
    rw [hc, hv]
    ring

/-- Perfect absolute correlation holds exactly for affine dependence almost
surely. Positive variances exclude the undefined statistical zero-scale case. -/
theorem correlation_abs_eq_one_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hvX : 0 < Var[X; P]) (hvY : 0 < Var[Y; P]) :
    |correlation P X Y| = 1 ↔ ∃ a b : ℝ, X =ᵐ[P] (fun ω => a + b * Y ω) := by
  have hp : 0 < Var[X; P] * Var[Y; P] := mul_pos hvX hvY
  have hd : 0 < Real.sqrt (Var[X; P] * Var[Y; P]) := Real.sqrt_pos.mpr hp
  rw [correlation, abs_div, abs_of_pos hd, div_eq_one_iff_eq hd.ne']
  rw [← covariance_equality_iff_affine P hX hY hvY]
  constructor
  · intro heq
    have h := congrArg (fun x : ℝ => x ^ 2) heq
    simpa only [sq_abs, Real.sq_sqrt hp.le] using h
  · intro heq
    have hs := Real.sq_sqrt hp.le
    have ha := sq_abs (cov[X, Y; P])
    have ha0 := abs_nonneg (cov[X, Y; P])
    nlinarith

end LectureNotes
