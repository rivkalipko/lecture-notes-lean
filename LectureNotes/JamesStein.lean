import LectureNotes.JamesSteinRisk

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

theorem regularized_inverse_le {S ε : ℝ} (hS : 0 ≤ S) (hε : 0 ≤ ε) :
    S / (S + ε) ^ 2 ≤ 1 / S := by
  by_cases hz : S = 0
  · simp [hz]
  have hS' : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
  have hd : 0 < S + ε := by positivity
  rw [div_le_div_iff₀ (sq_pos_of_pos hd) hS']
  nlinarith [sq_nonneg ε]

theorem regularizedSteinCorrection_sq_sum {p : ℕ} (a ε : ℝ) (y : Fin p → ℝ) :
    (∑ i, regularizedSteinCorrection a ε y i ^ 2) =
      a ^ 2 * (normalSquareNorm y / (normalSquareNorm y + ε) ^ 2) := by
  simp only [regularizedSteinCorrection, div_pow, mul_pow, neg_sq]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  unfold normalSquareNorm
  ring

theorem regularizedStein_loss_bound {p : ℕ} (θ y : Fin p → ℝ) (a ε : ℝ) (hε : 0 ≤ ε) :
    (∑ i, (y i + regularizedSteinCorrection a ε y i - θ i) ^ 2) ≤
      2 * (∑ i, (y i - θ i) ^ 2) + 2 * a ^ 2 * (1 / normalSquareNorm y) := by
  calc
    _ ≤ ∑ i, (2 * (y i - θ i) ^ 2 + 2 * regularizedSteinCorrection a ε y i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [sq_nonneg (y i - θ i - regularizedSteinCorrection a ε y i)]
    _ = 2 * (∑ i, (y i - θ i) ^ 2) +
        2 * a ^ 2 * (normalSquareNorm y / (normalSquareNorm y + ε) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        regularizedSteinCorrection_sq_sum]
      ring
    _ ≤ _ := add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left (regularized_inverse_le (normalSquareNorm_nonneg y) hε)
        (by positivity : 0 ≤ 2 * a ^ 2))

theorem regularizedSteinCorrection_limit {p : ℕ} (a : ℝ) (y : Fin p → ℝ) (i : Fin p)
    {eps : ℕ → ℝ} (heps : Tendsto eps atTop (𝓝 0)) :
    Tendsto (fun k => regularizedSteinCorrection a (eps k) y i) atTop
      (𝓝 (regularizedSteinCorrection a 0 y i)) := by
  by_cases hz : normalSquareNorm y = 0
  · have hy : y i = 0 := by
      have h := coordinate_sq_le_normalSquareNorm y i
      rw [hz] at h
      nlinarith [sq_nonneg (y i)]
    simp [regularizedSteinCorrection, hy]
  · simpa only [regularizedSteinCorrection, add_zero, Pi.div_apply] using!
      tendsto_const_nhds.div (tendsto_const_nhds.add heps) (by simpa using hz)

theorem normalSquareNorm_pos_ae {n : ℕ} (θ : Fin (n + 1) → ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    ∀ᵐ y ∂Measure.pi (fun j => gaussianReal (θ j) v), 0 < normalSquareNorm y := by
  letI : NullSingletonClass (gaussianReal (θ 0) v) := nullSingletonClass_gaussianReal hv
  have hz : ∀ᵐ y ∂Measure.pi (fun j => gaussianReal (θ j) v), y 0 ≠ 0 :=
    (measurePreserving_eval (fun j => gaussianReal (θ j) v) 0).quasiMeasurePreserving.ae
      ((gaussianReal (θ 0) v).ae_ne 0)
  filter_upwards [hz] with y hy
  exact (sq_pos_of_ne_zero hy).trans_le (coordinate_sq_le_normalSquareNorm y 0)


/-- A single integrable envelope controls squared losses down to ε = 0. -/
theorem regularized_stein_loss_limit {p : ℕ} (P : Measure (Fin p → ℝ))
    (θ : Fin p → ℝ) (a : ℝ)
    (hi : Integrable (fun y => 1 / normalSquareNorm y) P)
    (hn : Integrable (fun y => ∑ i, (y i - θ i) ^ 2) P)
    {eps : ℕ → ℝ} (he0 : ∀ k, 0 ≤ eps k) (he : Tendsto eps atTop (𝓝 0)) :
    Integrable (fun y => ∑ i, (y i + regularizedSteinCorrection a 0 y i - θ i) ^ 2) P ∧
    Tendsto (fun k => ∫ y, ∑ i, (y i + regularizedSteinCorrection a (eps k) y i - θ i) ^ 2 ∂P)
      atTop (𝓝 (∫ y, ∑ i, (y i + regularizedSteinCorrection a 0 y i - θ i) ^ 2 ∂P)) := by
  let bound y := 2 * (∑ i, (y i - θ i) ^ 2) + 2 * a ^ 2 * (1 / normalSquareNorm y)
  have hb : Integrable bound P := by
    simpa only [bound, Pi.add_apply] using! (hn.const_mul 2).add (hi.const_mul (2 * a ^ 2))
  have hm ε : Measurable (fun y => ∑ i, (y i + regularizedSteinCorrection a ε y i - θ i) ^ 2) := by
    unfold regularizedSteinCorrection normalSquareNorm
    fun_prop
  have hbound {ε : ℝ} (hε : 0 ≤ ε) :
      ∀ᵐ y ∂P, ‖∑ i, (y i + regularizedSteinCorrection a ε y i - θ i) ^ 2‖ ≤ bound y := by
    apply ae_of_all
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact regularizedStein_loss_bound θ y a ε hε
  refine ⟨hb.mono' (hm 0).aestronglyMeasurable (hbound le_rfl), ?_⟩
  apply tendsto_integral_of_dominated_convergence bound
    (fun k => (hm (eps k)).aestronglyMeasurable) hb (fun k => hbound (he0 k))
  apply ae_of_all
  intro y
  apply tendsto_finsetSum
  intro i _
  exact ((tendsto_const_nhds.add (regularizedSteinCorrection_limit a y i he)).sub
    tendsto_const_nhds).pow 2

/-- Exact James–Stein risk, including the integrability and singularity argument. -/
theorem jamesStein_risk_succ {n : ℕ} (θ : Fin (n + 1) → ℝ)
    (v : ℝ≥0) (hv : 0 < v) (hn : 3 ≤ n + 1) :
    (∫ y, ∑ i, (jamesStein v y i - θ i) ^ 2 ∂Measure.pi (fun j => gaussianReal (θ j) v)) =
      (n + 1 : ℕ) * (v : ℝ) - ((((n + 1 : ℕ) : ℝ) - 2) * v) ^ 2 *
        ∫ y, 1 / normalSquareNorm y ∂Measure.pi (fun j => gaussianReal (θ j) v) := by
  let P := Measure.pi (fun j => gaussianReal (θ j) v)
  let a : ℝ := (((n + 1 : ℕ) : ℝ) - 2) * v
  let eps (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have he0 k : 0 < eps k := by dsimp [eps]; positivity
  have helim : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hi := normal_inverse_square_integrable θ v hv hn
  have hnoise : Integrable (fun y : Fin (n + 1) → ℝ => ∑ i, (y i - θ i) ^ 2) P := by
    apply integrable_finsetSum
    intro i _
    have hY : HasLaw (fun y : Fin (n + 1) → ℝ => y i) (gaussianReal (θ i) v) P :=
      ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
    exact ((((hY.identDistrib HasLaw.id).memLp_iff.mpr (memLp_id_gaussianReal 2)).sub
      (memLp_const (θ i))).integrable_sq)
  have hR := (regularized_stein_loss_limit P θ a hi hnoise (fun k => (he0 k).le) helim).2
  have hF : Tendsto (fun k => ∫ y, normalSquareNorm y / (normalSquareNorm y + eps k) ^ 2 ∂P)
      atTop (𝓝 (∫ y, 1 / normalSquareNorm y ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun y => 1 / normalSquareNorm y)
      (fun k => (integrable_regularized_inverse P (he0 k)).1.aestronglyMeasurable) hi
    · intro k
      apply ae_of_all
      intro y
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (normalSquareNorm_nonneg y) (sq_nonneg _))]
      exact regularized_inverse_le (normalSquareNorm_nonneg y) (he0 k).le
    · filter_upwards [normalSquareNorm_pos_ae θ v hv.ne'] with y hy
      have hh : normalSquareNorm y / normalSquareNorm y ^ 2 = 1 / normalSquareNorm y := by field_simp
      rw [← hh]
      exact tendsto_const_nhds.div (by simpa only [add_zero] using
        (tendsto_const_nhds.add helim).pow 2) (pow_ne_zero 2 hy.ne')
  have hG : Tendsto (fun k => ∫ y, eps k / (normalSquareNorm y + eps k) ^ 2 ∂P)
      atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := P) (f := fun _ => (0 : ℝ))
      (F := fun k y => eps k / (normalSquareNorm y + eps k) ^ 2)
      (fun y => 1 / normalSquareNorm y)
      (fun k => (show Measurable (fun y : Fin (n + 1) → ℝ =>
        eps k / (normalSquareNorm y + eps k) ^ 2) from by unfold normalSquareNorm; fun_prop).aestronglyMeasurable)
      hi
    apply (by simpa only [integral_zero] using h)
    · intro k
      filter_upwards [normalSquareNorm_pos_ae θ v hv.ne'] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
        div_le_div_iff₀ (sq_pos_of_pos (add_pos hy (he0 k))) hy]
      nlinarith [sq_nonneg (normalSquareNorm y), sq_nonneg (eps k), mul_pos hy (he0 k)]
    · filter_upwards [normalSquareNorm_pos_ae θ v hv.ne'] with y hy
      simpa only [add_zero, zero_div, Pi.div_apply] using! helim.div
        ((tendsto_const_nhds.add helim).pow 2) (by simpa using pow_ne_zero 2 hy.ne')
  have hrhs := ((show Tendsto (fun _ : ℕ => (n + 1 : ℕ) * (v : ℝ)) atTop
    (𝓝 ((n + 1 : ℕ) * (v : ℝ))) from tendsto_const_nhds).sub (hF.const_mul (a ^ 2))).sub
    (hG.const_mul (2 * a * (n + 1 : ℕ) * v))
  have heq k : (∫ y, ∑ i, (y i + regularizedSteinCorrection a (eps k) y i - θ i) ^ 2 ∂P) =
      (n + 1 : ℕ) * (v : ℝ) - a ^ 2 *
        (∫ y, normalSquareNorm y / (normalSquareNorm y + eps k) ^ 2 ∂P) -
        (2 * a * (n + 1 : ℕ) * v) * (∫ y, eps k / (normalSquareNorm y + eps k) ^ 2 ∂P) := by
    rw [regularized_stein_risk θ v hv.ne' a (eps k) (he0 k)]
    have hcoef : a ^ 2 - 2 * a * v * (((n + 1 : ℕ) : ℝ) - 2) = -a ^ 2 := by dsimp [a]; ring
    rw [hcoef]
    have hd (y : Fin (n + 1) → ℝ) : eps k / (normalSquareNorm y + eps k) ^ 2 =
        eps k * (1 / (normalSquareNorm y + eps k) ^ 2) := by ring
    simp_rw [hd, integral_const_mul]
    ring
  have hlim : Tendsto (fun k => ∫ y, ∑ i,
      (y i + regularizedSteinCorrection a (eps k) y i - θ i) ^ 2 ∂P) atTop
      (𝓝 ((n + 1 : ℕ) * (v : ℝ) - a ^ 2 * (∫ y, 1 / normalSquareNorm y ∂P))) := by
    simp_rw [heq]
    simpa only [mul_zero, sub_zero] using hrhs
  have hresult := tendsto_nhds_unique hR hlim
  have hjs (y : Fin (n + 1) → ℝ) i : y i + regularizedSteinCorrection a 0 y i = jamesStein v y i := by
    unfold regularizedSteinCorrection jamesStein normalSquareNorm a
    ring
  simpa only [hjs, a, P] using hresult


/-- L13 Theorem 2, exact risk for every parameter and every p ≥ 3. -/
theorem jamesStein_risk {p : ℕ} (θ : Fin p → ℝ) (v : ℝ≥0) (hv : 0 < v) (hp : 3 ≤ p) :
    (∫ y, ∑ i, (jamesStein v y i - θ i) ^ 2 ∂Measure.pi (fun j => gaussianReal (θ j) v)) =
      p * (v : ℝ) - (((p : ℝ) - 2) * v) ^ 2 *
        ∫ y, 1 / normalSquareNorm y ∂Measure.pi (fun j => gaussianReal (θ j) v) := by
  cases p with
  | zero => omega
  | succ n => exact jamesStein_risk_succ θ v hv hp

theorem normal_inverse_square_positive {p : ℕ} (θ : Fin p → ℝ) (v : ℝ≥0)
    (hv : 0 < v) (hp : 3 ≤ p) :
    0 < ∫ y, 1 / normalSquareNorm y ∂Measure.pi (fun j => gaussianReal (θ j) v) := by
  cases p with
  | zero => omega
  | succ n =>
    apply (integral_pos_iff_support_of_nonneg
      (fun y => div_nonneg (by norm_num) (normalSquareNorm_nonneg y))
      (normal_inverse_square_integrable θ v hv hp)).mpr
    have hs : Function.support (fun y : Fin (n + 1) → ℝ => 1 / normalSquareNorm y) =ᵐ[
        Measure.pi (fun j => gaussianReal (θ j) v)] univ := by
      filter_upwards [normalSquareNorm_pos_ae θ v hv.ne'] with y hy
      change (1 / normalSquareNorm y ≠ 0) = True
      exact propext (iff_true_intro (one_div_pos.mpr hy).ne')
    rw [measure_congr hs, measure_univ]
    norm_num

/-- Strict improvement at every mean vector. Positive variance is essential. -/
theorem jamesStein_strict_improvement {p : ℕ} (θ : Fin p → ℝ) (v : ℝ≥0)
    (hv : 0 < v) (hp : 3 ≤ p) :
    (∫ y, ∑ i, (jamesStein v y i - θ i) ^ 2 ∂Measure.pi (fun j => gaussianReal (θ j) v)) <
      p * (v : ℝ) := by
  rw [jamesStein_risk θ v hv hp]
  have hdim : (2 : ℝ) < p := by exact_mod_cast hp
  have ha : 0 < ((p : ℝ) - 2) * v := mul_pos (sub_pos.mpr hdim) (by exact_mod_cast hv)
  have h := mul_pos (sq_pos_of_pos ha) (normal_inverse_square_positive θ v hv hp)
  linarith

/-- Transfer to any sample space carrying independent Gaussian coordinates. -/
theorem jamesStein_risk_of_independent_normals {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : ℕ} (hp : 3 ≤ p)
    (θ : Fin p → ℝ) (v : ℝ≥0) (hv : 0 < v) (Y : Fin p → Ω → ℝ)
    (hY : ∀ i, HasLaw (Y i) (gaussianReal (θ i) v) P) (hind : iIndepFun Y P) :
    (∫ ω, ∑ i, (jamesStein v (fun j => Y j ω) i - θ i) ^ 2 ∂P) =
      p * (v : ℝ) - (((p : ℝ) - 2) * v) ^ 2 *
        ∫ ω, 1 / (∑ i, Y i ω ^ 2) ∂P := by
  have hlaw := iIndepFun.hasLaw_pi hY hind
  have hm : Measurable (fun y : Fin p → ℝ => ∑ i, (jamesStein v y i - θ i) ^ 2) := by
    unfold jamesStein
    fun_prop
  have hi : Measurable (fun y : Fin p → ℝ => 1 / normalSquareNorm y) := by
    unfold normalSquareNorm
    fun_prop
  have hr : (∫ ω, ∑ i, (jamesStein v (fun j => Y j ω) i - θ i) ^ 2 ∂P) =
      ∫ y, ∑ i, (jamesStein v y i - θ i) ^ 2 ∂Measure.pi (fun j => gaussianReal (θ j) v) := by
    simpa only [Function.comp_apply] using! hlaw.integral_comp hm.aestronglyMeasurable
  have hinv : (∫ ω, 1 / (∑ i, Y i ω ^ 2) ∂P) =
      ∫ y, 1 / normalSquareNorm y ∂Measure.pi (fun j => gaussianReal (θ j) v) := by
    simpa only [Function.comp_apply, normalSquareNorm] using! hlaw.integral_comp hi.aestronglyMeasurable
  rw [hr, hinv, jamesStein_risk θ v hv hp]

end LectureNotes
