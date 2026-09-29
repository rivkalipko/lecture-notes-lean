import LectureNotes.DecisionTheory
import LectureNotes.NormalSampling

set_option autoImplicit false

/-! L13 normal-means risk calculations. Constant shrinkage and oracle
optimization are separate from the data-dependent James–Stein risk theorem. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem affine_normal_risk {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} {θ : ℝ} {v : ℝ≥0}
    (hY : HasLaw Y (gaussianReal θ v) P) (a b : ℝ) :
    mse P (fun ω => a + b * Y ω) θ = b ^ 2 * v + (a + (b - 1) * θ) ^ 2 := by
  have hi := hY.identDistrib HasLaw.id
  have hY2 : MemLp Y 2 P := hi.memLp_iff.mpr (memLp_id_gaussianReal 2)
  have hm : (∫ ω, Y ω ∂P) = θ := by
    rw [hi.integral_eq]; exact integral_id_gaussianReal
  have hv : Var[Y; P] = v := by
    rw [hi.variance_eq]; exact variance_id_gaussianReal
  have he : (fun ω => a + b * Y ω) = fun ω => b * Y ω + a := by funext ω; ring
  have haff : MemLp (fun ω => b * Y ω + a) 2 P :=
    (hY2.const_mul b).add (memLp_const a)
  rw [he, mse_eq_variance_add_bias_sq P haff θ,
    variance_add_const (hY2.aestronglyMeasurable.const_mul b), variance_const_mul, hv]
  unfold bias
  rw [integral_add (hY2.integrable (by norm_num) |>.const_mul b) (integrable_const a),
    integral_const_mul, hm, integral_const]
  simp only [probReal_univ, one_smul]
  ring

/-- The squared-error risk adds across coordinates; independence is not needed
for this moment calculation. Normal marginals with common variance suffice. -/
theorem normal_means_shrinkage_risk {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : ℕ}
    {Y : Fin p → Ω → ℝ} {θ : Fin p → ℝ} {v : ℝ≥0}
    (hY : ∀ i, HasLaw (Y i) (gaussianReal (θ i) v) P) (c : ℝ) :
    (∫ ω, ∑ i, (c * Y i ω - θ i) ^ 2 ∂P) =
      (1 - c) ^ 2 * (∑ i, θ i ^ 2) + c ^ 2 * p * v := by
  have hint (i : Fin p) : Integrable (fun ω => (c * Y i ω - θ i) ^ 2) P := by
    have h₂ : MemLp (Y i) 2 P :=
      ((hY i).identDistrib HasLaw.id).memLp_iff.mpr (memLp_id_gaussianReal 2)
    exact ((h₂.const_mul c).sub (memLp_const (θ i))).integrable_sq
  rw [integral_finset_sum _ (fun i _ => hint i)]
  have hi (i : Fin p) := affine_normal_risk (hY i) 0 c
  simp only [mse, zero_add] at hi
  simp_rw [hi, Finset.sum_add_distrib, mul_pow]
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem normal_means_identity_risk {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : ℕ}
    {Y : Fin p → Ω → ℝ} {θ : Fin p → ℝ} {v : ℝ≥0}
    (hY : ∀ i, HasLaw (Y i) (gaussianReal (θ i) v) P) :
    (∫ ω, ∑ i, (Y i ω - θ i) ^ 2 ∂P) = p * v := by
  simpa using normal_means_shrinkage_risk hY 1

/-- Completing the square proves the oracle coefficient is the global
minimizer, including the case of a zero signal. -/
theorem oracle_shrinkage_risk_identity (signal noise c : ℝ) (h : signal + noise ≠ 0) :
    (1 - c) ^ 2 * signal + c ^ 2 * noise =
      signal * noise / (signal + noise) +
        (signal + noise) * (c - signal / (signal + noise)) ^ 2 := by
  field_simp
  <;> ring

theorem oracle_shrinkage_optimal (signal noise c : ℝ) (hs : 0 ≤ signal) (hn : 0 < noise) :
    signal * noise / (signal + noise) ≤ (1 - c) ^ 2 * signal + c ^ 2 * noise := by
  rw [oracle_shrinkage_risk_identity signal noise c (by positivity)]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))

theorem oracle_shrinkage_strict_improvement (signal noise : ℝ)
    (hs : 0 ≤ signal) (hn : 0 < noise) : signal * noise / (signal + noise) < noise := by
  rw [div_lt_iff₀ (by positivity : 0 < signal + noise)]
  nlinarith [sq_pos_of_pos hn]

/-- The source's James–Stein rule, with real subtraction in p−2. At the
origin the returned vector is zero. This definition alone is not its risk theorem. -/
def jamesStein {p : ℕ} (variance : ℝ) (y : Fin p → ℝ) : Fin p → ℝ :=
  fun i => (1 - ((p : ℝ) - 2) * variance / (∑ j, y j ^ 2)) * y i

def positivePartJamesStein {p : ℕ} (variance : ℝ) (y : Fin p → ℝ) : Fin p → ℝ :=
  fun i => max 0 (1 - ((p : ℝ) - 2) * variance / (∑ j, y j ^ 2)) * y i

theorem jamesStein_measurable {p : ℕ} (variance : ℝ) :
    Measurable (jamesStein (p := p) variance) := by unfold jamesStein; fun_prop

theorem jamesStein_zero {p : ℕ} (variance : ℝ) :
    jamesStein (p := p) variance 0 = 0 := by ext i; simp [jamesStein]

end LectureNotes
