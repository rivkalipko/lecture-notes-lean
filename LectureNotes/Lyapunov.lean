import LectureNotes.LindebergFeller

set_option autoImplicit false

/-! L3: Lyapunov's higher-moment condition implies the Lindeberg condition.
The exponent increment is an arbitrary positive real number. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem lyapunov_pointwise_truncation_bound (x : ℝ) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    (if δ < |x| then x ^ 2 else 0) ≤ (δ ^ η)⁻¹ * |x| ^ (2 + η) := by
  by_cases hx : δ < |x|
  · rw [if_pos hx, mul_comm (δ ^ η)⁻¹, ← div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hδ η)).mpr
    rw [Real.rpow_add (hδ.trans hx), Real.rpow_two, sq_abs]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hx.le hη.le) (sq_nonneg x)
  · rw [if_neg hx]
    exact mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hδ.le _))
      (Real.rpow_nonneg (abs_nonneg x) _)

theorem lyapunov_truncSecondMoment_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hXm : Measurable X) (hX : MemLp X 2 P) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hint : Integrable (fun ω => |X ω| ^ (2 + η)) P) :
    truncSecondMoment P X δ ≤ (δ ^ η)⁻¹ * ∫ ω, |X ω| ^ (2 + η) ∂P := by
  unfold truncSecondMoment
  rw [← integral_const_mul]
  apply integral_mono (integrable_truncSecondMoment hXm hX δ) (hint.const_mul _)
  exact fun ω => lyapunov_pointwise_truncation_bound (X ω) hδ hη

/-- Lyapunov implies Lindeberg for normalized finite rows. Independence and
centering are needed for the CLT, but not for this implication between moment
conditions. -/
theorem lyapunov_implies_lindeberg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ → ℕ}
    {X : (n : ℕ) → Fin (m n) → Ω → ℝ} {η : ℝ} (hη : 0 < η)
    (hXm : ∀ n i, Measurable (X n i)) (hX : ∀ n i, MemLp (X n i) 2 P)
    (hint : ∀ n i, Integrable (fun ω => |X n i ω| ^ (2 + η)) P)
    (hlyap : Tendsto (fun n => ∑ i, ∫ ω, |X n i ω| ^ (2 + η) ∂P) atTop (𝓝 0)) :
    ∀ δ > 0, Tendsto (fun n => ∑ i, truncSecondMoment P (X n i) δ) atTop (𝓝 0) := by
  intro δ hδ
  apply squeeze_zero
    (fun n => Finset.sum_nonneg (fun i _ => truncSecondMoment_nonneg _ _))
    (g := fun n => (δ ^ η)⁻¹ * ∑ i, ∫ ω, |X n i ω| ^ (2 + η) ∂P)
  · intro n
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => lyapunov_truncSecondMoment_bound
      (hXm n i) (hX n i) hδ hη (hint n i))
  · simpa only [mul_zero] using hlyap.const_mul ((δ ^ η)⁻¹)

/-- Lyapunov's central limit theorem for independent centered finite rows.
The positive real higher-moment exponent need not be an integer. -/
theorem lyapunov_triangular_array {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ → ℕ}
    {X : (n : ℕ) → Fin (m n) → Ω → ℝ} {η : ℝ} (hη : 0 < η)
    (hXm : ∀ n i, Measurable (X n i)) (hX : ∀ n i, MemLp (X n i) 2 P)
    (hmean : ∀ n i, (∫ ω, X n i ω ∂P) = 0)
    (hind : ∀ n, iIndepFun (X n) P)
    (hvar : Tendsto (fun n => ∑ i, ∫ ω, X n i ω ^ 2 ∂P) atTop (𝓝 1))
    (hint : ∀ n i, Integrable (fun ω => |X n i ω| ^ (2 + η)) P)
    (hlyap : Tendsto (fun n => ∑ i, ∫ ω, |X n i ω| ^ (2 + η) ∂P) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω => ∑ i, X n i ω) atTop id (fun _ => P)
      (gaussianReal 0 1) :=
  lindeberg_feller_triangular_array hXm hX hmean hind hvar
    (lyapunov_implies_lindeberg hη hXm hX hint hlyap)

/-- The exact normalized higher-moment condition displayed after L3 Theorem
13 implies the displayed Lindeberg condition for the original sequence. -/
theorem lyapunov_implies_lindeberg_sequence {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ}
    (c : ℕ → ℝ) {η : ℝ} (hη : 0 < η)
    (hZm : ∀ i, Measurable (Z i)) (hZ : ∀ i, MemLp (Z i) 2 P)
    (hc : ∀ᶠ n in atTop, 0 < c n)
    (hint : ∀ i, Integrable (fun ω => |Z i ω - P[Z i]| ^ (2 + η)) P)
    (hlyap : Tendsto (fun n => (c n ^ (2 + η))⁻¹ *
      ∑ i ∈ Finset.range n, ∫ ω, |Z i ω - P[Z i]| ^ (2 + η) ∂P) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (c n ^ 2)⁻¹ * ∑ i ∈ Finset.range n,
      ∫ ω, if ε * c n < |Z i ω - P[Z i]| then (Z i ω - P[Z i]) ^ 2 else 0 ∂P)
      atTop (𝓝 0) := by
  intro ε hε
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity))
    (g := fun n => (ε ^ η)⁻¹ * ((c n ^ (2 + η))⁻¹ *
      ∑ i ∈ Finset.range n, ∫ ω, |Z i ω - P[Z i]| ^ (2 + η) ∂P))
  · filter_upwards [hc] with n hn
    have hb (i : ℕ) := lyapunov_truncSecondMoment_bound
      ((hZm i).sub measurable_const) ((hZ i).sub (memLp_const _))
      (mul_pos hε hn) hη (hint i)
    have hs := Finset.sum_le_sum (s := Finset.range n) (fun i _ => hb i)
    have he : (c n ^ 2)⁻¹ * ((ε * c n) ^ η)⁻¹ = (ε ^ η)⁻¹ * (c n ^ (2 + η))⁻¹ := by
      rw [Real.mul_rpow hε.le hn.le, Real.rpow_add hn, Real.rpow_two]
      simp only [mul_inv_rev]
      ring
    have hs' := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (sq_nonneg (c n)))
    simpa only [truncSecondMoment, Pi.sub_apply, ← Finset.mul_sum, ← mul_assoc, he] using hs'
  · simpa only [mul_zero] using hlyap.const_mul ((ε ^ η)⁻¹)

/-- Lyapunov CLT in the sequence notation and normalization of the notes. -/
theorem lyapunov_sequence {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ}
    (c : ℕ → ℝ) {η : ℝ} (hη : 0 < η)
    (hZm : ∀ i, Measurable (Z i)) (hZ : ∀ i, MemLp (Z i) 2 P)
    (hind : iIndepFun Z P) (hc : ∀ᶠ n in atTop, 0 < c n)
    (hcsq : ∀ n, c n ^ 2 = ∑ i ∈ Finset.range n, Var[Z i; P])
    (hint : ∀ i, Integrable (fun ω => |Z i ω - P[Z i]| ^ (2 + η)) P)
    (hlyap : Tendsto (fun n => (c n ^ (2 + η))⁻¹ *
      ∑ i ∈ Finset.range n, ∫ ω, |Z i ω - P[Z i]| ^ (2 + η) ∂P) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n ω => (∑ i ∈ Finset.range n, (Z i ω - P[Z i])) / c n)
      atTop id (fun _ => P) (gaussianReal 0 1) :=
  lindeberg_feller_sequence c hZm hZ hind hc hcsq
    (lyapunov_implies_lindeberg_sequence c hη hZm hZ hc hint hlyap)

end LectureNotes
