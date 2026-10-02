import LectureNotes.LindebergRows
import LectureNotes.BootstrapLindeberg

noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped Topology

/-- Squared tails vanish along any diverging real truncation thresholds. -/
theorem truncSecondMoment_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hXm : Measurable X) (hX : MemLp X 2 P) {r : ℕ → ℝ}
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun n => truncSecondMoment P X (r n)) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun ω => X ω ^ 2)
    (fun n => (integrable_truncSecondMoment hXm hX (r n)).aestronglyMeasurable)
    hX.integrable_sq
    (fun n => ae_of_all _ (fun ω => by
      split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X ω)), sq_nonneg]))
    (ae_of_all _ (fun ω => by
      apply tendsto_const_nhds.congr'
      filter_upwards [hr.eventually (eventually_ge_atTop (|X ω|))] with n hn
      simp [not_lt.mpr hn]))
  simpa only [truncSecondMoment, integral_zero] using h

theorem truncSecondMoment_div {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (δ : ℝ) {a : ℝ} (ha : 0 < a) :
    truncSecondMoment P (fun ω => X ω / a) δ =
      truncSecondMoment P X (δ * a) / a ^ 2 := by
  unfold truncSecondMoment
  have he (ω : Ω) : (if δ < |X ω / a| then (X ω / a) ^ 2 else 0) =
      (if δ * a < |X ω| then X ω ^ 2 else 0) / a ^ 2 := by
    simp only [abs_div, abs_of_pos ha, lt_div_iff₀ ha, div_pow]
    split_ifs <;> simp
  simp_rw [he]
  exact integral_div _ _

theorem truncSecondMoment_neg {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (δ : ℝ) :
    truncSecondMoment P (fun ω => -X ω) δ = truncSecondMoment P X δ := by
  simp only [truncSecondMoment, abs_neg, neg_sq]

/-- Repeated observations from one group satisfy Lindeberg after scaling,
provided the squared scale dominates sample size times a positive constant.
No relative sample-size limit is required. -/
theorem iid_group_lindeberg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hXm : Measurable X) (hX : MemLp X 2 P) {m : ℕ → ℕ} {a : ℕ → ℝ}
    (hm : Tendsto m atTop atTop) (ha : ∀ n, 0 < a n)
    {v : ℝ} (hv : 0 < v) (hbound : ∀ n, (m n : ℝ) * v ≤ (a n) ^ 2)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (m n : ℝ) * truncSecondMoment P (fun ω => X ω / a n) δ)
      atTop (𝓝 0) := by
  have hatop : Tendsto a atTop atTop := by
    have hmv : Tendsto (fun n => (m n : ℝ) * v) atTop atTop :=
      (tendsto_mul_const_atTop_of_pos hv).mpr (tendsto_natCast_atTop_atTop.comp hm)
    apply tendsto_atTop_mono (fun n => ?_) (Real.tendsto_sqrt_atTop.comp hmv)
    exact (Real.sqrt_le_iff).mpr ⟨(ha n).le, hbound n⟩
  have htail := truncSecondMoment_tendsto_zero hXm hX
    ((tendsto_const_mul_atTop_of_pos hδ).mpr hatop)
  have hlim : Tendsto (fun n => truncSecondMoment P X (δ * a n) / v) atTop (𝓝 0) := by
    simpa only [zero_div] using htail.div_const v
  apply squeeze_zero (fun n => mul_nonneg (Nat.cast_nonneg _) (truncSecondMoment_nonneg _ _)) _ hlim
  intro n
  rw [truncSecondMoment_div P X δ (ha n)]
  have hb : (m n : ℝ) / (a n) ^ 2 ≤ 1 / v := by
    rw [div_le_div_iff₀ (sq_pos_of_pos (ha n)) hv]
    simpa only [one_mul] using hbound n
  have h := mul_le_mul_of_nonneg_right hb (truncSecondMoment_nonneg (P := P) X (δ * a n))
  convert! h using 1 <;> ring

/-- The theoretical standard error for a difference of independent means. -/
def twoSampleStandardError (m n : ℕ) (vx vy : ℝ) : ℝ :=
  Real.sqrt (vx / m + vy / n)

theorem twoSampleStandardError_pos {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {vx vy : ℝ} (hx : 0 < vx) (hy : 0 < vy) :
    0 < twoSampleStandardError m n vx vy := by
  unfold twoSampleStandardError
  positivity

theorem twoSample_scales_sq {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {vx vy : ℝ} (hx : 0 < vx) (hy : 0 < vy) :
    ((m : ℝ) * twoSampleStandardError m n vx vy) ^ 2 = m * vx + m ^ 2 * vy / n ∧
    ((n : ℝ) * twoSampleStandardError m n vx vy) ^ 2 = n * vy + n ^ 2 * vx / m := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have he : (twoSampleStandardError m n vx vy) ^ 2 = vx / m + vy / n := by
    exact Real.sq_sqrt (by positivity)
  rw [mul_pow, mul_pow, he]
  constructor <;> field_simp <;> ring

theorem twoSample_variance_normalization {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {vx vy : ℝ} (hx : 0 < vx) (hy : 0 < vy) :
    (m : ℝ) * (vx / ((m : ℝ) * twoSampleStandardError m n vx vy) ^ 2) +
      (n : ℝ) * (vy / ((n : ℝ) * twoSampleStandardError m n vx vy) ^ 2) = 1 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have he : (twoSampleStandardError m n vx vy) ^ 2 = vx / m + vy / n := by
    exact Real.sq_sqrt (by positivity)
  have hs := (twoSampleStandardError_pos hm hn hx hy).ne'
  field_simp at he
  field_simp
  nlinarith [he]

end LectureNotes
