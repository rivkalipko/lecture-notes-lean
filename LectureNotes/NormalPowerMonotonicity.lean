import LectureNotes.NormalSamplePower
import LectureNotes.DensityDerivatives

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

/-- Exact two-sided standard-normal power at shift δ and cutoff c. -/
def normalTwoSidedPower (c δ : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) (δ - c) + cdf (gaussianReal 0 1) (-δ - c)

/-- The power function is the rejection probability under the actual normal law. -/
theorem normalTwoSidedPower_eq_probability (c δ : ℝ) (hc : 0 ≤ c) :
    normalTwoSidedPower c δ = (gaussianReal δ 1).real {x | c < |x|} := by
  have h := normal_two_sided_power_symmetric (T := id) (δ := δ) measurable_id HasLaw.id hc
  simpa only [normalTwoSidedPower, id_eq] using h.symm

/-- The derivative is obtained from the actual Gaussian density. -/
theorem gaussian_cdf_hasDerivAt (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (cdf (gaussianReal m v)) (gaussianPDFReal m v x) x := by
  have he : gaussianReal m v = volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal m v x)) :=
    gaussianReal_of_var_ne_zero m hv
  have : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal m v x))) :=
    he ▸ inferInstance
  rw [he]
  apply density_cdf_hasDerivAt (integrable_gaussianPDFReal m v) (gaussianPDFReal_nonneg m v)
  unfold gaussianPDFReal
  fun_prop

theorem normalTwoSidedPower_hasDerivAt (c δ : ℝ) :
    HasDerivAt (normalTwoSidedPower c)
      (gaussianPDFReal 0 1 (δ - c) - gaussianPDFReal 0 1 (-δ - c)) δ := by
  have h1 := (gaussian_cdf_hasDerivAt 0 (by norm_num : (1 : ℝ≥0) ≠ 0) (δ - c)).comp δ
    ((hasDerivAt_id δ).sub_const c)
  have h2 := (gaussian_cdf_hasDerivAt 0 (by norm_num : (1 : ℝ≥0) ≠ 0) (-δ - c)).comp δ
    ((hasDerivAt_id δ).neg.sub_const c)
  convert! h1.add h2 using 1
  simp [sub_eq_add_neg]

theorem normalTwoSidedPower_neg (c δ : ℝ) :
    normalTwoSidedPower c (-δ) = normalTwoSidedPower c δ := by
  simp only [normalTwoSidedPower, neg_neg, add_comm]

theorem normalTwoSidedPower_abs (c δ : ℝ) :
    normalTwoSidedPower c |δ| = normalTwoSidedPower c δ := by
  rcases le_total 0 δ with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, normalTwoSidedPower_neg]

/-- With a positive cutoff, exact power strictly increases with the
nonnegative magnitude of the standardized effect. -/
theorem normalTwoSidedPower_strictMonoOn {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (normalTwoSidedPower c) (Ici 0) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici (0 : ℝ))
    (fun x _ => (normalTwoSidedPower_hasDerivAt c x).continuousAt.continuousWithinAt)
    (fun x _ => (normalTwoSidedPower_hasDerivAt c x).hasDerivWithinAt)
  intro x hx
  have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  apply sub_pos.mpr
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  apply Real.exp_lt_exp.mpr
  nlinarith [mul_pos hx0 hc]

/-- The probabilistic statement compares the actual Gaussian test powers. -/
theorem normal_two_sided_power_strict_abs_effect {c δ₁ δ₂ : ℝ}
    (hc : 0 < c) (hδ : |δ₁| < |δ₂|) :
    (gaussianReal δ₁ 1).real {x | c < |x|} <
      (gaussianReal δ₂ 1).real {x | c < |x|} := by
  have h := normalTwoSidedPower_strictMonoOn hc
    (show |δ₁| ∈ Ici (0 : ℝ) from abs_nonneg δ₁)
    (show |δ₂| ∈ Ici (0 : ℝ) from abs_nonneg δ₂) hδ
  rw [normalTwoSidedPower_abs, normalTwoSidedPower_abs] at h
  rwa [normalTwoSidedPower_eq_probability c δ₁ hc.le,
    normalTwoSidedPower_eq_probability c δ₂ hc.le] at h

/-- The null power of the exact central normal test is its nominal level. -/
theorem normalTwoSidedPower_null {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    normalTwoSidedPower (distributionQuantile (gaussianReal 0 1) (1 - α / 2)) 0 = α := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hq : 1 - α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  simp only [normalTwoSidedPower, zero_sub, neg_zero]
  simp only [standardNormal_cdf_neg]
  rw [cdf_eq_real, distributionQuantile_exact _ _ hq]
  ring

/-- Both tails are retained in the large-effect limit. -/
theorem normalTwoSidedPower_tendsto_atTop (c : ℝ) :
    Tendsto (normalTwoSidedPower c) atTop (𝓝 1) := by
  have h1 := (tendsto_cdf_atTop (gaussianReal 0 1)).comp
    (tendsto_atTop_add_const_right atTop (-c) tendsto_id)
  have h2 := (tendsto_cdf_atBot (gaussianReal 0 1)).comp
    (tendsto_atBot_add_const_right atTop (-c) tendsto_neg_atTop_atBot)
  change Tendsto (fun x => cdf (gaussianReal 0 1) (x - c) +
    cdf (gaussianReal 0 1) (-x - c)) atTop (𝓝 1)
  simpa only [Function.comp_def, id_eq, sub_eq_add_neg, add_zero] using! h1.add h2

/-- Divergence of the absolute effect suffices, with either sign or changing signs. -/
theorem normalTwoSidedPower_tendsto_abs {ι : Type*} {l : Filter ι} {δ : ι → ℝ}
    (hδ : Tendsto (fun i => |δ i|) l atTop) (c : ℝ) :
    Tendsto (fun i => normalTwoSidedPower c (δ i)) l (𝓝 1) := by
  simpa only [Function.comp_def, normalTwoSidedPower_abs] using
    (normalTwoSidedPower_tendsto_atTop c).comp hδ

/-- Increasing the sample size strictly increases exact normal power at a
fixed nonzero effect, a positive standard deviation, and a positive cutoff. -/
theorem normalTwoSidedPower_sample_size_strict {m n : ℕ} {τ σ c : ℝ}
    (hmn : m < n) (hτ : τ ≠ 0) (hσ : 0 < σ) (hc : 0 < c) :
    normalTwoSidedPower c (Real.sqrt m * τ / σ) <
      normalTwoSidedPower c (Real.sqrt n * τ / σ) := by
  rw [← normalTwoSidedPower_abs c (Real.sqrt m * τ / σ),
    ← normalTwoSidedPower_abs c (Real.sqrt n * τ / σ)]
  apply normalTwoSidedPower_strictMonoOn hc (abs_nonneg (Real.sqrt m * τ / σ))
    (abs_nonneg (Real.sqrt n * τ / σ))
  simp only [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hσ]
  apply (div_lt_div_iff_of_pos_right hσ).mpr
  apply mul_lt_mul_of_pos_right _ (abs_pos.mpr hτ)
  exact Real.sqrt_lt_sqrt (Nat.cast_nonneg m) (by exact_mod_cast hmn)

/-- Fixed nonzero effects are detected with probability tending to one as
the normal sample size grows. -/
theorem normalTwoSidedPower_sample_size_tendsto {τ σ : ℝ} (hτ : τ ≠ 0) (hσ : 0 < σ)
    (c : ℝ) : Tendsto (fun n : ℕ => normalTwoSidedPower c (Real.sqrt n * τ / σ))
      atTop (𝓝 1) := by
  apply normalTwoSidedPower_tendsto_abs _ c
  have hs : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hh := hs.atTop_mul_const (div_pos (abs_pos.mpr hτ) hσ)
  simpa only [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hσ,
    mul_div_assoc] using hh

/-- The sample-size limit for the actual IID normal sampling experiment. -/
theorem normal_iid_two_sided_test_power_tendsto_one {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    {μ μ₀ : ℝ} {v : ℝ≥0} (hv : 0 < v) (hμ : μ ≠ μ₀)
    (hXm : ∀ i, Measurable (X i)) (hX : ∀ i, HasLaw (X i) (gaussianReal μ v) P)
    (hind : iIndepFun X P) {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ => P.real {ω | c <
      |Real.sqrt (n + 1 : ℕ) * (sampleMean (fun i : Fin (n + 1) => X i ω) - μ₀) /
        Real.sqrt v|}) atTop (𝓝 1) := by
  have hp := (normalTwoSidedPower_sample_size_tendsto (sub_ne_zero.mpr hμ)
    (Real.sqrt_pos.mpr (show (0 : ℝ) < v from hv)) c).comp (tendsto_add_atTop_nat 1)
  convert! hp using 1
  funext n
  exact normal_two_sided_power_symmetric (by unfold sampleMean; fun_prop)
    (normal_iid_z_law (Nat.succ_pos n) hv (fun i => hX i)
      (hind.precomp Fin.val_injective)) hc

end LectureNotes
