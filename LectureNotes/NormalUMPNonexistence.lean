import LectureNotes.NormalTestPower
import LectureNotes.NeymanPearson

set_option autoImplicit false

/-! L9's two-sided counterexample for the normal-observation experiment.
This includes the sample-mean experiment after substituting its known variance;
it does not assert a reduction from all tests of the full sample to mean-based tests. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- The actual normal density ratio, rather than a proportional likelihood kernel. -/
theorem gaussian_density_ratio {v : ℝ≥0} (hv : 0 < v) (θ₀ θ₁ x : ℝ) :
    gaussianPDFReal θ₁ v x / gaussianPDFReal θ₀ v x =
      Real.exp (((θ₁ - θ₀) * x + (θ₀ ^ 2 - θ₁ ^ 2) / 2) / v) := by
  have hc : (Real.sqrt (2 * Real.pi * v))⁻¹ ≠ 0 := by positivity
  simp only [gaussianPDFReal]
  rw [mul_div_mul_left _ _ hc, ← Real.exp_sub]
  congr 1
  ring

/-- A smaller mean has a strictly decreasing likelihood ratio. -/
theorem gaussian_density_ratio_strictAnti {v : ℝ≥0} (hv : 0 < v) {θ₀ θ₁ : ℝ}
    (hθ : θ₁ < θ₀) :
    StrictAnti (fun x => gaussianPDFReal θ₁ v x / gaussianPDFReal θ₀ v x) := by
  intro x y hxy
  dsimp only
  rw [gaussian_density_ratio hv, gaussian_density_ratio hv, Real.exp_lt_exp]
  apply (div_lt_div_iff_of_pos_right (by exact_mod_cast hv)).mpr
  have h := mul_lt_mul_of_neg_left hxy (sub_neg.mpr hθ)
  linarith

/-- The lower-tail rejection rule, with the boundary immaterial under a normal law. -/
def gaussianLowerTail (c : ℝ) : StatisticalTest ℝ :=
  StatisticalTest.ofRejectionSet (Iio c) measurableSet_Iio

theorem gaussianLowerTail_power (θ : ℝ) {v : ℝ≥0} (hv : 0 < v) (c : ℝ) :
    (gaussianLowerTail c).power (gaussianReal θ v) =
      cdf (gaussianReal 0 1) ((c - θ) / Real.sqrt v) := by
  have : NullSingletonClass (gaussianReal θ v) := nullSingletonClass_gaussianReal hv.ne'
  rw [gaussianLowerTail, StatisticalTest.power_ofRejectionSet, measureReal_congr Iio_ae_eq_Iic]
  exact normal_lower_tail hv (show HasLaw id (gaussianReal θ v) (gaussianReal θ v) from HasLaw.id) c

/-- Exact lower-tail size at the normal quantile. -/
theorem gaussianLowerTail_quantile_size (θ₀ : ℝ) {v : ℝ≥0} (hv : 0 < v)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    (gaussianLowerTail (distributionQuantile (gaussianReal θ₀ v) α)).power
      (gaussianReal θ₀ v) = α := by
  have : NullSingletonClass (gaussianReal θ₀ v) := nullSingletonClass_gaussianReal hv.ne'
  rw [gaussianLowerTail, StatisticalTest.power_ofRejectionSet,
    measureReal_congr Iio_ae_eq_Iic, distributionQuantile_exact _ _ hα]

/-- The normal observation law is exactly the density model used by Neyman–Pearson. -/
theorem gaussian_densityPower (φ : StatisticalTest ℝ) (θ : ℝ)
    {v : ℝ≥0} (hv : 0 < v) :
    φ.densityPower volume (gaussianPDFReal θ v) = φ.power (gaussianReal θ v) := by
  rw [φ.densityPower_eq_power (measurable_gaussianPDFReal θ v).aemeasurable
    (ae_of_all _ (gaussianPDFReal_nonneg θ v)), gaussianReal_of_var_ne_zero θ hv.ne']
  rfl

/-- Every cutoff has the likelihood-threshold property against every smaller mean. -/
theorem gaussianLowerTail_threshold {v : ℝ≥0} (hv : 0 < v) {θ₀ θ₁ : ℝ}
    (hθ : θ₁ < θ₀) (c : ℝ) :
    (gaussianLowerTail c).HasLikelihoodThreshold volume (gaussianPDFReal θ₀ v)
      (gaussianPDFReal θ₁ v) (gaussianPDFReal θ₁ v c / gaussianPDFReal θ₀ v c) := by
  apply ae_of_all
  intro x
  have hp := gaussianPDFReal_pos θ₀ v x hv.ne'
  have ha := gaussian_density_ratio_strictAnti hv hθ
  constructor
  · intro h
    have hx : x < c := ha.lt_iff_gt.mp ((lt_div_iff₀ hp).mpr h)
    simp [gaussianLowerTail, StatisticalTest.ofRejectionSet, hx]
  · intro h
    have hx : c < x := ha.lt_iff_gt.mp ((div_lt_iff₀ hp).mpr h)
    simp [gaussianLowerTail, StatisticalTest.ofRejectionSet, not_lt.mpr hx.le]

/-- Neyman–Pearson optimality applies to all measurable randomized tests of the
normal observation, rather than only to tests with a threshold shape. -/
theorem gaussianLowerTail_most_powerful {v : ℝ≥0} (hv : 0 < v) {θ₀ θ₁ : ℝ}
    (hθ : θ₁ < θ₀) (c : ℝ) (ψ : StatisticalTest ℝ)
    (hsize : ψ.power (gaussianReal θ₀ v) ≤ (gaussianLowerTail c).power (gaussianReal θ₀ v)) :
    ψ.power (gaussianReal θ₁ v) ≤ (gaussianLowerTail c).power (gaussianReal θ₁ v) := by
  simpa only [gaussian_densityPower _ _ hv] using
    (gaussianLowerTail c).neyman_pearson ψ (integrable_gaussianPDFReal θ₀ v)
      (integrable_gaussianPDFReal θ₁ v)
      (div_nonneg (gaussianPDFReal_nonneg θ₁ v c) (gaussianPDFReal_nonneg θ₀ v c))
      (gaussianLowerTail_threshold hv hθ c) (by simpa only [gaussian_densityPower _ _ hv] using hsize)

/-- Equality in optimal power forces agreement almost everywhere, since the
normal likelihood ratio has only one boundary point. -/
theorem gaussianLowerTail_unique {v : ℝ≥0} (hv : 0 < v) {θ₀ θ₁ : ℝ}
    (hθ : θ₁ < θ₀) (c : ℝ) (ψ : StatisticalTest ℝ)
    (hsize : ψ.power (gaussianReal θ₀ v) ≤ (gaussianLowerTail c).power (gaussianReal θ₀ v))
    (hpower : ψ.power (gaussianReal θ₁ v) = (gaussianLowerTail c).power (gaussianReal θ₁ v)) :
    ψ.reject =ᵐ[volume] (gaussianLowerTail c).reject := by
  have ht := (gaussianLowerTail c).neyman_pearson_necessity ψ
    (integrable_gaussianPDFReal θ₀ v) (integrable_gaussianPDFReal θ₁ v)
    (div_nonneg (gaussianPDFReal_nonneg θ₁ v c) (gaussianPDFReal_nonneg θ₀ v c))
    (gaussianLowerTail_threshold hv hθ c)
    (by simpa only [gaussian_densityPower _ _ hv] using hsize)
    (by simpa only [gaussian_densityPower _ _ hv] using hpower)
  filter_upwards [ht, (volume : Measure ℝ).ae_ne c] with x hx hxc
  have hp := gaussianPDFReal_pos θ₀ v x hv.ne'
  have ha := gaussian_density_ratio_strictAnti hv hθ
  rcases lt_or_gt_of_ne hxc with hlt | hgt
  · have hh := hx.1 ((lt_div_iff₀ hp).mp (ha hlt))
    simpa [gaussianLowerTail, StatisticalTest.ofRejectionSet, hlt] using hh
  · have hh := hx.2 ((div_lt_iff₀ hp).mp (ha hgt))
    simpa [gaussianLowerTail, StatisticalTest.ofRejectionSet, not_lt.mpr hgt.le] using hh

/-- For normal data the power decrease is strict, as claimed in the example. -/
theorem gaussianLowerTail_power_strictAnti {v : ℝ≥0} (hv : 0 < v) (c : ℝ) :
    StrictAnti (fun θ => (gaussianLowerTail c).power (gaussianReal θ v)) := by
  intro θ₁ θ₂ hθ
  dsimp only
  rw [gaussianLowerTail_power _ hv, gaussianLowerTail_power _ hv]
  apply gaussian_cdf_strictMono 0 1 (by norm_num)
  exact (div_lt_div_iff_of_pos_right (Real.sqrt_pos.mpr (by exact_mod_cast hv))).mpr
    (sub_lt_sub_left hθ c)

/-- The calibrated lower-tail test is UMP for the one-sided composite problem. -/
theorem gaussianLowerTail_one_sided_ump (θ₀ : ℝ) {v : ℝ≥0} (hv : 0 < v)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    (gaussianLowerTail (distributionQuantile (gaussianReal θ₀ v) α)).IsUMP
      (fun θ => gaussianReal θ v) (Ici θ₀) (Iio θ₀) α := by
  let c := distributionQuantile (gaussianReal θ₀ v) α
  have hcal := gaussianLowerTail_quantile_size θ₀ hv hα
  constructor
  · intro θ hθ
    exact ((gaussianLowerTail_power_strictAnti hv c).antitone hθ).trans hcal.le
  · intro ψ hψ θ hθ
    apply gaussianLowerTail_most_powerful hv hθ c ψ
    rw [hcal]
    exact hψ θ₀ (mem_Ici.mpr le_rfl)

/-- For every interior size there is no UMP test of a normal mean against a
two-sided alternative. The class includes every measurable randomized test. -/
theorem normal_observation_no_two_sided_ump (θ₀ : ℝ) {v : ℝ≥0} (hv : 0 < v)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    ¬ ∃ φ : StatisticalTest ℝ,
      φ.IsUMP (fun θ => gaussianReal θ v) {θ₀} {θ | θ ≠ θ₀} α := by
  rintro ⟨φ, hlevel, hump⟩
  let c := distributionQuantile (gaussianReal θ₀ v) α
  let ψ := gaussianLowerTail c
  have hcal : ψ.power (gaussianReal θ₀ v) = α := gaussianLowerTail_quantile_size θ₀ hv hα
  have hψ : ψ.HasLevel (fun θ => gaussianReal θ v) {θ₀} α := by
    intro θ hθ
    rw [mem_singleton_iff.mp hθ, hcal]
  have hsize : φ.power (gaussianReal θ₀ v) ≤ ψ.power (gaussianReal θ₀ v) := by
    rw [hcal]
    exact hlevel θ₀ (mem_singleton θ₀)
  have hpower : φ.power (gaussianReal (θ₀ - 1) v) = ψ.power (gaussianReal (θ₀ - 1) v) :=
    le_antisymm (gaussianLowerTail_most_powerful hv (by linarith) c φ hsize)
      (hump ψ hψ (θ₀ - 1) (by simp))
  have hae := gaussianLowerTail_unique hv (by linarith : θ₀ - 1 < θ₀) c φ hsize hpower
  have heq : φ.power (gaussianReal (θ₀ + 1) v) = ψ.power (gaussianReal (θ₀ + 1) v) :=
    integral_congr_ae ((gaussianReal_absolutelyContinuous _ hv.ne').ae_eq hae)
  have hsmall : ψ.power (gaussianReal (θ₀ + 1) v) < α := by
    rw [← hcal]
    dsimp only [ψ]
    rw [gaussianLowerTail_power _ hv, gaussianLowerTail_power _ hv]
    apply gaussian_cdf_strictMono 0 1 (by norm_num)
    apply (div_lt_div_iff_of_pos_right (Real.sqrt_pos.mpr (by exact_mod_cast hv))).mpr
    linarith
  let coin : StatisticalTest ℝ := ⟨fun _ => α, measurable_const,
    fun _ => hα.1.le, fun _ => hα.2.le⟩
  have hcoin (θ : ℝ) : coin.power (gaussianReal θ v) = α := by
    simp [StatisticalTest.power, coin]
  have hc : coin.HasLevel (fun θ => gaussianReal θ v) {θ₀} α := by
    intro θ _
    exact (hcoin θ).le
  have h := hump coin hc (θ₀ + 1) (by simp)
  rw [hcoin, heq] at h
  exact (not_le_of_gt hsmall) h

end LectureNotes
