import LectureNotes.NeymanPearsonExistence

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

namespace StatisticalTest

/-- Randomization between two decision rules. -/
def mixture (φ ψ : StatisticalTest Ω) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : StatisticalTest Ω where
  reject x := a * φ.reject x + b * ψ.reject x
  measurable_reject := (measurable_const.mul φ.measurable_reject).add
    (measurable_const.mul ψ.measurable_reject)
  nonneg x := add_nonneg (mul_nonneg ha (φ.nonneg x)) (mul_nonneg hb (ψ.nonneg x))
  le_one x := by nlinarith [φ.le_one x, ψ.le_one x]

theorem densityPower_mixture (φ ψ : StatisticalTest Ω) {f : Ω → ℝ}
    (hf : Integrable f ν) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (φ.mixture ψ a b ha hb hab).densityPower ν f =
      a * φ.densityPower ν f + b * ψ.densityPower ν f := by
  have he x : (a * φ.reject x + b * ψ.reject x) * f x =
      a * (φ.reject x * f x) + b * (ψ.reject x * f x) := by ring
  simp only [densityPower, mixture, he]
  rw [integral_add ((φ.integrable_mul_density hf).const_mul a)
    ((ψ.integrable_mul_density hf).const_mul b), integral_const_mul, integral_const_mul]

theorem densityPower_linear_density (φ : StatisticalTest Ω) {f g : Ω → ℝ}
    (hf : Integrable f ν) (hg : Integrable g ν) (a b : ℝ) :
    φ.densityPower ν (fun x => a * f x + b * g x) =
      a * φ.densityPower ν f + b * φ.densityPower ν g := by
  have he x : φ.reject x * (a * f x + b * g x) =
      a * (φ.reject x * f x) + b * (φ.reject x * g x) := by ring
  simp only [densityPower, he]
  rw [integral_add ((φ.integrable_mul_density hf).const_mul a)
    ((φ.integrable_mul_density hg).const_mul b), integral_const_mul, integral_const_mul]

/-- The statistical optimization Lagrangian, with size budget `α`. -/
def lagrangian (φ : StatisticalTest Ω) (ν : Measure Ω) (f₀ f₁ : Ω → ℝ)
    (α k : ℝ) : ℝ := φ.densityPower ν f₁ - k * (φ.densityPower ν f₀ - α)

theorem lagrangian_eq_integral (φ : StatisticalTest Ω) {f₀ f₁ : Ω → ℝ}
    (h₀ : Integrable f₀ ν) (h₁ : Integrable f₁ ν) (α k : ℝ) :
    φ.lagrangian ν f₀ f₁ α k =
      (∫ x, φ.reject x * (f₁ x - k * f₀ x) ∂ν) + k * α := by
  have h := φ.densityPower_linear_density h₁ h₀ 1 (-k)
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at h
  rw [← densityPower, h]
  unfold lagrangian
  ring

/-- Likelihood thresholding maximizes the Lagrangian over every randomized rule. -/
theorem likelihood_threshold_maximizes_lagrangian (φ ψ : StatisticalTest Ω)
    {f₀ f₁ : Ω → ℝ} {k : ℝ} (h₀ : Integrable f₀ ν) (h₁ : Integrable f₁ ν)
    (hφ : φ.HasLikelihoodThreshold ν f₀ f₁ k) (α : ℝ) :
    ψ.lagrangian ν f₀ f₁ α k ≤ φ.lagrangian ν f₀ f₁ α k := by
  rw [ψ.lagrangian_eq_integral h₀ h₁, φ.lagrangian_eq_integral h₀ h₁]
  apply add_le_add ?_ le_rfl
  apply integral_mono_ae (ψ.integrable_mul_density (h₁.sub (h₀.const_mul k)))
    (φ.integrable_mul_density (h₁.sub (h₀.const_mul k)))
  filter_upwards [φ.likelihood_threshold_contrast_nonneg ψ hφ] with x hx
  change 0 ≤ (φ.reject x - ψ.reject x) * (f₁ x - k * f₀ x) at hx
  change ψ.reject x * (f₁ x - k * f₀ x) ≤ φ.reject x * (f₁ x - k * f₀ x)
  nlinarith

/-- The multiplier gives a supporting line to attainable size/power pairs.
This is the precise shadow-price statement; no differentiability of the
optimal power curve is asserted. -/
theorem likelihood_threshold_supporting_line (φ ψ : StatisticalTest Ω)
    {f₀ f₁ : Ω → ℝ} {k α : ℝ} (h₀ : Integrable f₀ ν) (h₁ : Integrable f₁ ν)
    (hφ : φ.HasLikelihoodThreshold ν f₀ f₁ k) (hsize : φ.densityPower ν f₀ = α) :
    ψ.densityPower ν f₁ ≤ φ.densityPower ν f₁ + k * (ψ.densityPower ν f₀ - α) := by
  have h := φ.likelihood_threshold_maximizes_lagrangian ψ h₀ h₁ hφ α
  simp only [lagrangian, hsize, sub_self, mul_zero, sub_zero] at h
  linarith

end StatisticalTest

/-- The best attainable true-positive rate under a false-positive-rate budget. -/
def rocFrontier (ν : Measure Ω) (f₀ f₁ : Ω → ℝ) (α : ℝ) : ℝ :=
  sSup {β | ∃ φ : StatisticalTest Ω, φ.densityPower ν f₀ ≤ α ∧ φ.densityPower ν f₁ = β}

theorem rocFrontier_eq_of_optimal {f₀ f₁ : Ω → ℝ} {α : ℝ}
    (φ : StatisticalTest Ω) (hsize : φ.densityPower ν f₀ ≤ α)
    (hopt : ∀ ψ : StatisticalTest Ω, ψ.densityPower ν f₀ ≤ α →
      ψ.densityPower ν f₁ ≤ φ.densityPower ν f₁) :
    rocFrontier ν f₀ f₁ α = φ.densityPower ν f₁ := by
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨φ.densityPower ν f₁, φ, hsize, rfl⟩
  · rintro b ⟨ψ, hψ, rfl⟩
    exact hopt ψ hψ
  · intro b hb
    exact ⟨φ.densityPower ν f₁, ⟨φ, hsize, rfl⟩, hb⟩

/-- Every interior ROC budget is attained by a calibrated likelihood threshold. -/
theorem rocFrontier_attained {f₀ f₁ : Ω → ℝ}
    (hm₀ : Measurable f₀) (hm₁ : Measurable f₁)
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    ∃ k ≥ 0, ∃ φ : StatisticalTest Ω,
      φ.HasLikelihoodThreshold ν f₀ f₁ k ∧ φ.densityPower ν f₀ = α ∧
      φ.densityPower ν f₁ = rocFrontier ν f₀ f₁ α := by
  obtain ⟨k, hk, φ, hφ, hs⟩ := exists_neyman_pearson_test ν f₀ f₁ hm₀ hm₁ hi₀ hn₀ hn₁ h₀ α hα
  refine ⟨k, hk, φ, hφ, hs, ?_⟩
  symm
  exact rocFrontier_eq_of_optimal φ hs.le (fun ψ hψ =>
    φ.neyman_pearson ψ hi₀ hi₁ hk hφ (hψ.trans hs.ge))

theorem rocFrontier_monotoneOn {f₀ f₁ : Ω → ℝ}
    (hm₀ : Measurable f₀) (hm₁ : Measurable f₁)
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) : MonotoneOn (rocFrontier ν f₀ f₁) (Ioo 0 1) := by
  intro α hα β hβ hab
  obtain ⟨ka, hka, φa, hφa, hsa, hpa⟩ :=
    rocFrontier_attained hm₀ hm₁ hi₀ hi₁ hn₀ hn₁ h₀ hα
  obtain ⟨kb, hkb, φb, hφb, hsb, hpb⟩ :=
    rocFrontier_attained hm₀ hm₁ hi₀ hi₁ hn₀ hn₁ h₀ hβ
  rw [← hpa, ← hpb]
  exact φb.neyman_pearson φa hi₀ hi₁ hkb hφb (by rw [hsa, hsb]; exact hab)

/-- Randomization makes the optimal ROC frontier concave. -/
theorem rocFrontier_concaveOn {f₀ f₁ : Ω → ℝ}
    (hm₀ : Measurable f₀) (hm₁ : Measurable f₁)
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) : ConcaveOn ℝ (Ioo 0 1) (rocFrontier ν f₀ f₁) := by
  refine ⟨convex_Ioo _ _, ?_⟩
  intro α hα β hβ a b ha hb hab
  obtain ⟨ka, hka, φa, hφa, hsa, hpa⟩ :=
    rocFrontier_attained hm₀ hm₁ hi₀ hi₁ hn₀ hn₁ h₀ hα
  obtain ⟨kb, hkb, φb, hφb, hsb, hpb⟩ :=
    rocFrontier_attained hm₀ hm₁ hi₀ hi₁ hn₀ hn₁ h₀ hβ
  have hc : a * α + b * β ∈ Ioo (0 : ℝ) 1 := by
    have hc := (convex_Ioo (0 : ℝ) 1) hα hβ ha hb hab
    simpa only [smul_eq_mul] using hc
  obtain ⟨kc, hkc, φc, hφc, hsc, hpc⟩ :=
    rocFrontier_attained hm₀ hm₁ hi₀ hi₁ hn₀ hn₁ h₀ hc
  have hs : (φa.mixture φb a b ha hb hab).densityPower ν f₀ = a * α + b * β := by
    rw [φa.densityPower_mixture φb hi₀, hsa, hsb]
  have hp := φc.neyman_pearson (φa.mixture φb a b ha hb hab)
    hi₀ hi₁ hkc hφc (by rw [hs, hsc])
  rw [φa.densityPower_mixture φb hi₁, hpa, hpb, hpc] at hp
  simpa only [smul_eq_mul] using hp

/-- Population density when a fraction `π` of firms is noncompliant. -/
def auditPopulationDensity (π : ℝ) (f₀ f₁ : Ω → ℝ) : Ω → ℝ :=
  fun x => (1 - π) * f₀ x + π * f₁ x

theorem densityPower_auditPopulation (φ : StatisticalTest Ω) {f₀ f₁ : Ω → ℝ}
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν) (π : ℝ) :
    φ.densityPower ν (auditPopulationDensity π f₀ f₁) =
      (1 - π) * φ.densityPower ν f₀ + π * φ.densityPower ν f₁ :=
  φ.densityPower_linear_density hi₀ hi₁ (1 - π) π

theorem auditPopulationDensity_integrable {f₀ f₁ : Ω → ℝ}
    (h₀ : Integrable f₀ ν) (h₁ : Integrable f₁ ν) (π : ℝ) :
    Integrable (auditPopulationDensity π f₀ f₁) ν :=
  (h₀.const_mul (1 - π)).add (h₁.const_mul π)

theorem auditPopulationDensity_integral {f₀ f₁ : Ω → ℝ}
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) (h₁ : (∫ x, f₁ x ∂ν) = 1) (π : ℝ) :
    (∫ x, auditPopulationDensity π f₀ f₁ x ∂ν) = 1 := by
  unfold auditPopulationDensity
  rw [integral_add (hi₀.const_mul _) (hi₁.const_mul _),
    integral_const_mul, integral_const_mul, h₀, h₁]
  ring

/-- The population law is the actual mixture of the two conditional laws. -/
theorem auditPopulationLaw_eq_mixture {f₀ f₁ : Ω → ℝ}
    (hm₀ : Measurable f₀) (hm₁ : Measurable f₁)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    {π : ℝ} (hπ : π ∈ Icc (0 : ℝ) 1) :
    ν.withDensity (fun x => ENNReal.ofReal (auditPopulationDensity π f₀ f₁ x)) =
      ENNReal.ofReal (1 - π) • ν.withDensity (fun x => ENNReal.ofReal (f₀ x)) +
      ENNReal.ofReal π • ν.withDensity (fun x => ENNReal.ofReal (f₁ x)) := by
  have he : (fun x => ENNReal.ofReal (auditPopulationDensity π f₀ f₁ x)) =
      ENNReal.ofReal (1 - π) • (fun x => ENNReal.ofReal (f₀ x)) +
      ENNReal.ofReal π • (fun x => ENNReal.ofReal (f₁ x)) := by
    funext x
    simp only [auditPopulationDensity, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr hπ.2) (hn₀ x))
        (mul_nonneg hπ.1 (hn₁ x)),
      ENNReal.ofReal_mul (sub_nonneg.mpr hπ.2), ENNReal.ofReal_mul hπ.1]
  rw [he, withDensity_add_left (hm₀.ennreal_ofReal.const_smul _),
    withDensity_smul _ hm₀.ennreal_ofReal, withDensity_smul _ hm₁.ennreal_ofReal]

theorem auditPopulationLaw_isProbabilityMeasure {f₀ f₁ : Ω → ℝ}
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) (h₁ : (∫ x, f₁ x ∂ν) = 1)
    {π : ℝ} (hπ : π ∈ Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (ν.withDensity (fun x =>
      ENNReal.ofReal (auditPopulationDensity π f₀ f₁ x))) := by
  apply density_model_isProbabilityMeasure (auditPopulationDensity_integrable hi₀ hi₁ π)
    (ae_of_all _ fun x => add_nonneg
      (mul_nonneg (sub_nonneg.mpr hπ.2) (hn₀ x)) (mul_nonneg hπ.1 (hn₁ x)))
  exact auditPopulationDensity_integral hi₀ hi₁ h₀ h₁ π

/-- The actual audit rate is the prevalence-weighted mixture of false- and
true-positive rates, rather than the false-positive rate alone. -/
theorem actual_population_audit_rate (φ : StatisticalTest Ω) {f₀ f₁ : Ω → ℝ}
    (hm₀ : Measurable f₀) (hm₁ : Measurable f₁)
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    {π : ℝ} (hπ : π ∈ Icc (0 : ℝ) 1) :
    φ.power (ν.withDensity (fun x => ENNReal.ofReal (auditPopulationDensity π f₀ f₁ x))) =
      (1 - π) * φ.power (ν.withDensity (fun x => ENNReal.ofReal (f₀ x))) +
      π * φ.power (ν.withDensity (fun x => ENNReal.ofReal (f₁ x))) := by
  have hm : Measurable (auditPopulationDensity π f₀ f₁) :=
    (measurable_const.mul hm₀).add (measurable_const.mul hm₁)
  have hn x : 0 ≤ auditPopulationDensity π f₀ f₁ x :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr hπ.2) (hn₀ x)) (mul_nonneg hπ.1 (hn₁ x))
  rw [← φ.densityPower_eq_power hm.aemeasurable (ae_of_all _ hn)]
  rw [densityPower_auditPopulation φ hi₀ hi₁]
  rw [φ.densityPower_eq_power hm₀.aemeasurable (ae_of_all _ hn₀),
    φ.densityPower_eq_power hm₁.aemeasurable (ae_of_all _ hn₁)]

/-- Exact capacity calibration and optimal detection under the total population
audit constraint. The threshold compares noncompliance density to population
density; for positive prevalence this also ranks by posterior noncompliance
probability. -/
theorem exists_capacity_optimal_audit {f₀ f₁ : Ω → ℝ}
    (hm₀ : Measurable f₀) (hm₁ : Measurable f₁)
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) (h₁ : (∫ x, f₁ x ∂ν) = 1)
    {π α : ℝ} (hπ : π ∈ Icc (0 : ℝ) 1) (hα : α ∈ Ioo (0 : ℝ) 1) :
    ∃ k ≥ 0, ∃ φ : StatisticalTest Ω,
      φ.HasLikelihoodThreshold ν (auditPopulationDensity π f₀ f₁) f₁ k ∧
      (1 - π) * φ.densityPower ν f₀ + π * φ.densityPower ν f₁ = α ∧
      ∀ ψ : StatisticalTest Ω,
        (1 - π) * ψ.densityPower ν f₀ + π * ψ.densityPower ν f₁ ≤ α →
        ψ.densityPower ν f₁ ≤ φ.densityPower ν f₁ := by
  have hm : Measurable (auditPopulationDensity π f₀ f₁) :=
    (measurable_const.mul hm₀).add (measurable_const.mul hm₁)
  have hn x : 0 ≤ auditPopulationDensity π f₀ f₁ x :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr hπ.2) (hn₀ x)) (mul_nonneg hπ.1 (hn₁ x))
  have hi := auditPopulationDensity_integrable hi₀ hi₁ π
  obtain ⟨k, hk, φ, hφ, hs⟩ := exists_neyman_pearson_test ν
    (auditPopulationDensity π f₀ f₁) f₁ hm hm₁ hi hn hn₁
    (auditPopulationDensity_integral hi₀ hi₁ h₀ h₁ π) α hα
  refine ⟨k, hk, φ, hφ, ?_, ?_⟩
  · simpa only [densityPower_auditPopulation φ hi₀ hi₁] using hs
  · intro ψ hψ
    apply φ.neyman_pearson ψ hi hi₁ hk hφ
    rw [hs]
    simpa only [densityPower_auditPopulation ψ hi₀ hi₁] using hψ

/-- The capacity theorem expressed entirely using the actual population and
noncompliant-firm laws. Randomization calibrates ties exactly. -/
theorem exists_capacity_optimal_audit_actual {f₀ f₁ : Ω → ℝ}
    (hm₀ : Measurable f₀) (hm₁ : Measurable f₁)
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) (h₁ : (∫ x, f₁ x ∂ν) = 1)
    {π α : ℝ} (hπ : π ∈ Icc (0 : ℝ) 1) (hα : α ∈ Ioo (0 : ℝ) 1) :
    ∃ k ≥ 0, ∃ φ : StatisticalTest Ω,
      φ.HasLikelihoodThreshold ν (auditPopulationDensity π f₀ f₁) f₁ k ∧
      φ.power (ν.withDensity (fun x => ENNReal.ofReal (auditPopulationDensity π f₀ f₁ x))) = α ∧
      ∀ ψ : StatisticalTest Ω,
        ψ.power (ν.withDensity (fun x => ENNReal.ofReal (auditPopulationDensity π f₀ f₁ x))) ≤ α →
        ψ.power (ν.withDensity (fun x => ENNReal.ofReal (f₁ x))) ≤
          φ.power (ν.withDensity (fun x => ENNReal.ofReal (f₁ x))) := by
  obtain ⟨k, hk, φ, ht, hs, ho⟩ :=
    exists_capacity_optimal_audit hm₀ hm₁ hi₀ hi₁ hn₀ hn₁ h₀ h₁ hπ hα
  have hp (ψ : StatisticalTest Ω) :
      ψ.power (ν.withDensity (fun x => ENNReal.ofReal (auditPopulationDensity π f₀ f₁ x))) =
      (1 - π) * ψ.densityPower ν f₀ + π * ψ.densityPower ν f₁ := by
    rw [actual_population_audit_rate ψ hm₀ hm₁ hi₀ hi₁ hn₀ hn₁ hπ,
      ← ψ.densityPower_eq_power hm₀.aemeasurable (ae_of_all _ hn₀),
      ← ψ.densityPower_eq_power hm₁.aemeasurable (ae_of_all _ hn₁)]
  refine ⟨k, hk, φ, ht, (hp φ).trans hs, fun ψ hψ => ?_⟩
  rw [← ψ.densityPower_eq_power hm₁.aemeasurable (ae_of_all _ hn₁),
    ← φ.densityPower_eq_power hm₁.aemeasurable (ae_of_all _ hn₁)]
  exact ho ψ (by rwa [hp ψ] at hψ)

/-- On points with positive null density, ranking by population-normalized
alternative density is exactly likelihood-ratio ranking when `π < 1`. -/
theorem audit_ranking_eq_likelihood_ranking {f₀ f₁ : Ω → ℝ}
    (hn₁ : ∀ x, 0 ≤ f₁ x) {π : ℝ} (hπ : π ∈ Ico (0 : ℝ) 1)
    {x y : Ω} (hx : 0 < f₀ x) (hy : 0 < f₀ y) :
    f₁ x / auditPopulationDensity π f₀ f₁ x ≤ f₁ y / auditPopulationDensity π f₀ f₁ y ↔
      f₁ x / f₀ x ≤ f₁ y / f₀ y := by
  have hmx : 0 < auditPopulationDensity π f₀ f₁ x :=
    add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hπ.2) hx) (mul_nonneg hπ.1 (hn₁ x))
  have hmy : 0 < auditPopulationDensity π f₀ f₁ y :=
    add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hπ.2) hy) (mul_nonneg hπ.1 (hn₁ y))
  rw [div_le_div_iff₀ hmx hmy, div_le_div_iff₀ hx hy]
  unfold auditPopulationDensity
  constructor <;> intro h <;> nlinarith [sub_pos.mpr hπ.2]

theorem size_budget_does_not_equal_population_capacity {π α β : ℝ}
    (hπ : 0 < π) (hpower : α < β) : α < (1 - π) * α + π * β := by
  nlinarith

end LectureNotes
