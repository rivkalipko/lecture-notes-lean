import LectureNotes.TargetingROC

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- At zero false-positive budget, exactly the null-density-zero region can be
audited freely. This endpoint need not have a finite likelihood-ratio cutoff. -/
theorem zero_size_roc_optimum {f₀ f₁ : Ω → ℝ}
    (hm₀ : Measurable f₀) (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x) :
    ∃ φ : StatisticalTest Ω, φ.densityPower ν f₀ = 0 ∧
      ∀ ψ : StatisticalTest Ω, ψ.densityPower ν f₀ ≤ 0 →
        ψ.densityPower ν f₁ ≤ φ.densityPower ν f₁ := by
  let φ := StatisticalTest.ofRejectionSet {x | f₀ x = 0}
    (measurableSet_eq_fun hm₀ measurable_const)
  have hs : φ.densityPower ν f₀ = 0 := by
    have he x : φ.reject x * f₀ x = 0 := by
      by_cases hx : f₀ x = 0 <;> simp [φ, StatisticalTest.ofRejectionSet, hx]
    simp only [StatisticalTest.densityPower, he, integral_zero]
  refine ⟨φ, hs, fun ψ hψ => ?_⟩
  have hn : ∀ᵐ x ∂ν, 0 ≤ ψ.reject x * f₀ x :=
    ae_of_all _ fun x => mul_nonneg (ψ.nonneg x) (hn₀ x)
  have hz : (∫ x, ψ.reject x * f₀ x ∂ν) = 0 :=
    le_antisymm hψ (integral_nonneg_of_ae hn)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hn (ψ.integrable_mul_density hi₀)).1 hz
  apply integral_mono_ae (ψ.integrable_mul_density hi₁) (φ.integrable_mul_density hi₁)
  filter_upwards [hae] with x hx
  by_cases h0 : f₀ x = 0
  · have hφ : φ.reject x = 1 := by simp [φ, StatisticalTest.ofRejectionSet, h0]
    rw [hφ, one_mul]
    exact mul_le_of_le_one_left (hn₁ x) (ψ.le_one x)
  · have hψx : ψ.reject x = 0 := (mul_eq_zero.mp hx).resolve_right h0
    simp [hψx, φ, StatisticalTest.ofRejectionSet, h0]

theorem unit_size_roc_optimum {f₀ f₁ : Ω → ℝ}
    (hi₁ : Integrable f₁ ν) (hn₁ : ∀ x, 0 ≤ f₁ x)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) :
    ∃ φ : StatisticalTest Ω, φ.densityPower ν f₀ = 1 ∧
      ∀ ψ : StatisticalTest Ω, ψ.densityPower ν f₀ ≤ 1 →
        ψ.densityPower ν f₁ ≤ φ.densityPower ν f₁ := by
  let φ := StatisticalTest.ofRejectionSet (univ : Set Ω) MeasurableSet.univ
  have hφ x : φ.reject x = 1 := by simp [φ, StatisticalTest.ofRejectionSet]
  refine ⟨φ, ?_, fun ψ _ => ?_⟩
  · simpa only [StatisticalTest.densityPower, hφ, one_mul] using h₀
  · apply integral_mono (ψ.integrable_mul_density hi₁) (φ.integrable_mul_density hi₁)
    intro x
    change ψ.reject x * f₁ x ≤ φ.reject x * f₁ x
    rw [hφ, one_mul]
    exact mul_le_of_le_one_left (hn₁ x) (ψ.le_one x)

/-- The ROC optimum is attained at every budget, including both endpoints. -/
theorem rocFrontier_attained_closed {f₀ f₁ : Ω → ℝ}
    (hm₀ : Measurable f₀) (hm₁ : Measurable f₁)
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    ∃ φ : StatisticalTest Ω, φ.densityPower ν f₀ = α ∧
      φ.densityPower ν f₁ = rocFrontier ν f₀ f₁ α ∧
      ∀ ψ : StatisticalTest Ω, ψ.densityPower ν f₀ ≤ α →
        ψ.densityPower ν f₁ ≤ φ.densityPower ν f₁ := by
  have hex : ∃ φ : StatisticalTest Ω, φ.densityPower ν f₀ = α ∧
      ∀ ψ : StatisticalTest Ω, ψ.densityPower ν f₀ ≤ α →
        ψ.densityPower ν f₁ ≤ φ.densityPower ν f₁ := by
    by_cases hzero : α = 0
    · subst α
      exact zero_size_roc_optimum hm₀ hi₀ hi₁ hn₀ hn₁
    by_cases hone : α = 1
    · subst α
      exact unit_size_roc_optimum hi₁ hn₁ h₀
    exact exists_most_powerful_test ν f₀ f₁ hm₀ hm₁ hi₀ hi₁ hn₀ hn₁ h₀ α
      ⟨lt_of_le_of_ne hα.1 (Ne.symm hzero), lt_of_le_of_ne hα.2 hone⟩
  obtain ⟨φ, hs, ho⟩ := hex
  exact ⟨φ, hs, (rocFrontier_eq_of_optimal φ hs.le ho).symm, ho⟩

theorem rocFrontier_monotoneOn_closed {f₀ f₁ : Ω → ℝ}
    (hm₀ : Measurable f₀) (hm₁ : Measurable f₁)
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) : MonotoneOn (rocFrontier ν f₀ f₁) (Icc 0 1) := by
  intro α hα β hβ hab
  obtain ⟨φa, hsa, hpa, hoa⟩ := rocFrontier_attained_closed hm₀ hm₁ hi₀ hi₁ hn₀ hn₁ h₀ hα
  obtain ⟨φb, hsb, hpb, hob⟩ := rocFrontier_attained_closed hm₀ hm₁ hi₀ hi₁ hn₀ hn₁ h₀ hβ
  rw [← hpa, ← hpb]
  exact hob φa (by rw [hsa]; exact hab)

theorem rocFrontier_concaveOn_closed {f₀ f₁ : Ω → ℝ}
    (hm₀ : Measurable f₀) (hm₁ : Measurable f₁)
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) : ConcaveOn ℝ (Icc 0 1) (rocFrontier ν f₀ f₁) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro α hα β hβ a b ha hb hab
  obtain ⟨φa, hsa, hpa, hoa⟩ := rocFrontier_attained_closed hm₀ hm₁ hi₀ hi₁ hn₀ hn₁ h₀ hα
  obtain ⟨φb, hsb, hpb, hob⟩ := rocFrontier_attained_closed hm₀ hm₁ hi₀ hi₁ hn₀ hn₁ h₀ hβ
  have hc : a * α + b * β ∈ Icc (0 : ℝ) 1 := by
    simpa only [smul_eq_mul] using (convex_Icc (0 : ℝ) 1) hα hβ ha hb hab
  obtain ⟨φc, hsc, hpc, hoc⟩ := rocFrontier_attained_closed hm₀ hm₁ hi₀ hi₁ hn₀ hn₁ h₀ hc
  have hs : (φa.mixture φb a b ha hb hab).densityPower ν f₀ = a * α + b * β := by
    rw [φa.densityPower_mixture φb hi₀, hsa, hsb]
  have hp := hoc (φa.mixture φb a b ha hb hab) hs.le
  rw [φa.densityPower_mixture φb hi₁, hpa, hpb, hpc] at hp
  simpa only [smul_eq_mul] using hp

/-- Every finite likelihood multiplier at an interior calibrated optimum is
a supergradient of the full ROC frontier, including comparisons to endpoints. -/
theorem rocFrontier_supporting_line {f₀ f₁ : Ω → ℝ}
    (hm₀ : Measurable f₀) (hm₁ : Measurable f₁)
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) (φ : StatisticalTest Ω)
    {k α β : ℝ} (hk : 0 ≤ k) (ht : φ.HasLikelihoodThreshold ν f₀ f₁ k)
    (hs : φ.densityPower ν f₀ = α) (hβ : β ∈ Icc (0 : ℝ) 1) :
    rocFrontier ν f₀ f₁ β ≤ rocFrontier ν f₀ f₁ α + k * (β - α) := by
  have hpa := rocFrontier_eq_of_optimal φ hs.le
    (fun ψ hψ => φ.neyman_pearson ψ hi₀ hi₁ hk ht (hψ.trans hs.ge))
  obtain ⟨ψ, hsb, hpb, hob⟩ := rocFrontier_attained_closed hm₀ hm₁ hi₀ hi₁ hn₀ hn₁ h₀ hβ
  rw [hpa, ← hpb, ← hsb]
  exact φ.likelihood_threshold_supporting_line ψ hi₀ hi₁ ht hs

/-- True-positive rates remain genuine probabilities throughout the frontier. -/
theorem rocFrontier_mem_unitInterval {f₀ f₁ : Ω → ℝ}
    (hm₀ : Measurable f₀) (hm₁ : Measurable f₁)
    (hi₀ : Integrable f₀ ν) (hi₁ : Integrable f₁ ν)
    (hn₀ : ∀ x, 0 ≤ f₀ x) (hn₁ : ∀ x, 0 ≤ f₁ x)
    (h₀ : (∫ x, f₀ x ∂ν) = 1) (h₁ : (∫ x, f₁ x ∂ν) = 1)
    {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) : rocFrontier ν f₀ f₁ α ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨φ, hs, hp, ho⟩ := rocFrontier_attained_closed hm₀ hm₁ hi₀ hi₁ hn₀ hn₁ h₀ hα
  rw [← hp, φ.densityPower_eq_power hm₁.aemeasurable (ae_of_all _ hn₁)]
  letI := density_model_isProbabilityMeasure hi₁ (ae_of_all _ hn₁) h₁
  exact ⟨φ.power_nonneg _, φ.power_le_one _⟩

end LectureNotes
