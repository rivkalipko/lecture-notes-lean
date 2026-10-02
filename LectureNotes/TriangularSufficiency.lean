import LectureNotes.UniformSufficiency
import LectureNotes.LikelihoodRatioSupport

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The strict-support density from L5 Example 16. -/
def triangularEndpointDensity (θ x : ℝ) : ℝ :=
  (Ioo 0 θ).indicator (fun x => 2 * x / θ ^ 2) x

def triangularEndpointLaw (θ : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (triangularEndpointDensity θ x))

theorem triangularEndpointDensity_measurable (θ : ℝ) :
    Measurable (triangularEndpointDensity θ) :=
  (by fun_prop : Measurable (fun x : ℝ => 2 * x / θ ^ 2)).indicator measurableSet_Ioo

theorem triangularEndpointDensity_nonneg (θ x : ℝ) : 0 ≤ triangularEndpointDensity θ x := by
  by_cases hx : x ∈ Ioo 0 θ
  · simp only [triangularEndpointDensity, indicator_of_mem hx]
    exact div_nonneg (mul_nonneg (by norm_num) hx.1.le) (sq_nonneg _)
  · simp [triangularEndpointDensity, indicator_of_notMem hx]

theorem triangularEndpointDensity_integrable (θ : ℝ) :
    Integrable (triangularEndpointDensity θ) volume := by
  exact ((by fun_prop : Continuous (fun x : ℝ => 2 * x / θ ^ 2)).integrableOn_Icc.mono_set
    Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo

theorem triangularEndpointDensity_integral {θ : ℝ} (hθ : 0 < θ) :
    (∫ x, triangularEndpointDensity θ x) = 1 := by
  unfold triangularEndpointDensity
  rw [integral_indicator measurableSet_Ioo, ← integral_Icc_eq_integral_Ioo,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hθ.le,
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_id]
  field_simp [hθ.ne']
  ring

theorem triangularEndpointLaw_probability {θ : ℝ} (hθ : 0 < θ) :
    IsProbabilityMeasure (triangularEndpointLaw θ) := by
  constructor
  rw [triangularEndpointLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (triangularEndpointDensity_integrable θ)
      (ae_of_all _ (triangularEndpointDensity_nonneg θ)), triangularEndpointDensity_integral hθ]
  norm_num

theorem triangularEndpoint_ae_support (θ : ℝ) :
    ∀ᵐ x ∂triangularEndpointLaw θ, x ∈ Ioo 0 θ := by
  change ∀ᵐ x ∂volume.withDensity (fun x => ENNReal.ofReal (triangularEndpointDensity θ x)), _
  rw [ae_withDensity_iff (triangularEndpointDensity_measurable θ).ennreal_ofReal]
  exact ae_of_all _ (fun x hx => by
    by_contra hnot
    simpa [triangularEndpointDensity, indicator_of_notMem hnot] using hx)

def triangularEndpointExperiment (n : ℕ) (θ : {θ : ℝ // 0 < θ}) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => triangularEndpointLaw θ.1)

instance triangularEndpointExperiment_probability (n : ℕ) (θ : {θ : ℝ // 0 < θ}) :
    IsProbabilityMeasure (triangularEndpointExperiment n θ) := by
  have : IsProbabilityMeasure (triangularEndpointLaw θ.1) := triangularEndpointLaw_probability θ.2
  exact inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => triangularEndpointLaw θ.1)))

theorem sampleMaximum_lt_iff {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (t : ℝ) :
    sampleMaximum x < t ↔ ∀ i, x i < t := by
  have : NeZero n := ⟨hn.ne'⟩
  constructor
  · exact fun h i => (le_sampleMaximum x i).trans_lt h
  · intro h
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := x)
    change x i = sampleMaximum x at hi
    rw [← hi]
    exact h i

theorem triangularEndpoint_product_factorization {n : ℕ} (hn : 0 < n)
    (θ : ℝ) (hθ : 0 < θ) (x : Fin n → ℝ) :
    (∏ i, ENNReal.ofReal (triangularEndpointDensity θ (x i))) =
      (if ∀ i, 0 < x i then ∏ i, ENNReal.ofReal (2 * x i) else 0) *
      (if sampleMaximum x < θ then ENNReal.ofReal ((1 / θ ^ 2) ^ n) else 0) := by
  classical
  by_cases hp : ∀ i, 0 < x i
  · rw [if_pos hp]
    by_cases hmax : sampleMaximum x < θ
    · rw [if_pos hmax]
      have hs i : x i ∈ Ioo 0 θ := ⟨hp i, (sampleMaximum_lt_iff hn x θ).mp hmax i⟩
      simp only [triangularEndpointDensity, indicator_of_mem (hs _), div_eq_mul_inv,
        one_mul]
      have hmul i : ENNReal.ofReal (2 * x i * (θ ^ 2)⁻¹) =
          ENNReal.ofReal (2 * x i) * ENNReal.ofReal ((θ ^ 2)⁻¹) :=
        ENNReal.ofReal_mul (mul_pos (by norm_num) (hp i)).le
      simp_rw [hmul]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ENNReal.ofReal_pow (by positivity)]
    · rw [if_neg hmax, mul_zero]
      have hf : ¬ ∀ i, x i < θ := fun h => hmax ((sampleMaximum_lt_iff hn x θ).mpr h)
      obtain ⟨i, hi⟩ := not_forall.mp hf
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [triangularEndpointDensity, show x i ∉ Ioo 0 θ from fun h => hi h.2]
  · rw [if_neg hp, zero_mul]
    obtain ⟨i, hi⟩ := not_forall.mp hp
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [triangularEndpointDensity, show x i ∉ Ioo 0 θ from fun h => hi h.1]

/-- The factorization in L5 Example 16 is applied to the actual iid law. -/
theorem triangularEndpoint_maximum_sufficient {n : ℕ} (hn : 0 < n) :
    IsSufficientStatistic (triangularEndpointExperiment n)
      (sampleMaximum : (Fin n → ℝ) → ℝ) := by
  classical
  letI (θ : {θ : ℝ // 0 < θ}) : IsProbabilityMeasure (triangularEndpointLaw θ.1) :=
    triangularEndpointLaw_probability θ.2
  have hf (θ : {θ : ℝ // 0 < θ}) : Measurable
      (fun x => ENNReal.ofReal (triangularEndpointDensity θ.1 x)) :=
    (triangularEndpointDensity_measurable θ.1).ennreal_ofReal
  apply sufficient_of_density_factorization_sigmaFinite
    (P := triangularEndpointExperiment n) (Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))
    (fun θ x => ∏ i, ENNReal.ofReal (triangularEndpointDensity θ.1 (x i)))
    (fun θ => (iid_product_withDensity volume (triangularEndpointLaw θ.1)
      (fun x => ENNReal.ofReal (triangularEndpointDensity θ.1 x)) (hf θ) rfl n).symm)
    (sampleMaximum_measurable (fun i x => x i) (by intro i; fun_prop))
    (fun x => if ∀ i, 0 < x i then ∏ i, ENNReal.ofReal (2 * x i) else 0)
    (Measurable.ite (by measurability) (by fun_prop) measurable_const)
    (ae_of_all _ (fun x => by
      split_ifs
      · exact ENNReal.prod_ne_top (fun i _ => ENNReal.ofReal_ne_top)
      · exact ENNReal.zero_ne_top))
  intro θ
  refine ⟨fun m => if m < θ.1 then ENNReal.ofReal ((1 / θ.1 ^ 2) ^ n) else 0,
    Measurable.ite measurableSet_Iio measurable_const measurable_const,
    ae_of_all _ (fun x => triangularEndpoint_product_factorization hn θ.1 θ.2 x)⟩

end LectureNotes
