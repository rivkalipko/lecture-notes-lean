import LectureNotes.CauchyPolynomial
import LectureNotes.ExponentialFamilySufficiency

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The Cauchy location experiment of L5 Example 15, with unit scale. -/
def cauchyLocationExperiment (n : ℕ) (θ : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => cauchyMeasure θ 1)

instance cauchyLocationExperiment_probability (n : ℕ) (θ : ℝ) :
    IsProbabilityMeasure (cauchyLocationExperiment n θ) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => cauchyMeasure θ 1)))

theorem cauchySampleDenominator_sorted {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) :
    cauchySampleDenominator (sortedSample x).val θ = cauchySampleDenominator x θ :=
  sortedSample_prod (fun t => (θ - t) ^ 2 + 1) x

theorem cauchy_location_real_product {n : ℕ} (θ : ℝ) (x : Fin n → ℝ) :
    (∏ i, cauchyPDFReal θ 1 (x i)) = (Real.pi⁻¹) ^ n * (cauchySampleDenominator x θ)⁻¹ := by
  simp only [cauchyPDFReal_def, NNReal.coe_one, mul_one, one_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_inv_distrib]
  congr 2
  unfold cauchySampleDenominator
  apply Finset.prod_congr rfl
  intro i _
  rw [sub_sq_comm]

theorem cauchy_location_product_factorization {n : ℕ} (θ : ℝ) (x : Fin n → ℝ) :
    (∏ i, ENNReal.ofReal (cauchyPDFReal θ 1 (x i))) =
      (∏ i, ENNReal.ofReal (cauchyPDFReal 0 1 (x i))) *
        ENNReal.ofReal (cauchySampleDenominator x 0 / cauchySampleDenominator x θ) := by
  have he : (∏ i, cauchyPDFReal θ 1 (x i)) = (∏ i, cauchyPDFReal 0 1 (x i)) *
      (cauchySampleDenominator x 0 / cauchySampleDenominator x θ) := by
    rw [cauchy_location_real_product, cauchy_location_real_product]
    field_simp [(cauchySampleDenominator_pos x 0).ne', (cauchySampleDenominator_pos x θ).ne']
  simp only [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (cauchyPDF_pos _ one_ne_zero _).le),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => (cauchyPDF_pos _ one_ne_zero _).le)), he]

theorem cauchy_location_product_density (n : ℕ) (θ : ℝ) :
    (volume : Measure (Fin n → ℝ)).withDensity
      (fun x => ∏ i, ENNReal.ofReal (cauchyPDFReal θ 1 (x i))) = cauchyLocationExperiment n θ := by
  have hbase : volume.withDensity (fun x => ENNReal.ofReal (cauchyPDFReal θ 1 x)) = cauchyMeasure θ 1 := by
    rw [cauchyMeasure_of_scale_ne_zero θ one_ne_zero]
    rfl
  exact (iid_product_withDensity volume (cauchyMeasure θ 1)
    (fun x => ENNReal.ofReal (cauchyPDFReal θ 1 x))
    (measurable_cauchyPDFReal θ 1).ennreal_ofReal hbase n).symm

theorem cauchy_location_reference_density (n : ℕ) (θ : ℝ) :
    (cauchyLocationExperiment n 0).withDensity
      (fun x => ENNReal.ofReal (cauchySampleDenominator x 0 / cauchySampleDenominator x θ)) =
      cauchyLocationExperiment n θ := by
  rw [← cauchy_location_product_density n 0, ← cauchy_location_product_density n θ,
    ← withDensity_mul _
      (f := fun x : Fin n → ℝ => ∏ i, ENNReal.ofReal (cauchyPDFReal 0 1 (x i)))
      (g := fun x => ENNReal.ofReal (cauchySampleDenominator x 0 / cauchySampleDenominator x θ))
      (Finset.measurable_prod _ (fun i _ =>
        ((measurable_cauchyPDFReal 0 1).comp (measurable_pi_apply i)).ennreal_ofReal))
      (by unfold cauchySampleDenominator; fun_prop)]
  exact withDensity_congr_ae (ae_of_all _ (fun x => (cauchy_location_product_factorization θ x).symm))

theorem cauchySampleDenominator_measurable_sorted {n : ℕ} (θ : ℝ) :
    Measurable (fun s : SortedSample n => cauchySampleDenominator s.val θ) := by
  unfold cauchySampleDenominator
  apply Finset.measurable_prod
  intro i _
  have hi : Measurable (fun s : SortedSample n => s.val i) :=
    (measurable_pi_apply i).comp measurable_subtype_coe
  exact ((measurable_const.sub hi).pow_const 2).add_const 1

/-- The full ordered sample is sufficient in the actual Cauchy location family. -/
theorem cauchy_orderStatistics_sufficient (n : ℕ) :
    IsSufficientStatistic (cauchyLocationExperiment n) (sortedSample : (Fin n → ℝ) → SortedSample n) := by
  apply sufficient_of_reference_factorization (cauchyLocationExperiment n 0) sortedSample_measurable
  intro θ
  refine ⟨fun s : SortedSample n => ENNReal.ofReal
    (cauchySampleDenominator s.val 0 / cauchySampleDenominator s.val θ),
    ((cauchySampleDenominator_measurable_sorted 0).div
      (cauchySampleDenominator_measurable_sorted θ)).ennreal_ofReal, ?_⟩
  simpa only [cauchySampleDenominator_sorted] using cauchy_location_reference_density n θ

/-- L5 Example 15: all order statistics are minimal sufficient for Cauchy
location. Countably many actual likelihood ratios recover the sorted sample;
complex polynomial factors certify injectivity, including multiplicities. -/
theorem cauchy_orderStatistics_minimal_sufficient (n : ℕ) :
    IsMinimalSufficientStatistic (cauchyLocationExperiment n)
      (sortedSample : (Fin n → ℝ) → SortedSample n) := by
  have hdom θ : cauchyLocationExperiment n θ ≪ cauchyLocationExperiment n 0 := by
    rw [← cauchy_location_reference_density n θ]
    exact withDensity_absolutelyContinuous _ _
  let g (s : SortedSample n) (k : ℕ) :=
    ENNReal.ofReal (cauchySampleDenominator s.val 0 / cauchySampleDenominator s.val k)
  have hg : Measurable g := by
    dsimp only [g]
    exact measurable_pi_lambda _ (fun k =>
      ((cauchySampleDenominator_measurable_sorted 0).div
        (cauchySampleDenominator_measurable_sorted k)).ennreal_ofReal)
  have hginj : Function.Injective g := by
    intro s t h
    apply Subtype.ext
    apply cauchy_ratios_injective_on_sorted s.property t.property
    intro k
    have hk := congrArg ENNReal.toReal (congrFun h k)
    dsimp only [g] at hk
    simpa only [ENNReal.toReal_ofReal
      (div_pos (cauchySampleDenominator_pos _ 0) (cauchySampleDenominator_pos _ k)).le] using hk
  apply minimal_sufficient_of_injective_ratio_representation (cauchyLocationExperiment n)
    (cauchy_orderStatistics_sufficient n) 0 hdom (fun k : ℕ => (k : ℝ)) g hg hginj
  intro k
  have h := Measure.rnDeriv_withDensity (cauchyLocationExperiment n 0)
    (show Measurable (fun x : Fin n → ℝ =>
      ENNReal.ofReal (cauchySampleDenominator x 0 / cauchySampleDenominator x k)) by
      unfold cauchySampleDenominator; fun_prop)
  rw [cauchy_location_reference_density] at h
  simpa only [g, cauchySampleDenominator_sorted] using h

end LectureNotes
