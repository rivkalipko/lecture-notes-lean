import LectureNotes.UniformSufficiency
import LectureNotes.LikelihoodRatioSupport

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Minimal sufficiency of the maximum in the full positive uniform-endpoint
family. Positive rational endpoints recover the maximum from the zero sets of
countably many likelihood ratios relative to a dominating mixture. -/
theorem uniformEndpoint_maximum_minimal_sufficient {n : ℕ} (hn : 0 < n) :
    IsMinimalSufficientStatistic (uniformEndpointExperiment n)
      (sampleMaximum : (Fin n → ℝ) → ℝ) := by
  classical
  let ν : Measure (Fin n → ℝ) := Measure.pi (fun _ => (volume : Measure ℝ))
  let f (θ : {θ : ℝ // 0 < θ}) (x : Fin n → ℝ) :=
    ∏ i, ENNReal.ofReal (uniformEndpointDensity θ.1 (x i))
  letI (θ : {θ : ℝ // 0 < θ}) : IsProbabilityMeasure (uniformEndpointLaw θ.1) :=
    uniformEndpointLaw_probability θ.2
  have hd (θ : {θ : ℝ // 0 < θ}) : Measurable
      (fun x => ENNReal.ofReal (uniformEndpointDensity θ.1 x)) :=
    ENNReal.measurable_ofReal.comp (Measurable.ite measurableSet_Icc measurable_const measurable_const)
  have hf (θ : {θ : ℝ // 0 < θ}) : Measurable (f θ) := by
    dsimp only [f]
    exact Finset.measurable_prod _ (fun i _ => (hd θ).comp (measurable_pi_apply i))
  have hP (θ : {θ : ℝ // 0 < θ}) : ν.withDensity (f θ) = uniformEndpointExperiment n θ := by
    exact (iid_product_withDensity volume (uniformEndpointLaw θ.1)
      (fun x => ENNReal.ofReal (uniformEndpointDensity θ.1 x))
      (hd θ) (uniformEndpointLaw_density θ.2) n).symm
  have hdomν (θ : {θ : ℝ // 0 < θ}) : uniformEndpointExperiment n θ ≪ ν := by
    rw [← hP θ]
    exact withDensity_absolutelyContinuous _ _
  obtain ⟨ι, hcount, mixtureParameters, w, μ, hfinite, hmix, hμν, hdomμ⟩ :=
    exists_dominating_countable_mixture (uniformEndpointExperiment n) ν hdomν
  letI : Countable ι := hcount
  letI : IsFiniteMeasure μ := hfinite
  let parameters (q : {q : ℚ // 0 < q}) : {θ : ℝ // 0 < θ} :=
    ⟨q.1, by exact_mod_cast q.2⟩
  apply minimal_sufficient_of_mixture_ratio_recovery (uniformEndpointExperiment n)
    (uniformEndpoint_maximum_sufficient hn) μ mixtureParameters w hmix hdomμ
    parameters positiveRationalCutDecode positiveRationalCutDecode_measurable
  have hsuppθ (θ : {θ : ℝ // 0 < θ}) :
      ∀ᵐ x ∂uniformEndpointExperiment n θ, ∀ i, 0 < x i := by
    apply ae_all_iff.mpr
    intro i
    have hlaw : HasLaw (fun x : Fin n → ℝ => x i) (uniformEndpointLaw θ.1)
        (uniformEndpointExperiment n θ) :=
      (measurePreserving_eval (μ := fun _ : Fin n => uniformEndpointLaw θ.1) i).hasLaw
    have hs := (hlaw.ae_iff (show Measurable (fun x : ℝ => x ∈ Ioc 0 θ.1) by measurability)).mpr
      (uniformEndpoint_ae_support θ.1)
    exact hs.mono (fun x hx => hx.1)
  have hsupp : ∀ᵐ x ∂μ, ∀ i, 0 < x i := by
    rw [hmix]
    exact ae_mixture_of_ae_models (uniformEndpointExperiment n) mixtureParameters w hsuppθ
  have hratio : ∀ᵐ x ∂μ, ∀ q : {q : ℚ // 0 < q},
      (uniformEndpointExperiment n (parameters q)).rnDeriv μ x ≠ 0 ↔ f (parameters q) x ≠ 0 :=
    ae_all_iff.mpr (fun q => rnDeriv_nonzero_iff_density
      (uniformEndpointExperiment n (parameters q)) μ ν hμν (hdomμ (parameters q))
      (hf (parameters q)) (hP (parameters q)))
  filter_upwards [hsupp, hratio] with x hx hr
  apply positiveRationalCutDecode_recover
    ((hx ⟨0, hn⟩).trans_le (le_sampleMaximum x ⟨0, hn⟩))
  intro q
  rw [hr q]
  dsimp only [f, parameters]
  rw [uniformEndpoint_product_factorization hn (q.1 : ℝ) (by exact_mod_cast q.2),
    if_pos (fun i => (hx i).le), one_mul]
  have hc : ENNReal.ofReal ((1 / (q.1 : ℝ)) ^ n) ≠ 0 := by
    apply (ENNReal.ofReal_pos.mpr _).ne'
    have hq : (0 : ℝ) < q.1 := by exact_mod_cast q.2
    positivity
  by_cases hq : sampleMaximum x ≤ (q.1 : ℝ)
  · rw [if_pos hq]
    exact iff_of_true hc hq
  · simp [hq]

end LectureNotes
