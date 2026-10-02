import LectureNotes.SigmaFiniteFactorization
import LectureNotes.ExponentialFamilySufficiency
import LectureNotes.UniformEndpoint

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The full continuous sample experiment for a positive unknown upper endpoint. -/
def uniformEndpointExperiment (n : ℕ) (θ : {θ : ℝ // 0 < θ}) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => uniformEndpointLaw θ.1)

instance uniformEndpointExperiment_probability (n : ℕ) (θ : {θ : ℝ // 0 < θ}) :
    IsProbabilityMeasure (uniformEndpointExperiment n θ) := by
  have := uniformEndpointLaw_probability θ.2
  unfold uniformEndpointExperiment
  infer_instance

/-- The parameter-dependent support enters through the sample maximum, while
the common nonnegative support is retained in the carrier. -/
theorem uniformEndpoint_product_factorization {n : ℕ} (hn : 0 < n)
    (θ : ℝ) (hθ : 0 < θ) (x : Fin n → ℝ) :
    (∏ i, ENNReal.ofReal (uniformEndpointDensity θ (x i))) =
      (if ∀ i, 0 ≤ x i then (1 : ℝ≥0∞) else 0) *
      (if sampleMaximum x ≤ θ then ENNReal.ofReal ((1 / θ) ^ n) else 0) := by
  classical
  by_cases hnonneg : ∀ i, 0 ≤ x i
  · rw [if_pos hnonneg, one_mul]
    by_cases hmax : sampleMaximum x ≤ θ
    · have hfit (i) : x i ∈ Icc 0 θ := ⟨hnonneg i,
        (sampleMaximum_le_iff hn x θ).mp hmax i⟩
      simp only [uniformEndpointDensity, if_pos (hfit _), if_pos hmax,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact (ENNReal.ofReal_pow (by positivity) n).symm
    · rw [if_neg hmax]
      have hx : ¬ ∀ i, x i ≤ θ := fun h => hmax ((sampleMaximum_le_iff hn x θ).mpr h)
      obtain ⟨i, hi⟩ := not_forall.mp hx
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [uniformEndpointDensity, show x i ∉ Icc 0 θ from fun h => hi h.2]
  · rw [if_neg hnonneg, zero_mul]
    obtain ⟨i, hi⟩ := not_forall.mp hnonneg
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [uniformEndpointDensity, show x i ∉ Icc 0 θ from fun h => hi h.1]

/-- The sample maximum is sufficient for the whole unbounded positive endpoint
family, despite its parameter-dependent support. -/
theorem uniformEndpoint_maximum_sufficient {n : ℕ} (hn : 0 < n) :
    IsSufficientStatistic (uniformEndpointExperiment n)
      (sampleMaximum : (Fin n → ℝ) → ℝ) := by
  classical
  letI (θ : {θ : ℝ // 0 < θ}) : IsProbabilityMeasure (uniformEndpointLaw θ.1) :=
    uniformEndpointLaw_probability θ.2
  have hf (θ : {θ : ℝ // 0 < θ}) : Measurable
      (fun x => ENNReal.ofReal (uniformEndpointDensity θ.1 x)) := by
    exact ENNReal.measurable_ofReal.comp
      (Measurable.ite measurableSet_Icc measurable_const measurable_const)
  apply sufficient_of_density_factorization_sigmaFinite
    (P := uniformEndpointExperiment n) (Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))
    (fun θ x => ∏ i, ENNReal.ofReal (uniformEndpointDensity θ.1 (x i)))
    (fun θ => (iid_product_withDensity volume (uniformEndpointLaw θ.1)
      (fun x => ENNReal.ofReal (uniformEndpointDensity θ.1 x)) (hf θ)
      (uniformEndpointLaw_density θ.2) n).symm)
    (sampleMaximum_measurable (fun i x => x i) (by intro i; fun_prop))
    (fun x => if ∀ i, 0 ≤ x i then (1 : ℝ≥0∞) else 0)
    (Measurable.ite (by measurability) measurable_const measurable_const)
    (ae_of_all _ (fun x => by split_ifs <;> simp))
  intro θ
  refine ⟨fun m => if m ≤ θ.1 then ENNReal.ofReal ((1 / θ.1) ^ n) else 0,
    Measurable.ite measurableSet_Iic measurable_const measurable_const, ae_of_all _ (fun x => uniformEndpoint_product_factorization hn θ.1 θ.2 x)⟩

/-- The translated unit-interval law of L5 Example 13. -/
def uniformLocationLaw (θ : ℝ) : Measure ℝ := volume.restrict (Icc θ (θ + 1))

instance uniformLocationLaw_probability (θ : ℝ) : IsProbabilityMeasure (uniformLocationLaw θ) := by
  constructor
  simp [uniformLocationLaw, Real.volume_Icc]

/-- The sample minimum, with empty-sample behavior inherited from real infima. -/
def sampleMinimum {n : ℕ} (x : Fin n → ℝ) : ℝ := ⨅ i, x i

theorem sampleMinimum_ge_iff {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (t : ℝ) :
    t ≤ sampleMinimum x ↔ ∀ i, t ≤ x i := by
  have : NeZero n := ⟨hn.ne'⟩
  exact le_ciInf_iff (Finite.bddBelow_range x)

/-- The likelihood indicator for a translated uniform sample. -/
theorem uniformLocation_product_factorization {n : ℕ} (hn : 0 < n)
    (θ : ℝ) (x : Fin n → ℝ) :
    (∏ i, (Icc θ (θ + 1)).indicator (1 : ℝ → ℝ≥0∞) (x i)) =
      if θ ≤ sampleMinimum x ∧ sampleMaximum x ≤ θ + 1 then 1 else 0 := by
  classical
  by_cases hh : θ ≤ sampleMinimum x ∧ sampleMaximum x ≤ θ + 1
  · have hfit (i) : x i ∈ Icc θ (θ + 1) :=
      ⟨(sampleMinimum_ge_iff hn x θ).mp hh.1 i, (sampleMaximum_le_iff hn x (θ + 1)).mp hh.2 i⟩
    simp [hh, hfit]
  · rw [if_neg hh]
    have hbad : ¬ ∀ i, x i ∈ Icc θ (θ + 1) := by
      intro h
      exact hh ⟨(sampleMinimum_ge_iff hn x θ).mpr (fun i => (h i).1),
        (sampleMaximum_le_iff hn x (θ + 1)).mpr (fun i => (h i).2)⟩
    obtain ⟨i, hi⟩ := not_forall.mp hbad
    exact Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)

/-- L5 Example 13 on the actual product measure: the minimum and maximum are
sufficient for the location of the translated unit interval. -/
theorem uniformLocation_extremes_sufficient {n : ℕ} (hn : 0 < n) :
    IsSufficientStatistic (fun θ : ℝ => Measure.pi (fun _ : Fin n => uniformLocationLaw θ))
      (fun x : Fin n → ℝ => (sampleMinimum x, sampleMaximum x)) := by
  classical
  have hP (θ : ℝ) : volume.withDensity ((Icc θ (θ + 1)).indicator (1 : ℝ → ℝ≥0∞)) =
      uniformLocationLaw θ := by
    rw [withDensity_indicator measurableSet_Icc, withDensity_one]
    rfl
  apply sufficient_of_sigmaFinite_reference_factorization
    (P := fun θ : ℝ => Measure.pi (fun _ : Fin n => uniformLocationLaw θ))
    (Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))
    ((Measurable.iInf (fun i : Fin n => measurable_pi_apply i)).prodMk
      (sampleMaximum_measurable (fun i x => x i) (by intro i; fun_prop)))
  intro θ
  refine ⟨fun s : ℝ × ℝ => if θ ≤ s.1 ∧ s.2 ≤ θ + 1 then 1 else 0,
    Measurable.ite (by measurability) measurable_const measurable_const, ?_⟩
  rw [iid_product_withDensity volume (uniformLocationLaw θ)
    ((Icc θ (θ + 1)).indicator (1 : ℝ → ℝ≥0∞))
    (measurable_one.indicator measurableSet_Icc) (hP θ) n]
  apply withDensity_congr_ae
  exact ae_of_all _ (fun x => (uniformLocation_product_factorization hn θ x).symm)

end LectureNotes
