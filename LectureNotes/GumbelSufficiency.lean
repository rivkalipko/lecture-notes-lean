import LectureNotes.ExponentialFamilySufficiency
import LectureNotes.MinimalSufficiency

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

def gumbelLocationDensity (θ x : ℝ) : ℝ :=
  Real.exp (-(x - θ)) * Real.exp (-Real.exp (-(x - θ)))

def gumbelLocationLaw (θ : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (gumbelLocationDensity θ x))

theorem gumbelLocationDensity_pos (θ x : ℝ) : 0 < gumbelLocationDensity θ x :=
  mul_pos (Real.exp_pos _) (Real.exp_pos _)

theorem gumbelLocationDensity_measurable (θ : ℝ) : Measurable (gumbelLocationDensity θ) := by
  unfold gumbelLocationDensity
  fun_prop

theorem gumbelLocationDensity_integrable_integral (θ : ℝ) :
    Integrable (gumbelLocationDensity θ) volume ∧ (∫ x, gumbelLocationDensity θ x) = 1 := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x - θ))
  have hd x : HasDerivAt f (-Real.exp (-(x - θ))) x := by
    convert (((hasDerivAt_id x).sub_const θ).neg.exp) using 1 <;> simp [f]
  have hinj : InjOn f univ := by
    intro x _ y _ hxy
    have h : -(x - θ) = -(y - θ) := Real.exp_injective hxy
    linarith
  have himage : f '' univ = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, _, rfl⟩
      exact Real.exp_pos _
    · intro hy
      refine ⟨θ - Real.log y, mem_univ _, ?_⟩
      dsimp only [f]
      rw [show -(θ - Real.log y - θ) = Real.log y by ring, Real.exp_log hy]
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hd x).hasDerivWithinAt) hinj (fun y : ℝ => Real.exp (-y))
  rw [himage] at hi
  have hi' := hi.mp (integrableOn_exp_neg_Ioi 0)
  have he := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hd x).hasDerivWithinAt) hinj (fun y : ℝ => Real.exp (-y))
  rw [himage, integral_exp_neg_Ioi_zero] at he
  constructor
  · change Integrable (fun x => Real.exp (-(x - θ)) * Real.exp (-Real.exp (-(x - θ)))) volume
    simpa only [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul,
      integrableOn_univ, f, gumbelLocationDensity] using hi'
  · simpa only [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul,
      Measure.restrict_univ, f, gumbelLocationDensity] using he.symm

instance gumbelLocationLaw_probability (θ : ℝ) : IsProbabilityMeasure (gumbelLocationLaw θ) := by
  constructor
  rw [gumbelLocationLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (gumbelLocationDensity_integrable_integral θ).1
      (ae_of_all _ (fun x => (gumbelLocationDensity_pos θ x).le)),
    (gumbelLocationDensity_integrable_integral θ).2]
  norm_num

def gumbelLocationExperiment (n : ℕ) (θ : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gumbelLocationLaw θ)

instance gumbelLocationExperiment_probability (n : ℕ) (θ : ℝ) :
    IsProbabilityMeasure (gumbelLocationExperiment n θ) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => gumbelLocationLaw θ)))

def gumbelCanonicalStatistic {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, Real.exp (-x i)

theorem gumbel_location_density_ratio (θ x : ℝ) :
    gumbelLocationDensity θ x = gumbelLocationDensity 0 x *
      Real.exp (θ - (Real.exp θ - 1) * Real.exp (-x)) := by
  have he : Real.exp (-(x - θ)) = Real.exp θ * Real.exp (-x) := by
    rw [show -(x - θ) = θ + -x by ring, Real.exp_add]
  unfold gumbelLocationDensity
  simp only [sub_zero, ← Real.exp_add]
  congr 1
  rw [he]
  ring

theorem gumbel_location_product_factorization {n : ℕ} (θ : ℝ) (x : Fin n → ℝ) :
    (∏ i, ENNReal.ofReal (gumbelLocationDensity θ (x i))) =
      (∏ i, ENNReal.ofReal (gumbelLocationDensity 0 (x i))) *
        ENNReal.ofReal (Real.exp (n * θ - (Real.exp θ - 1) * gumbelCanonicalStatistic x)) := by
  have he : (∏ i, gumbelLocationDensity θ (x i)) =
      (∏ i, gumbelLocationDensity 0 (x i)) *
        Real.exp (n * θ - (Real.exp θ - 1) * gumbelCanonicalStatistic x) := by
    have hi (i : Fin n) := gumbel_location_density_ratio θ (x i)
    simp_rw [hi]
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    congr 2
    simp only [gumbelCanonicalStatistic, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (gumbelLocationDensity_pos _ _).le),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => (gumbelLocationDensity_pos _ _).le)), he]

theorem gumbel_location_product_density (n : ℕ) (θ : ℝ) :
    (volume : Measure (Fin n → ℝ)).withDensity
      (fun x => ∏ i, ENNReal.ofReal (gumbelLocationDensity θ (x i))) = gumbelLocationExperiment n θ :=
  (iid_product_withDensity volume (gumbelLocationLaw θ)
    (fun x => ENNReal.ofReal (gumbelLocationDensity θ x))
    (gumbelLocationDensity_measurable θ).ennreal_ofReal rfl n).symm

/-- L5 Example 17: the sum of exp(-Xi) is sufficient in the actual Gumbel
location experiment, with the normalization of its continuous density proved. -/
theorem gumbel_canonical_sufficient (n : ℕ) :
    IsSufficientStatistic (gumbelLocationExperiment n) (gumbelCanonicalStatistic : (Fin n → ℝ) → ℝ) := by
  apply sufficient_of_density_factorization (P := gumbelLocationExperiment n)
    volume (0 : ℝ) (fun θ x => ∏ i, ENNReal.ofReal (gumbelLocationDensity θ (x i)))
    (by
      intro θ
      exact Finset.measurable_prod _ (fun i _ =>
        ((gumbelLocationDensity_measurable θ).comp (measurable_pi_apply i)).ennreal_ofReal))
    (gumbel_location_product_density n) (by unfold gumbelCanonicalStatistic; fun_prop)
    (fun θ t => ENNReal.ofReal (Real.exp (n * θ - (Real.exp θ - 1) * t))) (by intro θ; fun_prop)
  exact fun θ => ae_of_all _ (gumbel_location_product_factorization θ)

theorem gumbel_location_reference_density (n : ℕ) (θ : ℝ) :
    (gumbelLocationExperiment n 0).withDensity
      (fun x => ENNReal.ofReal (Real.exp (n * θ - (Real.exp θ - 1) * gumbelCanonicalStatistic x))) =
      gumbelLocationExperiment n θ := by
  rw [← gumbel_location_product_density n 0, ← gumbel_location_product_density n θ,
    ← withDensity_mul _
      (f := fun x : Fin n → ℝ => ∏ i, ENNReal.ofReal (gumbelLocationDensity 0 (x i)))
      (g := fun x => ENNReal.ofReal
        (Real.exp (n * θ - (Real.exp θ - 1) * gumbelCanonicalStatistic x)))
      (Finset.measurable_prod _ (fun i _ =>
        ((gumbelLocationDensity_measurable 0).comp (measurable_pi_apply i)).ennreal_ofReal))
      (by unfold gumbelCanonicalStatistic; fun_prop)]
  exact withDensity_congr_ae (ae_of_all _ (fun x => (gumbel_location_product_factorization θ x).symm))

/-- A single nonzero location contrast measurably recovers the canonical sum,
so it is minimal sufficient among all standard Borel sufficient statistics. -/
theorem gumbel_canonical_minimal_sufficient (n : ℕ) :
    IsMinimalSufficientStatistic (gumbelLocationExperiment n)
      (gumbelCanonicalStatistic : (Fin n → ℝ) → ℝ) := by
  have hdom θ : gumbelLocationExperiment n θ ≪ gumbelLocationExperiment n 0 := by
    rw [← gumbel_location_reference_density n θ]
    exact withDensity_absolutelyContinuous _ _
  let decode (r : Fin 1 → ℝ≥0∞) := (n - Real.log (r 0).toReal) / (Real.exp 1 - 1)
  apply minimal_sufficient_of_likelihood_ratio_recovery (gumbelLocationExperiment n)
    (gumbel_canonical_sufficient n) 0 hdom (fun _ : Fin 1 => (1 : ℝ)) decode
    (by dsimp only [decode]; fun_prop)
  have hr : (gumbelLocationExperiment n 1).rnDeriv (gumbelLocationExperiment n 0) =ᵐ[
      gumbelLocationExperiment n 0]
      (fun x => ENNReal.ofReal (Real.exp (n - (Real.exp 1 - 1) * gumbelCanonicalStatistic x))) := by
    have h := Measure.rnDeriv_withDensity (gumbelLocationExperiment n 0)
      (show Measurable (fun x : Fin n → ℝ => ENNReal.ofReal
        (Real.exp (n * 1 - (Real.exp 1 - 1) * gumbelCanonicalStatistic x))) by
        unfold gumbelCanonicalStatistic; fun_prop)
    rw [gumbel_location_reference_density] at h
    simpa only [mul_one] using h
  filter_upwards [hr] with x hx
  dsimp only [decode]
  rw [hx, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]
  have hc : Real.exp 1 - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr (by norm_num)))
  field_simp
  ring

end LectureNotes
