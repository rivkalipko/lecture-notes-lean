import LectureNotes.BayesianUpdating

set_option autoImplicit false

/-! L12 beta conjugacy as equality of posterior probability measures.
The beta density is supported on (0,1); changing endpoint values does not
change the distribution. Success and failure counts are natural numbers. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- Updating a prior with a density is equivalent to normalizing the product
of its density and the likelihood against the reference measure. -/
theorem bayesUpdate_withDensity {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) (p L : Θ → ℝ) (hp : Measurable p) (hL : Measurable L)
    (hp0 : ∀ θ, 0 ≤ p θ) :
    bayesUpdate (ν.withDensity (fun θ => ENNReal.ofReal (p θ))) L =
      bayesUpdate ν (fun θ => p θ * L θ) := by
  have he : evidence (ν.withDensity (fun θ => ENNReal.ofReal (p θ))) L =
      evidence ν (fun θ => p θ * L θ) := by
    unfold evidence
    rw [integral_withDensity_eq_integral_toReal_smul₀ hp.ennreal_ofReal.aemeasurable
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hp0 _), smul_eq_mul]
  unfold bayesUpdate
  rw [he, ← withDensity_mul ν hp.ennreal_ofReal (hL.div_const _).ennreal_ofReal]
  congr 1
  funext θ
  change ENNReal.ofReal (p θ) * ENNReal.ofReal (L θ / _) = _
  rw [← ENNReal.ofReal_mul (hp0 θ), mul_div_assoc]

theorem beta_density_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    0 ≤ betaPDFReal a b x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact (betaPDFReal_pos hx.1 hx.2 ha hb).le
  · simp [betaPDFReal, hx]

theorem beta_density_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (betaPDFReal a b) volume := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_betaPDFReal a b).aestronglyMeasurable
    (ae_of_all _ (beta_density_nonneg ha hb))).mp
  change (∫⁻ x, betaPDF a b x) ≠ ⊤
  rw [lintegral_betaPDF_eq_one ha hb]
  norm_num

theorem beta_density_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x, betaPDFReal a b x) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (beta_density_nonneg ha hb))
    (measurable_betaPDFReal a b).aestronglyMeasurable]
  change (∫⁻ x, betaPDF a b x).toReal = 1
  rw [lintegral_betaPDF_eq_one ha hb]
  norm_num

theorem normalized_beta_density {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    bayesUpdate volume (betaPDFReal a b) = betaMeasure a b := by
  have he : evidence volume (betaPDFReal a b) = 1 := beta_density_integral ha hb
  rw [bayesUpdate, he]
  simp only [div_one]
  rfl

/-- Multiplication by the Bernoulli sample likelihood shifts the two beta
shape parameters by the numbers of successes and failures. -/
theorem beta_likelihood_product (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (s f : ℕ) (x : ℝ) :
    betaPDFReal a b x * (x ^ s * (1 - x) ^ f) =
      (beta (a + s) (b + f) / beta a b) * betaPDFReal (a + s) (b + f) x := by
  by_cases hx : 0 < x ∧ x < 1
  · have hbnew : beta (a + s) (b + f) ≠ 0 := (beta_pos (by positivity) (by positivity)).ne'
    have hbold : beta a b ≠ 0 := (beta_pos ha hb).ne'
    simp only [betaPDFReal, if_pos hx]
    rw [show a + (s : ℝ) - 1 = (a - 1) + s by ring,
      show b + (f : ℝ) - 1 = (b - 1) + f by ring,
      Real.rpow_add hx.1, Real.rpow_add (by linarith : 0 < 1 - x),
      Real.rpow_natCast, Real.rpow_natCast]
    field_simp
    <;> ring
  · simp [betaPDFReal, hx]

/-- Exact beta–Bernoulli/binomial conjugacy. Parameter-independent binomial
coefficients cancel by `bayesUpdate_scale`. -/
theorem beta_bernoulli_conjugacy (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (s f : ℕ) :
    bayesUpdate (betaMeasure a b) (fun x => x ^ s * (1 - x) ^ f) =
      betaMeasure (a + s) (b + f) := by
  change bayesUpdate (volume.withDensity (fun x => ENNReal.ofReal (betaPDFReal a b x)))
    (fun x => x ^ s * (1 - x) ^ f) = _
  rw [bayesUpdate_withDensity volume _ _
    (measurable_betaPDFReal a b) (by fun_prop) (beta_density_nonneg ha hb)]
  simp_rw [beta_likelihood_product a b ha hb s f]
  rw [bayesUpdate_scale _ _ (div_ne_zero (beta_pos (by positivity) (by positivity)).ne'
    (beta_pos ha hb).ne')]
  exact normalized_beta_density (by positivity) (by positivity)

/-- All nonnegative integer moments reduce to ratios of beta normalizers. -/
theorem beta_moment (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    (∫ x, x ^ k ∂betaMeasure a b) = beta (a + k) b / beta a b := by
  change (∫ x, x ^ k ∂volume.withDensity (fun x => ENNReal.ofReal (betaPDFReal a b x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (measurable_betaPDFReal a b).ennreal_ofReal.aemeasurable
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (beta_density_nonneg ha hb _), smul_eq_mul]
  have hprod x : betaPDFReal a b x * x ^ k =
      (beta (a + k) b / beta a b) * betaPDFReal (a + k) b x := by
    simpa using beta_likelihood_product a b ha hb k 0 x
  simp_rw [hprod]
  rw [integral_const_mul, beta_density_integral (by positivity) hb, mul_one]

theorem beta_power_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    Integrable (fun x => x ^ k) (betaMeasure a b) := by
  change Integrable (fun x => x ^ k)
    (volume.withDensity (fun x => ENNReal.ofReal (betaPDFReal a b x)))
  rw [integrable_withDensity_iff_integrable_smul₀'
    (measurable_betaPDFReal a b).ennreal_ofReal.aemeasurable
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (beta_density_nonneg ha hb _), smul_eq_mul]
  have hprod : (fun x => betaPDFReal a b x * x ^ k) =
      fun x => (beta (a + k) b / beta a b) * betaPDFReal (a + k) b x := by
    funext x
    simpa using beta_likelihood_product a b ha hb k 0 x
  rw [hprod]
  exact (beta_density_integrable (by positivity) hb).const_mul _

/-- The beta normalizer recurrence, derived from the Gamma recurrence. -/
theorem beta_step (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    beta (a + 1) b = a / (a + b) * beta a b := by
  unfold beta
  rw [show a + 1 + b = (a + b) + 1 by ring,
    Real.Gamma_add_one ha.ne', Real.Gamma_add_one (add_pos ha hb).ne']
  field_simp

theorem beta_mean (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x, x ∂betaMeasure a b) = a / (a + b) := by
  have h := beta_moment a b ha hb 1
  simp only [pow_one, Nat.cast_one] at h
  rw [h, beta_step a b ha hb]
  exact mul_div_cancel_right₀ _ (beta_pos ha hb).ne'

theorem beta_second_moment (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x, x ^ 2 ∂betaMeasure a b) = a * (a + 1) / ((a + b) * (a + b + 1)) := by
  rw [beta_moment a b ha hb 2]
  norm_num only [Nat.cast_ofNat]
  rw [show a + 2 = (a + 1) + 1 by ring,
    beta_step (a + 1) b (by positivity) hb, beta_step a b ha hb]
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  have hab1 : a + b + 1 ≠ 0 := by positivity
  have hab2 : a + 1 + b ≠ 0 := by positivity
  have hbeta : beta a b ≠ 0 := (beta_pos ha hb).ne'
  field_simp
  <;> ring

theorem beta_variance (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Var[id; betaMeasure a b] = a * b / ((a + b) ^ 2 * (a + b + 1)) := by
  letI := isProbabilityMeasureBeta ha hb
  have h₂ : MemLp (id : ℝ → ℝ) 2 (betaMeasure a b) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (beta_power_integrable a b ha hb 2)
  rw [variance_eq_sub h₂]
  change (∫ x, x ^ 2 ∂betaMeasure a b) - (∫ x, x ∂betaMeasure a b) ^ 2 = _
  rw [beta_second_moment a b ha hb, beta_mean a b ha hb]
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  have hab1 : a + b + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- The prior predictive probability of a particular binary sample, with
parameter-independent combinatorial factors omitted for a count statistic. -/
theorem beta_predictive_evidence (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (s f : ℕ) :
    evidence (betaMeasure a b) (fun x => x ^ s * (1 - x) ^ f) =
      beta (a + s) (b + f) / beta a b := by
  change (∫ x, x ^ s * (1 - x) ^ f ∂volume.withDensity
    (fun x => ENNReal.ofReal (betaPDFReal a b x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (measurable_betaPDFReal a b).ennreal_ofReal.aemeasurable
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (beta_density_nonneg ha hb _), smul_eq_mul]
  simp_rw [beta_likelihood_product a b ha hb s f]
  rw [integral_const_mul, beta_density_integral (by positivity) (by positivity), mul_one]

/-- Beta(1,1) is the actual uniform probability measure on [0,1]. The endpoint
values of the density make no difference to the measure. -/
theorem beta_one_one_uniform : betaMeasure 1 1 = volume.restrict (Icc 0 1) := by
  have hpdf : betaPDF 1 1 = (Ioo (0 : ℝ) 1).indicator 1 := by
    funext x
    by_cases hx : 0 < x ∧ x < 1
    · simp [betaPDF, betaPDFReal, hx, beta, Real.Gamma_add_one,
        Set.indicator_of_mem hx]
    · simp [betaPDF, betaPDFReal, hx, Set.indicator_of_notMem hx]
  rw [betaMeasure, hpdf, withDensity_indicator_one measurableSet_Ioo,
    restrict_Ioo_eq_restrict_Icc]

theorem uniform_bernoulli_posterior (s f : ℕ) :
    bayesUpdate (volume.restrict (Icc (0 : ℝ) 1)) (fun x => x ^ s * (1 - x) ^ f) =
      betaMeasure (s + 1) (f + 1) := by
  rw [← beta_one_one_uniform]
  simpa [add_comm] using beta_bernoulli_conjugacy 1 1 (by norm_num) (by norm_num) s f

theorem uniform_bernoulli_posterior_mean (s f : ℕ) :
    (∫ x, x ∂bayesUpdate (volume.restrict (Icc (0 : ℝ) 1))
      (fun x => x ^ s * (1 - x) ^ f)) = ((s : ℝ) + 1) / (s + f + 2) := by
  rw [uniform_bernoulli_posterior, beta_mean _ _ (by positivity) (by positivity)]
  congr 1
  ring

theorem uniform_bernoulli_posterior_variance (s f : ℕ) :
    Var[id; bayesUpdate (volume.restrict (Icc (0 : ℝ) 1))
      (fun x => x ^ s * (1 - x) ^ f)] =
        ((s : ℝ) + 1) * (f + 1) / ((s + f + 2) ^ 2 * (s + f + 3)) := by
  rw [uniform_bernoulli_posterior, beta_variance _ _ (by positivity) (by positivity)]
  congr 1
  ring

end LectureNotes
