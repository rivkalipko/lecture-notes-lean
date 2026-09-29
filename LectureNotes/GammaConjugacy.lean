import LectureNotes.BetaConjugacy

set_option autoImplicit false

/-! L12 Gamma–Poisson conjugacy. Mathlib uses shape and rate; the notes use
shape and scale. The scale conversion is stated explicitly below. Density
values at the origin are immaterial because Lebesgue measure has no atoms. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

theorem bayesUpdate_congr_ae {Θ : Type*} [MeasurableSpace Θ]
    {ν : Measure Θ} {q f : Θ → ℝ} (h : q =ᵐ[ν] f) :
    bayesUpdate ν q = bayesUpdate ν f := by
  have he : evidence ν q = evidence ν f := integral_congr_ae h
  unfold bayesUpdate
  rw [he]
  apply withDensity_congr_ae
  exact h.mono (fun θ hθ => by dsimp; rw [hθ])

theorem gamma_density_integrable {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (gammaPDFReal a r) volume := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_gammaPDFReal a r).aestronglyMeasurable
    (ae_of_all _ (gammaPDFReal_nonneg ha hr))).mp
  change (∫⁻ x, gammaPDF a r x) ≠ ⊤
  rw [lintegral_gammaPDF_eq_one ha hr]
  norm_num

theorem gamma_density_integral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ x, gammaPDFReal a r x) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (gammaPDFReal_nonneg ha hr))
    (measurable_gammaPDFReal a r).aestronglyMeasurable]
  change (∫⁻ x, gammaPDF a r x).toReal = 1
  rw [lintegral_gammaPDF_eq_one ha hr]
  norm_num

theorem normalized_gamma_density {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    bayesUpdate volume (gammaPDFReal a r) = gammaMeasure a r := by
  have he : evidence volume (gammaPDFReal a r) = 1 := gamma_density_integral ha hr
  rw [bayesUpdate, he]
  simp only [div_one]
  rfl

theorem gamma_likelihood_product (a r : ℝ) (ha : 0 < a) (hr : 0 < r)
    (n s : ℕ) :
    (fun x => gammaPDFReal a r x * (Real.exp (-(n : ℝ) * x) * x ^ s)) =ᵐ[volume]
      (fun x => (r ^ a * Real.Gamma (a + s) /
        (Real.Gamma a * (r + n) ^ (a + s))) * gammaPDFReal (a + s) (r + n) x) := by
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  by_cases hxpos : 0 < x
  · have hg : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
    have hgs : Real.Gamma (a + s) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hrn : (r + (n : ℝ)) ^ (a + s) ≠ 0 :=
      (Real.rpow_pos_of_pos (by positivity) _).ne'
    simp only [gammaPDFReal, if_pos hxpos.le]
    rw [show a + (s : ℝ) - 1 = (a - 1) + s by ring,
      Real.rpow_add hxpos, Real.rpow_natCast,
      show -((r + (n : ℝ)) * x) = -(r * x) + -(n : ℝ) * x by ring,
      Real.exp_add]
    field_simp
    <;> ring
  · have hxneg : ¬ 0 ≤ x := by exact not_le.mpr (lt_of_le_of_ne (le_of_not_gt hxpos) hx)
    simp [gammaPDFReal, hxneg]

/-- Exact Gamma–Poisson updating, in shape/rate coordinates. The likelihood
omits only positive factors depending on the observed counts, not on λ. -/
theorem gamma_poisson_conjugacy (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (n s : ℕ) :
    bayesUpdate (gammaMeasure a r) (fun x => Real.exp (-(n : ℝ) * x) * x ^ s) =
      gammaMeasure (a + s) (r + n) := by
  change bayesUpdate (volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal a r x)))
    (fun x => Real.exp (-(n : ℝ) * x) * x ^ s) = _
  rw [bayesUpdate_withDensity volume _ _ (measurable_gammaPDFReal a r) (by fun_prop)
    (gammaPDFReal_nonneg ha hr), bayesUpdate_congr_ae (gamma_likelihood_product a r ha hr n s)]
  have hc : r ^ a * Real.Gamma (a + s) / (Real.Gamma a * (r + n) ^ (a + s)) ≠ 0 := by
    apply ne_of_gt
    apply div_pos
    · exact mul_pos (Real.rpow_pos_of_pos hr _) (Real.Gamma_pos_of_pos (by positivity))
    · exact mul_pos (Real.Gamma_pos_of_pos ha) (Real.rpow_pos_of_pos (by positivity) _)
  rw [bayesUpdate_scale _ _ hc]
  exact normalized_gamma_density (by positivity) (by positivity)

/-- The source's scale β becomes rate 1/β in Mathlib. The updated scale is
β/(nβ+1), with positive denominators proved from β > 0. -/
theorem gamma_poisson_conjugacy_scale (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (n s : ℕ) :
    bayesUpdate (gammaMeasure a (1 / β)) (fun x => Real.exp (-(n : ℝ) * x) * x ^ s) =
      gammaMeasure (gammaPosteriorShape a s) (1 / gammaPosteriorScale β n) := by
  rw [gamma_poisson_conjugacy a (1 / β) ha (by positivity) n s]
  unfold gammaPosteriorShape gammaPosteriorScale
  congr 1
  field_simp
  <;> ring

/-- Integer moments, expressed as ratios of Gamma normalizers. -/
theorem gamma_moment (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (k : ℕ) :
    (∫ x, x ^ k ∂gammaMeasure a r) = Real.Gamma (a + k) / (Real.Gamma a * r ^ k) := by
  change (∫ x, x ^ k ∂volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal a r x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (measurable_gammaPDFReal a r).ennreal_ofReal.aemeasurable
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _), smul_eq_mul]
  have hprod := gamma_likelihood_product a r ha hr 0 k
  simp only [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero, one_mul, add_zero] at hprod
  rw [integral_congr_ae hprod, integral_const_mul,
    gamma_density_integral (by positivity) hr, mul_one,
    Real.rpow_add hr, Real.rpow_natCast]
  have hpow : r ^ a ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have hg : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  field_simp

theorem gamma_power_integrable (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (k : ℕ) :
    Integrable (fun x => x ^ k) (gammaMeasure a r) := by
  change Integrable (fun x => x ^ k)
    (volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal a r x)))
  rw [integrable_withDensity_iff_integrable_smul₀'
    (measurable_gammaPDFReal a r).ennreal_ofReal.aemeasurable
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _), smul_eq_mul]
  have hprod := gamma_likelihood_product a r ha hr 0 k
  simp only [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero, one_mul, add_zero] at hprod
  apply (integrable_congr hprod).mpr
  exact (gamma_density_integrable (by positivity) hr).const_mul _

theorem gamma_mean (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    (∫ x, x ∂gammaMeasure a r) = a / r := by
  have h := gamma_moment a r ha hr 1
  simp only [pow_one, Nat.cast_one] at h
  rw [h, Real.Gamma_add_one ha.ne']
  have hg : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  field_simp

theorem gamma_second_moment (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    (∫ x, x ^ 2 ∂gammaMeasure a r) = a * (a + 1) / r ^ 2 := by
  rw [gamma_moment a r ha hr 2]
  norm_num only [Nat.cast_ofNat]
  rw [show a + 2 = (a + 1) + 1 by ring,
    Real.Gamma_add_one (by positivity : a + 1 ≠ 0), Real.Gamma_add_one ha.ne']
  have hg : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  field_simp
  <;> ring

theorem gamma_variance (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    Var[id; gammaMeasure a r] = a / r ^ 2 := by
  letI := isProbabilityMeasure_gammaMeasure ha hr
  have h₂ : MemLp (id : ℝ → ℝ) 2 (gammaMeasure a r) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (gamma_power_integrable a r ha hr 2)
  rw [variance_eq_sub h₂]
  change (∫ x, x ^ 2 ∂gammaMeasure a r) - (∫ x, x ∂gammaMeasure a r) ^ 2 = _
  rw [gamma_second_moment a r ha hr, gamma_mean a r ha hr]
  field_simp
  <;> ring

theorem gamma_poisson_posterior_mean (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (n s : ℕ) :
    (∫ x, x ∂bayesUpdate (gammaMeasure a (1 / β))
      (fun x => Real.exp (-(n : ℝ) * x) * x ^ s)) =
        β * (a + s) / (n * β + 1) := by
  rw [gamma_poisson_conjugacy a (1 / β) ha (by positivity) n s,
    gamma_mean _ _ (by positivity) (by positivity)]
  field_simp
  <;> ring

theorem gamma_poisson_posterior_variance (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (n s : ℕ) :
    Var[id; bayesUpdate (gammaMeasure a (1 / β))
      (fun x => Real.exp (-(n : ℝ) * x) * x ^ s)] =
        β ^ 2 * (a + s) / (n * β + 1) ^ 2 := by
  rw [gamma_poisson_conjugacy a (1 / β) ha (by positivity) n s,
    gamma_variance _ _ (by positivity) (by positivity)]
  field_simp
  <;> ring

end LectureNotes
