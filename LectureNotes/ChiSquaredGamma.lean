import LectureNotes.GaussianRadialMoments
import LectureNotes.GaussianQuadraticForms
import LectureNotes.ErlangCDF
import LectureNotes.GaussianVarianceTests

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology ENNReal NNReal

/-- Squaring the radial coordinate converts its even-dimensional volume
factor to the Gamma power. -/
theorem radial_square_integral (k : ℕ) (f : ℝ → ℝ) :
    (∫ u in Ioi (0 : ℝ), u ^ k * exp (-u / 2) * f u) =
      2 * ∫ r in Ioi (0 : ℝ), r ^ (2 * k + 1) * exp (-r ^ 2 / 2) * f (r ^ 2) := by
  have hh := integral_comp_rpow_Ioi_of_pos (g := fun u : ℝ => u ^ k * exp (-u / 2) * f u)
    (by norm_num : (0 : ℝ) < 2)
  rw [← hh, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, smul_eq_mul]
  rw [← pow_mul, pow_succ]
  ring

/-- The normalization constant from polar integration equals the Gamma
normalization constant, including its Jacobian factor. -/
theorem gaussian_even_radial_constant (k : ℕ) :
    (2 * (k + 1) : ℝ) * (Real.pi ^ (k + 1) / ((k + 1).factorial : ℝ)) *
      (1 / Real.sqrt (2 * Real.pi)) ^ (2 * (k + 1)) =
        2 * ((1 / 2 : ℝ) ^ (k + 1) / (k.factorial : ℝ)) := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [pow_mul, div_pow, one_pow, Real.sq_sqrt (by positivity), div_pow, mul_pow,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [div_pow, one_pow]
  field_simp

/-- Polar integration of the actual standard Gaussian density. -/
theorem stdGaussian_even_norm_sq_integral (k : ℕ) (f : ℝ → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * (k + 1))), f (‖x‖ ^ 2) ∂stdGaussian _) =
      (2 * ((1 / 2 : ℝ) ^ (k + 1) / (k.factorial : ℝ))) *
        ∫ r in Ioi (0 : ℝ), r ^ (2 * k + 1) * exp (-r ^ 2 / 2) * f (r ^ 2) := by
  let E := EuclideanSpace ℝ (Fin (2 * (k + 1)))
  letI : Nonempty (Fin (2 * (k + 1))) := ⟨⟨0, by omega⟩⟩
  rw [stdGaussian_radial_density, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (by filter_upwards [] with x; exact ENNReal.ofReal_lt_top)]
  have he : (fun x : E =>
      (ENNReal.ofReal ((1 / Real.sqrt (2 * Real.pi)) ^ (2 * (k + 1)) *
        exp (-‖x‖ ^ 2 / 2))).toReal • f (‖x‖ ^ 2)) =
      (fun x : E => (1 / Real.sqrt (2 * Real.pi)) ^ (2 * (k + 1)) *
        (exp (-‖x‖ ^ 2 / 2) * f (‖x‖ ^ 2))) := by
    funext x
    rw [ENNReal.toReal_ofReal (by positivity)]
    simp only [smul_eq_mul]
    ring
  rw [he, integral_const_mul, integral_fun_norm_addHaar (volume : Measure E)
    (fun r : ℝ => exp (-r ^ 2 / 2) * f (r ^ 2))]
  have hv : (volume : Measure E).real (Metric.ball 0 1) =
      Real.pi ^ (k + 1) / ((k + 1).factorial : ℝ) := by
    rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (k := k + 1)
      (by simp [E])]
    have hvnonneg : 0 ≤ Real.pi ^ (k + 1) / ((k + 1).factorial : ℝ) :=
      div_nonneg (pow_nonneg pi_nonneg _) (Nat.cast_nonneg _)
    simp [hvnonneg]
  rw [hv]
  simp only [E, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul]
  have hn : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [hn]
  simp only [← mul_assoc]
  convert! congrArg (fun c : ℝ => c * ∫ r in Ioi (0 : ℝ),
    r ^ (2 * k + 1) * exp (-r ^ 2 / 2) * f (r ^ 2))
    (gaussian_even_radial_constant k) using 1 <;> push_cast <;> ring

/-- The integer-shape Gamma integral is the same radial integral. -/
theorem gamma_nat_half_integral (k : ℕ) (f : ℝ → ℝ) :
    (∫ u, f u ∂gammaMeasure ((k : ℝ) + 1) (1 / 2)) =
      (2 * ((1 / 2 : ℝ) ^ (k + 1) / (k.factorial : ℝ))) *
        ∫ r in Ioi (0 : ℝ), r ^ (2 * k + 1) * exp (-r ^ 2 / 2) * f (r ^ 2) := by
  have hmeas : Measurable (gammaPDF ((k : ℝ) + 1) (1 / 2)) := by
    exact (measurable_gammaPDFReal _ _).ennreal_ofReal
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul
    hmeas (by filter_upwards [] with u; exact ENNReal.ofReal_lt_top)]
  have he : (fun u : ℝ => (gammaPDF ((k : ℝ) + 1) (1 / 2) u).toReal • f u) =
      (Ici (0 : ℝ)).indicator (fun u =>
        ((1 / 2 : ℝ) ^ (k + 1) / (k.factorial : ℝ)) *
          (u ^ k * exp (-u / 2) * f u)) := by
    funext u
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg (by positivity) (by norm_num) u)]
    simp only [gammaPDFReal, Real.Gamma_nat_eq_factorial, smul_eq_mul]
    have hp : (1 / 2 : ℝ) ^ ((k : ℝ) + 1) = (1 / 2 : ℝ) ^ (k + 1) := by
      rw [← Nat.cast_add_one, Real.rpow_natCast]
    rw [hp, show (k : ℝ) + 1 - 1 = k by ring, Real.rpow_natCast]
    by_cases hu : 0 ≤ u <;> simp [hu, neg_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  rw [he, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, radial_square_integral]
  ring

/-- An even number of independent squared standard normal coordinates has
Gamma law with shape half the dimension and rate one half. -/
theorem chiSquared_even_eq_gamma_succ (k : ℕ) :
    chiSquared (2 * (k + 1)) = gammaMeasure ((k : ℝ) + 1) (1 / 2) := by
  letI : IsProbabilityMeasure (gammaMeasure ((k : ℝ) + 1) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hlaw := stdGaussian_norm_sq (E := EuclideanSpace ℝ (Fin (2 * (k + 1))))
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hlaw
  rw [← hlaw.integral_comp f.continuous.aestronglyMeasurable]
  simp only [Function.comp_def]
  rw [stdGaussian_even_norm_sq_integral, gamma_nat_half_integral]

/-- Positive even degrees of freedom in the usual shape/rate convention. -/
theorem chiSquared_even_eq_gamma {k : ℕ} (hk : 0 < k) :
    chiSquared (2 * k) = gammaMeasure (k : ℝ) (1 / 2) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    chiSquared_even_eq_gamma_succ l

/-- The actual chi-square lower-tail probability in L8's numerical example. -/
theorem chiSquared_hundred_cdf_ninety_bounds :
    (246 : ℝ) / 1000 < cdf (chiSquared 100) 90 ∧
      cdf (chiSquared 100) 90 < (247 : ℝ) / 1000 := by
  have he : chiSquared 100 = gammaMeasure 50 (1 / 2) := by
    simpa using chiSquared_even_eq_gamma (k := 50) (by norm_num)
  rw [he]
  exact gamma_fifty_half_cdf_ninety_bounds

/-- In particular, 90 lies strictly above the five-percent lower critical value. -/
theorem chiSquared_hundred_five_percent_quantile_lt_ninety :
    distributionQuantile (chiSquared 100) (5 / 100) < 90 := by
  haveI : NullSingletonClass (chiSquared 100) := chiSquared_nullSingletonClass (by norm_num)
  have hq : cdf (chiSquared 100)
      (distributionQuantile (chiSquared 100) (5 / 100)) = 5 / 100 := by
    rw [cdf_eq_real, distributionQuantile_exact _ _ (by norm_num : (5 / 100 : ℝ) ∈ Ioo 0 1)]
  by_contra h
  have hh := (monotone_cdf (μ := chiSquared 100)) (le_of_not_gt h)
  rw [hq] at hh
  linarith [chiSquared_hundred_cdf_ninety_bounds.1]

/-- The source's observed n−1 sample variance gives its stated p-value. -/
theorem normal_variance_example_pvalue {x : Fin 101 → ℝ}
    (hx : sampleVariance x = 9 / 10) :
    (246 : ℝ) / 1000 < cdf (chiSquared (101 - 1)) (((101 : ℝ) - 1) * sampleVariance x / 1) ∧
      cdf (chiSquared (101 - 1)) (((101 : ℝ) - 1) * sampleVariance x / 1) < (247 : ℝ) / 1000 := by
  simpa only [hx, show (101 : ℕ) - 1 = 100 by norm_num,
    show ((101 : ℝ) - 1) * (9 / 10) / 1 = 90 by norm_num] using
    chiSquared_hundred_cdf_ninety_bounds

/-- The actual calibrated lower-tail variance test does not reject this sample. -/
theorem normal_variance_example_no_rejection {x : Fin 101 → ℝ}
    (hx : sampleVariance x = 9 / 10) :
    (gaussianVarianceLowerTest 101 1
      (distributionQuantile (chiSquared (101 - 1)) (5 / 100))).reject x = 0 := by
  have hcut := chiSquared_hundred_five_percent_quantile_lt_ninety
  simp only [gaussianVarianceLowerTest, StatisticalTest.ofRejectionSet]
  apply indicator_of_notMem
  simp only [mem_setOf_eq, hx, show (101 : ℕ) - 1 = 100 by norm_num,
    show ((101 : ℝ) - 1) * (9 / 10) / 1 = 90 by norm_num]
  convert not_le.mpr hcut using 1 <;> norm_num

end LectureNotes
