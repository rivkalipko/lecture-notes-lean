import LectureNotes.BinomialSample

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Parameter-free conditional probability of one success in one block.
The t=0 branch is necessary; coefficients also handle totals beyond the support. -/
def binomialRaoBlackwell (k n t : ℕ) : ℝ :=
  (if t = 0 then 0 else (k : ℝ) * ((k * (n - 1)).choose (t - 1) : ℝ)) /
    ((k * n).choose t : ℝ)

def binomialOneSuccessAverage {k n : ℕ} (x : Fin n → Fin (k + 1)) : ℝ :=
  (∑ i, if (x i : ℕ) = 1 then (1 : ℝ) else 0) / n

/-- Atomic conditioning uses the actual regular conditional law. -/
theorem binomial_condDistrib_one_success {k n : ℕ} (i₀ : Fin n)
    (p : Icc (0 : ℝ) 1) (t : ℕ)
    (ht : (binomialSampleLaw k n p).map binomialSampleTotal {t} ≠ 0) :
    (condDistrib id binomialSampleTotal (binomialSampleLaw k n p) t).real
      {x | (x i₀ : ℕ) = 1} = binomialRaoBlackwell k n t := by
  let P := binomialSampleLaw k n p
  have ht' : P {x | binomialSampleTotal x = t} ≠ 0 := by
    simpa only [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton t),
      Set.preimage, Set.mem_singleton_iff, P] using ht
  have htr : P.real {x | binomialSampleTotal x = t} ≠ 0 := (measureReal_ne_zero_iff).mpr ht'
  have hd := binomialSample_total_mass k n t p
  have hA : (p : ℝ) ^ t * (1 - (p : ℝ)) ^ (k * n - t) ≠ 0 := by
    rw [hd, mul_assoc] at htr
    exact (mul_ne_zero_iff.mp htr).2
  have hC : ((k * n).choose t : ℝ) ≠ 0 := by
    rw [hd, mul_assoc] at htr
    exact (mul_ne_zero_iff.mp htr).1
  have h := congrArg ENNReal.toReal
    (condDistrib_apply_of_ne_zero (μ := P) (X := binomialSampleTotal)
      (Y := id) measurable_id t ht {x | (x i₀ : ℕ) = 1})
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ← measureReal_def] at h
  rw [map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton t),
    map_measureReal_apply (measurable_of_finite _)
      ((measurableSet_singleton t).prod MeasurableSet.of_discrete)] at h
  change (condDistrib id binomialSampleTotal P t).real {x | (x i₀ : ℕ) = 1} =
    (P.real {x | binomialSampleTotal x = t})⁻¹ *
      P.real {x | binomialSampleTotal x = t ∧ (x i₀ : ℕ) = 1} at h
  rw [h]
  dsimp only [P]
  rw [binomialSample_total_mass, binomialSample_one_success_joint_mass]
  unfold binomialRaoBlackwell
  rw [mul_assoc, mul_assoc, inv_mul_eq_div]
  rw [mul_div_mul_right _ _ hA]

/-- The complete finite conditional law is independent of p. This statement
is restricted to conditioning values of positive probability under both laws;
regular conditional kernels need not agree at impossible values. -/
theorem binomial_condDistrib_singleton {k n : ℕ} (p : Icc (0 : ℝ) 1) (t : ℕ)
    (ht : (binomialSampleLaw k n p).map binomialSampleTotal {t} ≠ 0)
    (x : Fin n → Fin (k + 1)) :
    (condDistrib id binomialSampleTotal (binomialSampleLaw k n p) t).real {x} =
      (if binomialSampleTotal x = t then binomialSampleWeight x else 0) /
        ((k * n).choose t : ℝ) := by
  let P := binomialSampleLaw k n p
  have ht' : P {y | binomialSampleTotal y = t} ≠ 0 := by
    simpa only [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton t),
      Set.preimage, Set.mem_singleton_iff, P] using ht
  have htr : P.real {y | binomialSampleTotal y = t} ≠ 0 := (measureReal_ne_zero_iff).mpr ht'
  rw [binomialSample_total_mass, mul_assoc] at htr
  have hA := (mul_ne_zero_iff.mp htr).2
  have h := congrArg ENNReal.toReal
    (condDistrib_apply_of_ne_zero (μ := P) (X := binomialSampleTotal)
      (Y := id) measurable_id t ht {x})
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ← measureReal_def] at h
  rw [map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton t),
    map_measureReal_apply (measurable_of_finite _)
      ((measurableSet_singleton t).prod (measurableSet_singleton x))] at h
  change (condDistrib id binomialSampleTotal P t).real {x} =
    (P.real {y | binomialSampleTotal y = t})⁻¹ * P.real {y | binomialSampleTotal y = t ∧ y = x} at h
  by_cases hx : binomialSampleTotal x = t
  · have he : {y : Fin n → Fin (k + 1) | binomialSampleTotal y = t ∧ y = x} = {x} := by aesop
    rw [h, he, if_pos hx]
    dsimp only [P]
    rw [binomialSample_total_mass, binomialSampleLaw_real_singleton, hx,
      mul_assoc, mul_assoc, inv_mul_eq_div, mul_div_mul_right _ _ hA]
  · have he : {y : Fin n → Fin (k + 1) | binomialSampleTotal y = t ∧ y = x} = ∅ := by aesop
    rw [h, he, measureReal_empty, mul_zero, if_neg hx, zero_div]

theorem binomial_condDistrib_parameter_independent {k n : ℕ}
    (p q : Icc (0 : ℝ) 1) (t : ℕ)
    (hp : (binomialSampleLaw k n p).map binomialSampleTotal {t} ≠ 0)
    (hq : (binomialSampleLaw k n q).map binomialSampleTotal {t} ≠ 0) :
    condDistrib id binomialSampleTotal (binomialSampleLaw k n p) t =
      condDistrib id binomialSampleTotal (binomialSampleLaw k n q) t := by
  apply Measure.ext_of_singleton
  intro x
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  exact (binomial_condDistrib_singleton p t hp x).trans (binomial_condDistrib_singleton q t hq x).symm

/-- The explicit formula is a conditional expectation of the observed fraction
of one-success blocks, under every p including the two boundary laws. -/
theorem binomial_raoBlackwell_condExp {k n : ℕ} (hn : 0 < n) (p : Icc (0 : ℝ) 1) :
    (binomialSampleLaw k n p)[binomialOneSuccessAverage |
      (inferInstance : MeasurableSpace ℕ).comap binomialSampleTotal] =ᵐ[binomialSampleLaw k n p]
      (fun x => binomialRaoBlackwell k n (binomialSampleTotal x)) := by
  let P := binomialSampleLaw k n p
  have hc := condExp_ae_eq_integral_condDistrib_id (μ := P)
    (X := binomialSampleTotal) (f := binomialOneSuccessAverage)
    (measurable_of_finite _) Integrable.of_finite
  have hs : ∀ᵐ x ∂P, P.map binomialSampleTotal {binomialSampleTotal x} ≠ 0 := by
    apply ae_iff_of_countable.mpr
    intro x hx
    rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
    exact ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hx)
      (measure_mono (by intro y hy; rw [Set.mem_singleton_iff.mp hy]; rfl)))
  filter_upwards [hc, hs] with x hx ht
  rw [hx]
  unfold binomialOneSuccessAverage
  rw [integral_div, integral_finsetSum Finset.univ (fun i _ => Integrable.of_finite)]
  have hi (i : Fin n) : (∫ y, (if (y i : ℕ) = 1 then (1 : ℝ) else 0)
      ∂condDistrib id binomialSampleTotal P (binomialSampleTotal x)) =
      binomialRaoBlackwell k n (binomialSampleTotal x) := by
    rw [show (fun y : Fin n → Fin (k + 1) => if (y i : ℕ) = 1 then (1 : ℝ) else 0) =
      {y | (y i : ℕ) = 1}.indicator (fun _ => (1 : ℝ)) from by ext y; simp [Set.indicator_apply],
      integral_indicator_const _ MeasurableSet.of_discrete, smul_eq_mul, mul_one]
    exact binomial_condDistrib_one_success i p _ ht
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne')

end LectureNotes
