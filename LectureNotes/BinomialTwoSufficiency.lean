import LectureNotes.LikelihoodRepresentationMinimal
import LectureNotes.ExponentialFamilySufficiency

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The parameter includes both degenerate boundary laws. -/
def binomialTwoMass (p : Icc (0 : ℝ) 1) (k : Fin 3) : ℝ :=
  (Nat.choose 2 k : ℝ) * (p : ℝ) ^ (k : ℕ) * (1 - (p : ℝ)) ^ (2 - (k : ℕ))

theorem binomialTwoMass_nonneg (p : Icc (0 : ℝ) 1) (k : Fin 3) :
    0 ≤ binomialTwoMass p k :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg p.property.1 _))
    (pow_nonneg (sub_nonneg.mpr p.property.2) _)

theorem binomialTwoMass_sum (p : Icc (0 : ℝ) 1) :
    ∑ k : Fin 3, binomialTwoMass p k = 1 := by
  simp [Fin.sum_univ_succ, binomialTwoMass]
  ring

/-- Actual Binomial(2,p) mass on its three possible observations. -/
def binomialTwoLaw (p : Icc (0 : ℝ) 1) : Measure (Fin 3) :=
  Measure.count.withDensity (fun k => ENNReal.ofReal (binomialTwoMass p k))

instance binomialTwoLaw_probability (p : Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (binomialTwoLaw p) := by
  constructor
  rw [binomialTwoLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_count, tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg
      (fun k _ => binomialTwoMass_nonneg p k), binomialTwoMass_sum, ENNReal.ofReal_one]

theorem binomialTwoLaw_singleton (p : Icc (0 : ℝ) 1) (k : Fin 3) :
    binomialTwoLaw p {k} = ENNReal.ofReal (binomialTwoMass p k) := by
  simp [binomialTwoLaw, withDensity_apply _ (measurableSet_singleton k), lintegral_singleton]

def binomialTwoExperiment (n : ℕ) (p : Icc (0 : ℝ) 1) : Measure (Fin n → Fin 3) :=
  Measure.pi (fun _ => binomialTwoLaw p)

instance binomialTwoExperiment_probability (n : ℕ) (p : Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (binomialTwoExperiment n p) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => binomialTwoLaw p)))

def binomialTwoStatistic {n : ℕ} (x : Fin n → Fin 3) : ℕ := ∑ i, (x i : ℕ)

theorem binomialTwo_complement_sum {n : ℕ} (x : Fin n → Fin 3) :
    (∑ i, (2 - (x i : ℕ))) = 2 * n - binomialTwoStatistic x := by
  rw [Finset.sum_tsub_distrib Finset.univ (f := fun _ => 2) (g := fun i => (x i : ℕ))
    (by intro i _; have h := (x i).isLt; omega)]
  simp [binomialTwoStatistic, mul_comm]

/-- The exact iid product likelihood, including the binomial coefficients. -/
theorem binomialTwo_product_factorization {n : ℕ} (p : Icc (0 : ℝ) 1) (x : Fin n → Fin 3) :
    (∏ i, binomialTwoMass p (x i)) =
      (∏ i, (Nat.choose 2 (x i) : ℝ)) * (p : ℝ) ^ binomialTwoStatistic x *
        (1 - (p : ℝ)) ^ (2 * n - binomialTwoStatistic x) := by
  simp only [binomialTwoMass, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, binomialTwo_complement_sum]
  rfl

/-- The full-support reference at p=1/2 also dominates p=0 and p=1. -/
theorem binomialTwoMass_reference (p : Icc (0 : ℝ) 1) (k : Fin 3) :
    binomialTwoMass p k = binomialTwoMass ⟨1 / 2, by norm_num⟩ k *
      ((2 * (p : ℝ)) ^ (k : ℕ) * (2 * (1 - (p : ℝ))) ^ (2 - (k : ℕ))) := by
  fin_cases k <;> norm_num [binomialTwoMass] <;> ring

theorem binomialTwo_product_reference {n : ℕ} (p : Icc (0 : ℝ) 1) (x : Fin n → Fin 3) :
    (∏ i, ENNReal.ofReal (binomialTwoMass p (x i))) =
      (∏ i, ENNReal.ofReal (binomialTwoMass ⟨1 / 2, by norm_num⟩ (x i))) *
        ENNReal.ofReal ((2 * (p : ℝ)) ^ binomialTwoStatistic x *
          (2 * (1 - (p : ℝ))) ^ (2 * n - binomialTwoStatistic x)) := by
  have hi (i : Fin n) := binomialTwoMass_reference p (x i)
  have hr : (∏ i, binomialTwoMass p (x i)) =
      (∏ i, binomialTwoMass ⟨1 / 2, by norm_num⟩ (x i)) *
        ((2 * (p : ℝ)) ^ binomialTwoStatistic x *
          (2 * (1 - (p : ℝ))) ^ (2 * n - binomialTwoStatistic x)) := by
    simp_rw [hi]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, binomialTwo_complement_sum]
    rfl
  simpa only [← ENNReal.ofReal_prod_of_nonneg (fun i _ => binomialTwoMass_nonneg p (x i)),
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => binomialTwoMass_nonneg ⟨1 / 2, by norm_num⟩ (x i)),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg
      (fun i _ => binomialTwoMass_nonneg ⟨1 / 2, by norm_num⟩ (x i)))] using congrArg ENNReal.ofReal hr

theorem binomialTwo_product_density (n : ℕ) (p : Icc (0 : ℝ) 1) :
    (Measure.pi (fun _ : Fin n => (Measure.count : Measure (Fin 3)))).withDensity
      (fun x => ∏ i, ENNReal.ofReal (binomialTwoMass p (x i))) = binomialTwoExperiment n p :=
  (iid_product_withDensity Measure.count (binomialTwoLaw p)
    (fun k => ENNReal.ofReal (binomialTwoMass p k)) (measurable_of_finite _) rfl n).symm

theorem binomialTwo_reference_density (n : ℕ) (p : Icc (0 : ℝ) 1) :
    (binomialTwoExperiment n ⟨1 / 2, by norm_num⟩).withDensity
      (fun x => ENNReal.ofReal ((2 * (p : ℝ)) ^ binomialTwoStatistic x *
        (2 * (1 - (p : ℝ))) ^ (2 * n - binomialTwoStatistic x))) =
      binomialTwoExperiment n p := by
  rw [← binomialTwo_product_density n ⟨1 / 2, by norm_num⟩,
    ← binomialTwo_product_density n p, ← withDensity_mul _
      (f := fun x => ∏ i, ENNReal.ofReal (binomialTwoMass ⟨1 / 2, by norm_num⟩ (x i)))
      (g := fun x => ENNReal.ofReal ((2 * (p : ℝ)) ^ binomialTwoStatistic x *
        (2 * (1 - (p : ℝ))) ^ (2 * n - binomialTwoStatistic x)))
      (measurable_of_finite _) (measurable_of_finite _)]
  exact withDensity_congr_ae (ae_of_all _ (fun x => (binomialTwo_product_reference p x).symm))

/-- The total number of successes is sufficient throughout the closed parameter interval. -/
theorem binomialTwo_sum_sufficient (n : ℕ) :
    IsSufficientStatistic (binomialTwoExperiment n) (binomialTwoStatistic (n := n)) := by
  apply sufficient_of_reference_factorization (binomialTwoExperiment n ⟨1 / 2, by norm_num⟩)
    (measurable_of_finite _)
  intro p
  exact ⟨fun s => ENNReal.ofReal ((2 * (p : ℝ)) ^ s *
    (2 * (1 - (p : ℝ))) ^ (2 * n - s)), measurable_of_countable _, binomialTwo_reference_density n p⟩

theorem binomialTwo_contrast_strictMono (n : ℕ) :
    StrictMono (fun s : ℕ => ENNReal.ofReal (((4 / 3 : ℝ) ^ s) * (2 / 3 : ℝ) ^ (2 * n - s))) := by
  intro s t hst
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
  have ha : (4 / 3 : ℝ) ^ s < (4 / 3 : ℝ) ^ t := pow_lt_pow_right₀ (by norm_num) hst
  have hb : (2 / 3 : ℝ) ^ (2 * n - s) ≤ (2 / 3 : ℝ) ^ (2 * n - t) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.sub_le_sub_left hst.le (2 * n))
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right ha (by positivity))
    (mul_le_mul_of_nonneg_left hb (by positivity))

/-- L5 Example 18, with an actual normalized product experiment and the
boundary parameter values retained. One interior contrast separates all sums. -/
theorem binomialTwo_sum_minimal_sufficient (n : ℕ) :
    IsMinimalSufficientStatistic (binomialTwoExperiment n) (binomialTwoStatistic (n := n)) := by
  let p₀ : Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  let p₁ : Icc (0 : ℝ) 1 := ⟨2 / 3, by norm_num⟩
  let g (s : ℕ) (_ : Fin 1) := ENNReal.ofReal ((4 / 3 : ℝ) ^ s * (2 / 3 : ℝ) ^ (2 * n - s))
  have hdom p : binomialTwoExperiment n p ≪ binomialTwoExperiment n p₀ := by
    rw [← binomialTwo_reference_density n p]
    exact withDensity_absolutelyContinuous _ _
  have hginj : Function.Injective g := by
    intro s t h
    exact (binomialTwo_contrast_strictMono n).injective (congrFun h 0)
  apply minimal_sufficient_of_injective_ratio_representation (binomialTwoExperiment n)
    (binomialTwo_sum_sufficient n) p₀ hdom (fun _ : Fin 1 => p₁) g
    (measurable_of_countable _) hginj
  intro i
  have h := Measure.rnDeriv_withDensity (binomialTwoExperiment n p₀)
    (show Measurable (fun x : Fin n → Fin 3 => ENNReal.ofReal
      ((2 * (p₁ : ℝ)) ^ binomialTwoStatistic x *
        (2 * (1 - (p₁ : ℝ))) ^ (2 * n - binomialTwoStatistic x))) from measurable_of_finite _)
  change ((binomialTwoExperiment n ⟨1 / 2, by norm_num⟩).withDensity _).rnDeriv _ =ᵐ[_] _ at h
  rw [binomialTwo_reference_density] at h
  convert h using 1 <;> norm_num [p₀, p₁, g]

end LectureNotes
