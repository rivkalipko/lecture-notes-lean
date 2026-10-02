import LectureNotes.BinomialSample

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- A reference likelihood factor valid throughout p∈[0,1]. -/
theorem binomialSample_product_reference {k n : ℕ} (p : Icc (0 : ℝ) 1)
    (x : Fin n → Fin (k + 1)) :
    (∏ i, ENNReal.ofReal (binomialCountMass k p (x i))) =
      (∏ i, ENNReal.ofReal (binomialCountMass k ⟨1 / 2, by norm_num⟩ (x i))) *
        ENNReal.ofReal ((2 * (p : ℝ)) ^ binomialSampleTotal x *
          (2 * (1 - (p : ℝ))) ^ (k * n - binomialSampleTotal x)) := by
  have hr : (∏ i, binomialCountMass k p (x i)) =
      (∏ i, binomialCountMass k ⟨1 / 2, by norm_num⟩ (x i)) *
        ((2 * (p : ℝ)) ^ binomialSampleTotal x *
          (2 * (1 - (p : ℝ))) ^ (k * n - binomialSampleTotal x)) := by
    rw [binomialSample_product_factorization, binomialSample_product_factorization]
    norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    symm
    calc
      _ = binomialSampleWeight x *
          ((1 / 2 : ℝ) ^ binomialSampleTotal x * (2 * (p : ℝ)) ^ binomialSampleTotal x) *
          ((1 / 2 : ℝ) ^ (k * n - binomialSampleTotal x) *
            (2 * (1 - (p : ℝ))) ^ (k * n - binomialSampleTotal x)) := by ring
      _ = _ := by
        rw [← mul_pow, ← mul_pow,
          show (1 / 2 : ℝ) * (2 * (p : ℝ)) = (p : ℝ) by ring,
          show (1 / 2 : ℝ) * (2 * (1 - (p : ℝ))) = 1 - (p : ℝ) by ring]
  simpa only [← ENNReal.ofReal_prod_of_nonneg (fun i _ => binomialCountMass_nonneg k p (x i)),
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => binomialCountMass_nonneg k ⟨1 / 2, by norm_num⟩ (x i)),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg
      (fun i _ => binomialCountMass_nonneg k ⟨1 / 2, by norm_num⟩ (x i)))] using congrArg ENNReal.ofReal hr

theorem binomialSample_product_density (k n : ℕ) (p : Icc (0 : ℝ) 1) :
    (Measure.pi (fun _ : Fin n => (Measure.count : Measure (Fin (k + 1))))).withDensity
      (fun x => ∏ i, ENNReal.ofReal (binomialCountMass k p (x i))) = binomialSampleLaw k n p :=
  (iid_product_withDensity Measure.count (binomialCountLaw k p)
    (fun j => ENNReal.ofReal (binomialCountMass k p j)) (measurable_of_finite _) rfl n).symm

theorem binomialSample_reference_density (k n : ℕ) (p : Icc (0 : ℝ) 1) :
    (binomialSampleLaw k n ⟨1 / 2, by norm_num⟩).withDensity
      (fun x => ENNReal.ofReal ((2 * (p : ℝ)) ^ binomialSampleTotal x *
        (2 * (1 - (p : ℝ))) ^ (k * n - binomialSampleTotal x))) =
      binomialSampleLaw k n p := by
  rw [← binomialSample_product_density k n ⟨1 / 2, by norm_num⟩,
    ← binomialSample_product_density k n p, ← withDensity_mul _
      (f := fun x => ∏ i, ENNReal.ofReal (binomialCountMass k ⟨1 / 2, by norm_num⟩ (x i)))
      (g := fun x => ENNReal.ofReal ((2 * (p : ℝ)) ^ binomialSampleTotal x *
        (2 * (1 - (p : ℝ))) ^ (k * n - binomialSampleTotal x)))
      (measurable_of_finite _) (measurable_of_finite _)]
  exact withDensity_congr_ae (ae_of_all _ (fun x => (binomialSample_product_reference p x).symm))

theorem binomialSample_contrast_strictMono (m : ℕ) :
    StrictMono (fun s : ℕ => ENNReal.ofReal (((4 / 3 : ℝ) ^ s) * (2 / 3 : ℝ) ^ (m - s))) := by
  intro s t hst
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
  have ha : (4 / 3 : ℝ) ^ s < (4 / 3 : ℝ) ^ t := pow_lt_pow_right₀ (by norm_num) hst
  have hb : (2 / 3 : ℝ) ^ (m - s) ≤ (2 / 3 : ℝ) ^ (m - t) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.sub_le_sub_left hst.le m)
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right ha (by positivity))
    (mul_le_mul_of_nonneg_left hb (by positivity))

/-- The general Binomial(k,p) success total is minimal sufficient, including
p=0,1. Empty samples and k=0 give the valid constant-statistic special cases. -/
theorem binomialSample_total_minimal_sufficient (k n : ℕ) :
    IsMinimalSufficientStatistic (binomialSampleLaw k n) (binomialSampleTotal (k := k) (n := n)) := by
  let p₀ : Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  let p₁ : Icc (0 : ℝ) 1 := ⟨2 / 3, by norm_num⟩
  let g (s : ℕ) (_ : Fin 1) := ENNReal.ofReal ((4 / 3 : ℝ) ^ s * (2 / 3 : ℝ) ^ (k * n - s))
  have hdom p : binomialSampleLaw k n p ≪ binomialSampleLaw k n p₀ := by
    rw [← binomialSample_reference_density k n p]
    exact withDensity_absolutelyContinuous _ _
  have hginj : Function.Injective g := by
    intro s t h
    exact (binomialSample_contrast_strictMono (k * n)).injective (congrFun h 0)
  apply minimal_sufficient_of_injective_ratio_representation (binomialSampleLaw k n)
    (binomialSample_total_sufficient k n) p₀ hdom (fun _ : Fin 1 => p₁) g
    (measurable_of_countable _) hginj
  intro i
  have h := Measure.rnDeriv_withDensity (binomialSampleLaw k n p₀)
    (show Measurable (fun x : Fin n → Fin (k + 1) => ENNReal.ofReal
      ((2 * (p₁ : ℝ)) ^ binomialSampleTotal x *
        (2 * (1 - (p₁ : ℝ))) ^ (k * n - binomialSampleTotal x))) from measurable_of_finite _)
  change ((binomialSampleLaw k n ⟨1 / 2, by norm_num⟩).withDensity _).rnDeriv _ =ᵐ[_] _ at h
  rw [binomialSample_reference_density] at h
  convert h using 1 <;> norm_num [p₀, p₁, g]

end LectureNotes
