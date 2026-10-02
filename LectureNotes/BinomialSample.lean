import LectureNotes.BinomialCounting
import LectureNotes.FisherNeymanGeneral

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Binomial(k,p) mass, on the exact finite observation space. -/
def binomialCountMass (k : ℕ) (p : Icc (0 : ℝ) 1) (j : Fin (k + 1)) : ℝ :=
  (k.choose j : ℝ) * (p : ℝ) ^ (j : ℕ) * (1 - (p : ℝ)) ^ (k - (j : ℕ))

theorem binomialCountMass_nonneg (k : ℕ) (p : Icc (0 : ℝ) 1) (j : Fin (k + 1)) :
    0 ≤ binomialCountMass k p j := by
  unfold binomialCountMass
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg p.property.1 _))
    (pow_nonneg (sub_nonneg.mpr p.property.2) _)

theorem binomialCountMass_sum (k : ℕ) (p : Icc (0 : ℝ) 1) :
    ∑ j, binomialCountMass k p j = 1 := by
  unfold binomialCountMass
  rw [Fin.sum_univ_eq_sum_range (fun j => (k.choose j : ℝ) * (p : ℝ) ^ j *
    (1 - (p : ℝ)) ^ (k - j)) (k + 1)]
  have h := add_pow (p : ℝ) (1 - (p : ℝ)) k
  rw [add_sub_cancel, one_pow] at h
  convert h.symm using 1
  apply Finset.sum_congr rfl
  intro j _
  ring

def binomialCountLaw (k : ℕ) (p : Icc (0 : ℝ) 1) : Measure (Fin (k + 1)) :=
  Measure.count.withDensity (fun j => ENNReal.ofReal (binomialCountMass k p j))

instance binomialCountLaw_probability (k : ℕ) (p : Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (binomialCountLaw k p) := by
  constructor
  rw [binomialCountLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_count, tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg
      (fun j _ => binomialCountMass_nonneg k p j), binomialCountMass_sum, ENNReal.ofReal_one]

theorem binomialCountLaw_singleton (k : ℕ) (p : Icc (0 : ℝ) 1) (j : Fin (k + 1)) :
    binomialCountLaw k p {j} = ENNReal.ofReal (binomialCountMass k p j) := by
  simp [binomialCountLaw, withDensity_apply _ (measurableSet_singleton j)]

/-- The actual product experiment of L5 Example 19. -/
def binomialSampleLaw (k n : ℕ) (p : Icc (0 : ℝ) 1) : Measure (Fin n → Fin (k + 1)) :=
  Measure.pi (fun _ => binomialCountLaw k p)

instance binomialSampleLaw_probability (k n : ℕ) (p : Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (binomialSampleLaw k n p) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => binomialCountLaw k p)))

theorem binomialSample_product_factorization {k n : ℕ} (p : Icc (0 : ℝ) 1)
    (x : Fin n → Fin (k + 1)) :
    (∏ i, binomialCountMass k p (x i)) = binomialSampleWeight x *
      (p : ℝ) ^ binomialSampleTotal x * (1 - (p : ℝ)) ^ (k * n - binomialSampleTotal x) := by
  have hc : (∑ i, (k - (x i : ℕ))) = k * n - binomialSampleTotal x := by
    rw [Finset.sum_tsub_distrib Finset.univ (f := fun _ => k) (g := fun i => (x i : ℕ))
      (by intro i _; have h := (x i).isLt; omega)]
    simp [binomialSampleTotal, mul_comm]
  simp only [binomialCountMass, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, hc]
  rfl

theorem binomialSampleLaw_real_singleton {k n : ℕ} (p : Icc (0 : ℝ) 1)
    (x : Fin n → Fin (k + 1)) :
    (binomialSampleLaw k n p).real {x} = binomialSampleWeight x *
      (p : ℝ) ^ binomialSampleTotal x * (1 - (p : ℝ)) ^ (k * n - binomialSampleTotal x) := by
  simp only [measureReal_def, binomialSampleLaw, Measure.pi_singleton, binomialCountLaw_singleton,
    ENNReal.toReal_prod, ENNReal.toReal_ofReal (binomialCountMass_nonneg k p _)]
  exact binomialSample_product_factorization p x

theorem finite_measureReal_set {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Measure Ω) [IsFiniteMeasure P] (s : Set Ω) [DecidablePred (· ∈ s)] :
    P.real s = ∑ x, if x ∈ s then P.real {x} else 0 := by
  classical
  have hs : ((Finset.univ.filter (fun x : Ω => x ∈ s) : Finset Ω) : Set Ω) = s := by
    ext x
    simp
  have h := sum_measureReal_singleton (μ := P) (Finset.univ.filter (fun x : Ω => x ∈ s))
  rw [hs] at h
  simpa only [Finset.sum_filter] using h.symm

/-- The sum of n independent Binomial(k,p) observations has the exact
Binomial(kn,p) mass, including p=0 and p=1. -/
theorem binomialSample_total_mass (k n t : ℕ) (p : Icc (0 : ℝ) 1) :
    (binomialSampleLaw k n p).real {x | binomialSampleTotal x = t} =
      ((k * n).choose t : ℝ) * (p : ℝ) ^ t * (1 - (p : ℝ)) ^ (k * n - t) := by
  rw [finite_measureReal_set]
  simp only [Set.mem_ofPred_eq, binomialSampleLaw_real_singleton]
  have he (x : Fin n → Fin (k + 1)) :
      (if binomialSampleTotal x = t then binomialSampleWeight x * (p : ℝ) ^ binomialSampleTotal x *
        (1 - (p : ℝ)) ^ (k * n - binomialSampleTotal x) else 0) =
      (if binomialSampleTotal x = t then binomialSampleWeight x else 0) *
        (p : ℝ) ^ t * (1 - (p : ℝ)) ^ (k * n - t) := by
    split_ifs with hx <;> simp [hx]
  simp_rw [he]
  rw [← Finset.sum_mul, ← Finset.sum_mul, binomial_sample_fiber_weight]

/-- Joint mass of a total and a specified coordinate with exactly one success. -/
theorem binomialSample_one_success_joint_mass {k n : ℕ} (i₀ : Fin n)
    (t : ℕ) (p : Icc (0 : ℝ) 1) :
    (binomialSampleLaw k n p).real {x | binomialSampleTotal x = t ∧ (x i₀ : ℕ) = 1} =
      (if t = 0 then 0 else (k : ℝ) * ((k * (n - 1)).choose (t - 1) : ℝ)) *
        (p : ℝ) ^ t * (1 - (p : ℝ)) ^ (k * n - t) := by
  rw [finite_measureReal_set]
  simp only [Set.mem_ofPred_eq, binomialSampleLaw_real_singleton]
  have he (x : Fin n → Fin (k + 1)) :
      (if binomialSampleTotal x = t ∧ (x i₀ : ℕ) = 1 then
        binomialSampleWeight x * (p : ℝ) ^ binomialSampleTotal x *
          (1 - (p : ℝ)) ^ (k * n - binomialSampleTotal x) else 0) =
      (if binomialSampleTotal x = t ∧ (x i₀ : ℕ) = 1 then binomialSampleWeight x else 0) *
        (p : ℝ) ^ t * (1 - (p : ℝ)) ^ (k * n - t) := by
    split_ifs with hx
    · simp [hx.1]
    · simp
  simp_rw [he]
  rw [← Finset.sum_mul, ← Finset.sum_mul, binomial_one_success_fiber_weight]

/-- The total success count is sufficient for the full closed parameter
interval, including its degenerate boundary distributions. -/
theorem binomialSample_total_sufficient (k n : ℕ) :
    IsSufficientStatistic (binomialSampleLaw k n) (binomialSampleTotal (k := k) (n := n)) := by
  let ν : Measure (Fin n → Fin (k + 1)) := Measure.pi (fun _ => Measure.count)
  let f (p : Icc (0 : ℝ) 1) (x : Fin n → Fin (k + 1)) :=
    ∏ i, ENNReal.ofReal (binomialCountMass k p (x i))
  have hd p : ν.withDensity (f p) = binomialSampleLaw k n p :=
    (iid_product_withDensity Measure.count (binomialCountLaw k p)
      (fun j => ENNReal.ofReal (binomialCountMass k p j)) (measurable_of_finite _) rfl n).symm
  apply (fisherNeyman_general (binomialSampleLaw k n) ν f
    (fun _ => measurable_of_finite _) hd (measurable_of_finite _)).mpr
  refine ⟨fun x => ENNReal.ofReal (binomialSampleWeight x), measurable_of_finite _, ?_⟩
  intro p
  refine ⟨fun t => ENNReal.ofReal ((p : ℝ) ^ t * (1 - (p : ℝ)) ^ (k * n - t)),
    measurable_of_countable _, ae_of_all _ ?_⟩
  intro x
  dsimp only [f]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => binomialCountMass_nonneg k p (x i)),
    ← ENNReal.ofReal_mul (binomialSampleWeight_pos x).le,
    binomialSample_product_factorization, mul_assoc]

end LectureNotes
