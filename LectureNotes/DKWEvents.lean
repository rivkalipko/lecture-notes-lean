import LectureNotes.DKWCensorBridge
import LectureNotes.EmpiricalUniform

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- The number of observations in a closed lower tail. -/
def dkwCount {n : ℕ} (x : Fin n → ℝ) (u : ℝ) : ℕ :=
  (Finset.univ.filter (fun i => x i ≤ u)).card

theorem dkwCount_le {n : ℕ} (x : Fin n → ℝ) (u : ℝ) : dkwCount x u ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem dkwCount_mono {n : ℕ} (x : Fin n → ℝ) : Monotone (dkwCount x) := by
  intro u v huv
  apply Finset.card_le_card
  intro i hi
  have h := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h.trans huv⟩

theorem empiricalCDF_eq_dkwCount {n : ℕ} (x : Fin n → ℝ) (u : ℝ) :
    empiricalCDF x u = (dkwCount x u : ℝ) / n := by
  simp [empiricalCDF, dkwCount, Finset.sum_boole]

theorem dkwProductWeight_eq_pow {n : ℕ} (x : Fin n → ℝ) (u ℓ : ℝ) :
    dkwProductWeight u ℓ x = (1 + ℓ / u) ^ dkwCount x u := by
  simp [dkwProductWeight, dkwCountWeight, dkwCount, ← Finset.prod_filter]

/-- Every upper CDF deviation is witnessed at a deterministic count threshold.
The strict deviation makes the new threshold strictly positive. -/
theorem empiricalCDF_upper_count_witness {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) {ε t : ℝ} (ht : 0 ≤ t)
    (hdev : ε < empiricalCDF x t - t) :
    ∃ k ≤ n, ε < (k : ℝ) / n ∧
      (k : ℕ) ≤ dkwCount x ((k : ℝ) / n - ε) := by
  refine ⟨dkwCount x t, dkwCount_le x t, ?_, ?_⟩
  · rw [empiricalCDF_eq_dkwCount] at hdev
    linarith
  · apply dkwCount_mono x
    rw [empiricalCDF_eq_dkwCount] at hdev
    linarith

/-- The reflected closed tail is the complement of the original open tail. -/
theorem empiricalCDF_reflect {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (t : ℝ) :
    empiricalCDF (fun i => 1 - x i) (1 - t) = 1 - empiricalCDFLeft x t := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have he : (fun i : Fin n => if 1 - x i ≤ 1 - t then (1 : ℝ) else 0) =
      (fun i => 1 - (if x i < t then (1 : ℝ) else 0)) := by
    funext i
    by_cases h : x i < t
    · simp [h, show ¬ 1 - x i ≤ 1 - t by linarith]
    · simp [h, show 1 - x i ≤ 1 - t by linarith]
  unfold empiricalCDF empiricalCDFLeft
  rw [he, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp

theorem empiricalCDFLeft_le {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    empiricalCDFLeft x t ≤ empiricalCDF x t := by
  unfold empiricalCDFLeft empiricalCDF
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum
  intro i _
  by_cases h : x i < t
  · simp [h, h.le]
  · simp only [if_neg h]
    split <;> norm_num

/-- Reflection turns a lower deviation into an upper deviation, including ties. -/
theorem empiricalCDF_lower_reflect_upper {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) {ε t : ℝ} (hdev : ε < t - empiricalCDF x t) :
    ε < empiricalCDF (fun i => 1 - x i) (1 - t) - (1 - t) := by
  rw [empiricalCDF_reflect hn]
  have hh := empiricalCDFLeft_le x t
  linarith

/-- A likelihood-weight lower bound when a closed tail contains at least k points. -/
theorem dkwProductWeight_exp_lower {n k : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) {u ℓ c : ℝ} (hu : 0 < u) (hℓ : 0 ≤ ℓ)
    (hk : k ≤ dkwCount x u)
    (hc : Real.log (1 + ℓ) + ((k : ℝ) / n) *
      (Real.log u - Real.log (u + ℓ)) ≤ c) :
    Real.exp ((n : ℝ) * (Real.log (1 + ℓ) - c)) ≤ dkwProductWeight u ℓ x := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hul : 0 < u + ℓ := add_pos_of_pos_of_nonneg hu hℓ
  have hb : 0 < 1 + ℓ / u := by positivity
  have hlog : Real.log (1 + ℓ / u) = Real.log (u + ℓ) - Real.log u := by
    rw [← Real.log_div hul.ne' hu.ne']
    congr 1
    field_simp
  have hlog0 : 0 ≤ Real.log (1 + ℓ / u) := Real.log_nonneg (by have h := div_nonneg hℓ hu.le; linarith)
  have hkc : (n : ℝ) * ((k : ℝ) / n) = k := by field_simp
  have hh := mul_le_mul_of_nonneg_left hc hnR.le
  have hbound : (n : ℝ) * (Real.log (1 + ℓ) - c) ≤
      (k : ℝ) * Real.log (1 + ℓ / u) := by
    rw [mul_add, ← mul_assoc, hkc] at hh
    rw [hlog]
    nlinarith
  calc
    Real.exp ((n : ℝ) * (Real.log (1 + ℓ) - c)) ≤
        Real.exp ((k : ℝ) * Real.log (1 + ℓ / u)) := Real.exp_le_exp.mpr hbound
    _ ≤ Real.exp ((dkwCount x u : ℝ) * Real.log (1 + ℓ / u)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hlog0
    _ = dkwProductWeight u ℓ x := by
      rw [Real.exp_nat_mul, Real.exp_log hb, dkwProductWeight_eq_pow]

/-- Reflection preserves the uniform law, including its endpoints. -/
theorem dkwUniformLaw_reflect : dkwUniformLaw.map (fun x => 1 - x) = dkwUniformLaw := by
  have hm : Measurable (fun x : ℝ => 1 - x) := by fun_prop
  have he : (fun x : ℝ => 1 - x) ⁻¹' Icc 0 1 = Icc 0 1 := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith
  change (volume.restrict (Icc 0 1)).map (fun x : ℝ => 1 - x) = volume.restrict (Icc 0 1)
  rw [← he, ← Measure.restrict_map hm measurableSet_Icc,
    (volume.measurePreserving_sub_left 1).map_eq, he]

/-- Coordinatewise reflection as an involutive measurable equivalence. -/
def dkwReflectEquiv (n : ℕ) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) where
  toFun x i := 1 - x i
  invFun x i := 1 - x i
  left_inv x := by funext i; dsimp; ring
  right_inv x := by funext i; dsimp; ring
  measurable_toFun := by change Measurable (fun x : Fin n → ℝ => fun i => 1 - x i); fun_prop
  measurable_invFun := by change Measurable (fun x : Fin n → ℝ => fun i => 1 - x i); fun_prop

theorem dkwProductLaw_reflect (n : ℕ) :
    (dkwProductLaw n).map (dkwReflectEquiv n) = dkwProductLaw n := by
  change (Measure.pi (fun _ : Fin n => dkwUniformLaw)).map
    (fun x i => 1 - x i) = Measure.pi (fun _ : Fin n => dkwUniformLaw)
  rw [Measure.pi_map_pi (μ := fun _ : Fin n => dkwUniformLaw)
    (f := fun _ : Fin n => fun x : ℝ => 1 - x) (fun _ => by fun_prop)]
  simp only [dkwUniformLaw_reflect]

end LectureNotes
