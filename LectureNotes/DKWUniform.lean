import LectureNotes.DKWGrid
import LectureNotes.DKWEvents
import LectureNotes.DKWQuasiconcavity

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

def dkwUpperEvent (n : ℕ) (ε : ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ t ∈ Icc (0 : ℝ) 1, ε < empiricalCDF x t - t}

/-- A single tilt controls all of the count thresholds simultaneously. -/
theorem dkw_uniform_upper_bound_slack {n : ℕ} (hn : 0 < n) {ε η : ℝ}
    (hε : ε ∈ Ioo 0 1) (hη : 0 < η) :
    (dkwProductLaw n).real (dkwUpperEvent n ε) ≤
      Real.exp ((n : ℝ) * (-2 * ε ^ 2 + η)) := by
  classical
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let K : Finset ℕ := (Finset.range (n + 1)).filter (fun k : ℕ => ε < (k : ℝ) / n)
  let s := K.image (fun k : ℕ => (k : ℝ) / n - ε)
  have hsn : 1 - ε ∈ s := by
    apply Finset.mem_image.mpr
    refine ⟨n, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by simpa [hnR.ne'] using hε.2⟩
    · simp [hnR.ne']
  have hs : s.Nonempty := ⟨_, hsn⟩
  have hs0 : ∀ u ∈ s, 0 < u := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
    exact sub_pos.mpr (Finset.mem_filter.mp hk).2
  have hs1 : ∀ u ∈ s, u + ε ≤ 1 := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
    have hkN : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
    have hp : (k : ℝ) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hkN)
    linarith
  let a := s.min' hs + ε
  have ha : a ∈ Ioc ε 1 := by
    have hm := Finset.min'_mem s hs
    exact ⟨by have hh := hs0 _ hm; dsimp [a]; linarith, hs1 _ hm⟩
  obtain ⟨ℓ, hℓ, hparam⟩ := dkwLogBound_uniform_parameter hε ha hη
  change 0 ≤ ℓ at hℓ
  let c := -2 * ε ^ 2 + η
  let b := Real.exp ((n : ℝ) * (Real.log (1 + ℓ) - c))
  have hb : 0 < b := Real.exp_pos _
  have hcross := dkw_finite_grid_crossing_bound (n := n) s hs0
    (fun u hu => by have h := hs1 u hu; linarith [hε.1]) hℓ hb
  have hsubset : dkwUpperEvent n ε ⊆ {x | ∃ u ∈ s, b ≤ dkwProductWeight u ℓ x} := by
    intro x hx
    rcases hx with ⟨t, ht, hdev⟩
    obtain ⟨k, hkN, hkp, hk⟩ := empiricalCDF_upper_count_witness hn x ht.1 hdev
    have hu : (k : ℝ) / n - ε ∈ s := Finset.mem_image.mpr
      ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hkN), hkp⟩, rfl⟩
    refine ⟨_, hu, dkwProductWeight_exp_lower hn x (sub_pos.mpr hkp) hℓ hk ?_⟩
    have hlo : a ≤ (k : ℝ) / n := by
      have hh := Finset.min'_le s _ hu
      dsimp [a]
      linarith
    have hhi : (k : ℝ) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hkN)
    exact (hparam _ ⟨hlo, hhi⟩).le
  have he : (1 + ℓ) ^ n / b = Real.exp ((n : ℝ) * c) := by
    have hbase : 0 < 1 + ℓ := by linarith
    have hexp : (1 + ℓ) ^ n = Real.exp ((n : ℝ) * Real.log (1 + ℓ)) := by
      rw [Real.exp_nat_mul, Real.exp_log hbase]
    dsimp only [b]
    rw [hexp, ← Real.exp_sub]
    congr 1
    ring
  exact (measureReal_mono hsubset).trans (hcross.trans_eq he)

/-- Sharp one-sided empirical-CDF bound for IID uniform observations. -/
theorem dkw_uniform_upper_bound {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (dkwProductLaw n).real (dkwUpperEvent n ε) ≤ Real.exp (-2 * n * ε ^ 2) := by
  by_cases he : ε < 1
  · have hc : Continuous (fun η : ℝ => Real.exp ((n : ℝ) * (-2 * ε ^ 2 + η))) := by fun_prop
    have hl := (hc.continuousAt (x := 0)).continuousWithinAt (s := Ioi (0 : ℝ))
    have hh : (dkwProductLaw n).real (dkwUpperEvent n ε) ≤
        Real.exp ((n : ℝ) * (-2 * ε ^ 2 + 0)) := by
      apply ge_of_tendsto hl
      filter_upwards [self_mem_nhdsWithin] with η hη
      exact dkw_uniform_upper_bound_slack hn ⟨hε, he⟩ hη
    convert hh using 1 <;> congr 1 <;> ring
  · have hempty : dkwUpperEvent n ε = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      rcases hx with ⟨t, ht, hdev⟩
      have hh := empiricalCDF_le_one hn x t
      linarith [ht.1]
    rw [hempty, measureReal_empty]
    exact (Real.exp_pos _).le

/-- The sharp two-sided DKW bound on [0,1]. No union over grid points is
used: Doob's inequality bounds the simultaneous crossing event. -/
theorem dkw_uniform_two_sided_bound {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (dkwProductLaw n).real {x | ∃ t ∈ Icc (0 : ℝ) 1,
      ε < |empiricalCDF x t - t|} ≤ 2 * Real.exp (-2 * n * ε ^ 2) := by
  let A := dkwUpperEvent n ε
  let R := dkwReflectEquiv n
  have hs : {x : Fin n → ℝ | ∃ t ∈ Icc (0 : ℝ) 1, ε < |empiricalCDF x t - t|} ⊆
      A ∪ R ⁻¹' A := by
    intro x hx
    rcases hx with ⟨t, ht, hdev⟩
    by_cases hsign : 0 ≤ empiricalCDF x t - t
    · left
      exact ⟨t, ht, by rwa [abs_of_nonneg hsign] at hdev⟩
    · right
      refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      apply empiricalCDF_lower_reflect_upper hn x
      rw [abs_of_neg (lt_of_not_ge hsign)] at hdev
      linarith
  have href : (dkwProductLaw n).real (R ⁻¹' A) = (dkwProductLaw n).real A := by
    have hh := (dkwReflectEquiv n).map_apply (μ := dkwProductLaw n) A
    rw [dkwProductLaw_reflect] at hh
    exact congrArg ENNReal.toReal hh.symm
  calc
    _ ≤ (dkwProductLaw n).real (A ∪ R ⁻¹' A) := measureReal_mono hs
    _ ≤ (dkwProductLaw n).real A + (dkwProductLaw n).real (R ⁻¹' A) := measureReal_union_le _ _
    _ = 2 * (dkwProductLaw n).real A := by rw [href]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (dkw_uniform_upper_bound hn hε) (by norm_num)

end LectureNotes
