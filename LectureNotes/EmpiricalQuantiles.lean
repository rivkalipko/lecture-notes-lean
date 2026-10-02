import LectureNotes.Bootstrap
import LectureNotes.OrderStatistics
import LectureNotes.DKWEvents
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- Sorting preserves the empirical probability law, with multiplicities. -/
theorem empiricalLaw_sortedSample {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    empiricalLaw (sortedSample x).val = empiricalLaw x := by
  apply Measure.eq_of_cdf
  ext t
  rw [empiricalLaw_cdf, empiricalLaw_cdf]
  unfold empiricalCDF
  congr 1
  exact Equiv.sum_comp (Tuple.sort x) (fun a => if x a ≤ t then (1 : ℝ) else 0)

/-- A sorted empirical quantile is the k-th zero-based order statistic when
k/n < q ≤ (k+1)/n, including tied observations. -/
theorem empirical_quantile_rank {n : ℕ} [NeZero n]
    (x : Fin n → ℝ) (hmono : Monotone x) (k : Fin n) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hlo : (k : ℝ) / n < q) (hhi : q ≤ ((k : ℝ) + 1) / n) :
    distributionQuantile (empiricalLaw x) q = x k := by
  classical
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  apply le_antisymm
  · apply (distributionQuantile_le_iff (empiricalLaw x) hq).mpr
    rw [empiricalLaw_cdf, empiricalCDF_eq_dkwCount]
    apply hhi.trans
    apply div_le_div_of_nonneg_right _ hnR.le
    have hcount : k.val + 1 ≤ dkwCount x (x k) := by
      calc
        k.val + 1 = (Finset.Iic k).card := (Fin.card_Iic k).symm
        _ ≤ _ := Finset.card_le_card (by
          intro j hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmono (Finset.mem_Iic.mp hj)⟩)
    exact_mod_cast hcount
  · by_contra hh
    have ht : distributionQuantile (empiricalLaw x) q < x k := lt_of_not_ge hh
    have hc : dkwCount x (distributionQuantile (empiricalLaw x) q) ≤ k.val := by
      calc
        _ ≤ (Finset.Iio k).card := Finset.card_le_card (by
          intro j hj
          apply Finset.mem_Iio.mpr
          by_contra hle
          have hm := hmono (le_of_not_gt hle)
          have hj' := (Finset.mem_filter.mp hj).2
          linarith)
        _ = k.val := Fin.card_Iio k
    have hbr := (distributionQuantile_bracket (empiricalLaw x) q hq).2
    rw [← cdf_eq_real, empiricalLaw_cdf, empiricalCDF_eq_dkwCount] at hbr
    have hle : (dkwCount x (distributionQuantile (empiricalLaw x) q) : ℝ) / n ≤ (k : ℝ) / n :=
      div_le_div_of_nonneg_right (by exact_mod_cast hc) hnR.le
    exact (not_lt_of_ge (hbr.trans hle)) hlo

/-- The correct one-based empirical-quantile rank is ceiling(n*q), not floor(n*q).
The returned `Fin` index is therefore ceiling(n*q)-1. -/
theorem empirical_quantile_ceiling {n : ℕ} [NeZero n] (x : Fin n → ℝ) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    ∃ k : Fin n, k.val + 1 = Nat.ceil ((n : ℝ) * q) ∧
      distributionQuantile (empiricalLaw x) q = (sortedSample x).val k := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hprod : 0 < (n : ℝ) * q := mul_pos hnR hq.1
  have hceil : 0 < Nat.ceil ((n : ℝ) * q) := Nat.ceil_pos.mpr hprod
  have hceilN : Nat.ceil ((n : ℝ) * q) ≤ n := Nat.ceil_le.mpr (by nlinarith [hq.2])
  let k : Fin n := ⟨Nat.ceil ((n : ℝ) * q) - 1, by omega⟩
  have hk : k.val + 1 = Nat.ceil ((n : ℝ) * q) := by dsimp [k]; omega
  have hkR : (k : ℝ) + 1 = (Nat.ceil ((n : ℝ) * q) : ℝ) := by exact_mod_cast hk
  refine ⟨k, hk, ?_⟩
  rw [← empiricalLaw_sortedSample x]
  apply empirical_quantile_rank _ (sortedSample x).property k hq
  · apply (div_lt_iff₀ hnR).mpr
    have hh := Nat.ceil_lt_add_one hprod.le
    rw [← hkR] at hh
    nlinarith
  · apply (le_div_iff₀ hnR).mpr
    have hh := Nat.le_ceil ((n : ℝ) * q)
    rw [← hkR] at hh
    nlinarith

end LectureNotes
