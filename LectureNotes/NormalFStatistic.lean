import LectureNotes.NormalSamplingDistribution

/-! L2 p8: the F statistic for two independent normal samples. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Divide the sample-variance ratio by the population-variance ratio. -/
theorem normal_fStatistic {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n m : ℕ} (hn : 1 < n) (hm : 1 < m)
    {X : Fin n → Ω → ℝ} {Y : Fin m → Ω → ℝ} {μX μY : ℝ} {vX vY : ℝ≥0}
    (hvX : 0 < vX) (hvY : 0 < vY)
    (hX : ∀ i, HasLaw (X i) (gaussianReal μX vX) P)
    (hY : ∀ j, HasLaw (Y j) (gaussianReal μY vY) P)
    (hiX : iIndepFun X P) (hiY : iIndepFun Y P)
    (hXY : IndepFun (fun ω i => X i ω) (fun ω j => Y j ω) P) :
    HasLaw (fun ω => (sampleVariance (fun i => X i ω) / sampleVariance (fun j => Y j ω)) /
      ((vX : ℝ) / vY)) (fDistribution (n - 1) (m - 1)) P := by
  have hQX := normal_sampleVariance hn hvX hX hiX
  have hQY := normal_sampleVariance hm hvY hY hiY
  have hiQ := hXY.comp
    (show Measurable (fun x : Fin n → ℝ => ((n : ℝ) - 1) * sampleVariance x / vX) by
      unfold sampleVariance sampleMean
      fun_prop)
    (show Measurable (fun y : Fin m → ℝ => ((m : ℝ) - 1) * sampleVariance y / vY) by
      unfold sampleVariance sampleMean
      fun_prop)
  have hF := fDistribution_ratio (by omega : 0 < n - 1) (by omega : 0 < m - 1) hQX hQY hiQ
  apply hF.congr
  filter_upwards [normal_sampleVariance_pos hm hvY hY hiY] with ω hpos
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < m := by exact_mod_cast hm
    linarith
  have hvXR : (vX : ℝ) ≠ 0 := by exact_mod_cast hvX.ne'
  have hvYR : (vY : ℝ) ≠ 0 := by exact_mod_cast hvY.ne'
  simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  field_simp [hpos.ne', hn1, hm1, hvXR, hvYR]

end LectureNotes
