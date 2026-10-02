import LectureNotes.VectorScoreCLT

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- The vector mean of the first n observations, with value zero at n=0. -/
def vectorPrefixMean {Ω : Type*} {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (n : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) := (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω

theorem sqrt_vectorPrefixMean {Ω : Type*} {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (n : ℕ) (ω : Ω)
    (μ : EuclideanSpace ℝ (Fin d)) :
    Real.sqrt n • (vectorPrefixMean X n ω - μ) =
      (Real.sqrt n)⁻¹ • ((∑ i ∈ Finset.range n, X i ω) - (n : ℝ) • μ) := by
  by_cases hn : n = 0
  · simp [hn, vectorPrefixMean]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hs : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    have he : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
      field_simp
      exact Real.sq_sqrt (Nat.cast_nonneg n)
    have he' : (Real.sqrt n)⁻¹ * (n : ℝ) = Real.sqrt n := by
      field_simp
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
    simp only [vectorPrefixMean, smul_sub, smul_smul, he, he']

/-- The actual finite-second-moment vector sample-mean CLT, with its
canonical covariance, including degenerate covariance matrices. -/
theorem vectorPrefixMean_clt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : MemLp (X 0) 2 P) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : ℕ) ω =>
      Real.sqrt n • (vectorPrefixMean X n ω - P[X 0])) atTop id (fun _ => P)
      (multivariateGaussian 0 (vectorCovariance P (X 0))) := by
  simpa only [sqrt_vectorPrefixMean] using multivariate_clt_covariance hX hind hident

/-- Independent entire samples give independent means for every pair of
finite group sample sizes. -/
theorem independent_vectorPrefixMeans {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} {X Y : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    (hXY : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P) (m n : ℕ) :
    IndepFun (vectorPrefixMean X m) (vectorPrefixMean Y n) P := by
  exact hXY.comp
    (by fun_prop : Measurable (fun z : ℕ → EuclideanSpace ℝ (Fin d) =>
      (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, z i))
    (by fun_prop : Measurable (fun z : ℕ → EuclideanSpace ℝ (Fin d) =>
      (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, z i))

end LectureNotes
