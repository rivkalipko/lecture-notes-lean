import LectureNotes.TwoSampleVectorCLT

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology MatrixProbability Matrix.Norms.Elementwise

/-- L10's balance covariance for a common within-group covariance matrix. -/
def covariateBalanceCovariance {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (γ : ℝ) :=
  γ⁻¹ • S + (1 - γ)⁻¹ • S

/-- The actual two-sample Wald balance test under an independent IID
superpopulation model. Both population means and covariances agree under the
null. The covariance estimator need not be independent of the group means. -/
theorem covariate_balance_wald_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (hd : 0 < d)
    {X Y : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : MemLp (X 0) 2 P) (hY : MemLp (Y 0) 2 P)
    (hindX : iIndepFun X P) (hindY : iIndepFun Y P)
    (hidentX : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hXY : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P)
    (m n : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hmp : ∀ k, 0 < m k) (hnp : ∀ k, 0 < n k)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (hfrac : Tendsto (fun k => (m k : ℝ) / (m k + n k)) atTop (𝓝 γ))
    (hnull : P[X 0] = P[Y 0])
    (hcommon : vectorCovariance P (X 0) = vectorCovariance P (Y 0))
    (hV : (covariateBalanceCovariance (vectorCovariance P (X 0)) γ).PosDef)
    {Vhat : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ}
    (hVhat : TendstoInMeasure P Vhat atTop
      (fun _ => covariateBalanceCovariance (vectorCovariance P (X 0)) γ))
    (hVm : ∀ k, AEMeasurable (Vhat k) P)
    {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun k => P.real {ω | ((m k : ℝ) + n k) * matrixQuadratic (Vhat k ω)⁻¹
      (vectorPrefixMean X (m k) ω - vectorPrefixMean Y (n k) ω) ≤
        distributionQuantile (chiSquared d) q}) atTop (𝓝 q) := by
  have hclt := two_sample_vector_mean_clt hX hY hindX hindY hidentX hidentY hXY
    m n hm hn hmp hnp hγ hfrac
  have hlaw := two_sample_vector_limit_law
    (vectorCovariance_posSemidef hX) (vectorCovariance_posSemidef hY) hγ
  rw [← hcommon] at hlaw hclt
  change HasLaw _ (multivariateGaussian 0
    (covariateBalanceCovariance (vectorCovariance P (X 0)) γ)) _ at hlaw
  have hh := vector_wald_coverage hd hV hclt hlaw hVhat hVm hq
  simpa only [hnull, sub_self, sub_zero, matrixQuadratic_smul,
    Real.sq_sqrt (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))] using! hh

end LectureNotes
