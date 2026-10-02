import LectureNotes.IndependentLimits
import LectureNotes.GaussianIndependentContrasts
import LectureNotes.VectorSampleMeans

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology MatrixProbability Matrix.Norms.Elementwise

/-- The treated/control allocation fractions are complementary for every
positive pair of sample sizes. -/
theorem two_sample_control_fraction (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (n : ℝ) / (m + n) = 1 - (m : ℝ) / (m + n) := by
  have h : (m : ℝ) + n ≠ 0 := by positivity
  field_simp
  ring

/-- L10's two-group vector mean CLT, derived from actual independent IID
samples. Group sizes may vary, with an interior limiting allocation fraction.
Within-vector covariances and singular marginal covariance matrices are allowed. -/
theorem two_sample_vector_mean_clt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    {X Y : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : MemLp (X 0) 2 P) (hY : MemLp (Y 0) 2 P)
    (hindX : iIndepFun X P) (hindY : iIndepFun Y P)
    (hidentX : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hXY : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P)
    (m n : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hmp : ∀ k, 0 < m k) (hnp : ∀ k, 0 < n k)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (hfrac : Tendsto (fun k => (m k : ℝ) / (m k + n k)) atTop (𝓝 γ)) :
    TendstoInDistribution (fun k ω => Real.sqrt ((m k : ℝ) + n k) •
      ((vectorPrefixMean X (m k) ω - vectorPrefixMean Y (n k) ω) - (P[X 0] - P[Y 0])))
      atTop (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        (Real.sqrt γ)⁻¹ • z.1 - (Real.sqrt (1 - γ))⁻¹ • z.2) (fun _ => P)
      ((multivariateGaussian 0 (vectorCovariance P (X 0))).prod
        (multivariateGaussian 0 (vectorCovariance P (Y 0)))) := by
  let EX k ω := Real.sqrt (m k) • (vectorPrefixMean X (m k) ω - P[X 0])
  let EY k ω := Real.sqrt (n k) • (vectorPrefixMean Y (n k) ω - P[Y 0])
  have hEX := distribution_limit_subsequence (vectorPrefixMean_clt hX hindX hidentX) hm
  have hEY := distribution_limit_subsequence (vectorPrefixMean_clt hY hindY hidentY) hn
  have hi k : IndepFun (EX k) (EY k) P :=
    (independent_vectorPrefixMeans hXY (m k) (n k)).comp
      (by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin d) => Real.sqrt (m k) • (z - P[X 0])))
      (by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin d) => Real.sqrt (n k) • (z - P[Y 0])))
  have hj := independent_joint_limit hEX hEY hi
  let a k := (Real.sqrt ((m k : ℝ) / (m k + n k)))⁻¹
  let b k := (Real.sqrt ((n k : ℝ) / (m k + n k)))⁻¹
  have ha : Tendsto a atTop (𝓝 (Real.sqrt γ)⁻¹) :=
    ((Real.continuous_sqrt.continuousAt.tendsto).comp hfrac).inv₀ (Real.sqrt_pos.mpr hγ.1).ne'
  have hc : Tendsto (fun k => (n k : ℝ) / (m k + n k)) atTop (𝓝 (1 - γ)) := by
    simp_rw [two_sample_control_fraction (m _) (n _) (hmp _) (hnp _)]
    exact tendsto_const_nhds.sub hfrac
  have hb : Tendsto b atTop (𝓝 (Real.sqrt (1 - γ))⁻¹) :=
    ((Real.continuous_sqrt.continuousAt.tendsto).comp hc).inv₀
      (Real.sqrt_pos.mpr (sub_pos.mpr hγ.2)).ne'
  have hab : TendstoInMeasure P (fun k _ω => (a k, b k)) atTop
      (fun _ => ((Real.sqrt γ)⁻¹, (Real.sqrt (1 - γ))⁻¹)) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ (fun _ => ha.prodMk_nhds hb))
  have h := hj.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun z : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × (ℝ × ℝ) =>
      z.2.1 • z.1.1 - z.2.2 • z.1.2) (by fun_prop) hab (fun _ => aemeasurable_const)
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl)) h
  intro k
  apply ae_of_all
  intro ω
  have hmR : (0 : ℝ) < m k := by exact_mod_cast hmp k
  have hnR : (0 : ℝ) < n k := by exact_mod_cast hnp k
  have hsm : Real.sqrt (m k) ≠ 0 := (Real.sqrt_pos.mpr hmR).ne'
  have hsn : Real.sqrt (n k) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  have hae : a k * Real.sqrt (m k) = Real.sqrt ((m k : ℝ) + n k) := by
    dsimp only [a]
    rw [Real.sqrt_div hmR.le, inv_div]
    field_simp
  have hbe : b k * Real.sqrt (n k) = Real.sqrt ((m k : ℝ) + n k) := by
    dsimp only [b]
    rw [Real.sqrt_div hnR.le, inv_div]
    field_simp
  change a k • (Real.sqrt (m k) • _) - b k • (Real.sqrt (n k) • _) = _
  rw [smul_smul, smul_smul, hae, hbe, ← smul_sub]
  congr 1
  abel

/-- The limiting two-group Gaussian covariance has the exact inverse
allocation weights printed in the notes. -/
theorem two_sample_vector_limit_law {d : ℕ} {S T : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    HasLaw (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        (Real.sqrt γ)⁻¹ • z.1 - (Real.sqrt (1 - γ))⁻¹ • z.2)
      (multivariateGaussian 0 (γ⁻¹ • S + (1 - γ)⁻¹ • T))
      ((multivariateGaussian 0 S).prod (multivariateGaussian 0 T)) := by
  simpa only [inv_pow, Real.sq_sqrt hγ.1.le, Real.sq_sqrt (sub_nonneg.mpr hγ.2.le)] using
    gaussian_product_contrast hS hT (Real.sqrt γ)⁻¹ (Real.sqrt (1 - γ))⁻¹

end LectureNotes
