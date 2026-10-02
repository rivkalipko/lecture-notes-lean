import LectureNotes.VectorDeltaMethod
import LectureNotes.VectorMLE

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped Topology

/-- Invert the vector of empirical moments, allowing dependence among
coordinates of the moment vector from a single observation. -/
def vectorMomentInverseEstimator {Ω α : Type*} {d : ℕ}
    (g : α → EuclideanSpace ℝ (Fin d))
    (inverse : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  inverse ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, g (X i ω))

/-- Vector inverse-moment consistency follows from the vector strong law and
continuity at the population moment. -/
theorem vector_moment_inverse_strong_consistency {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {X : ℕ → Ω → α} (g : α → EuclideanSpace ℝ (Fin d))
    (hg : Measurable g) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hint : Integrable (fun ω => g (X 0 ω)) P)
    {inverse : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hi : ContinuousAt inverse (∫ ω, g (X 0 ω) ∂P)) {θ : EuclideanSpace ℝ (Fin d)}
    (hid : inverse (∫ ω, g (X 0 ω) ∂P) = θ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => vectorMomentInverseEstimator g inverse X n ω) atTop (𝓝 θ) := by
  have hh := strong_law_ae (fun i ω => g (X i ω)) hint
    (fun i j hij => (hind.comp (fun _ => g) (fun _ => hg)).indepFun hij)
    (fun i => (hident i).comp hg)
  filter_upwards [hh] with ω hω
  simpa only [vectorMomentInverseEstimator, hid, Function.comp_def] using hi.tendsto.comp hω

/-- The observed empirical moments solve the original equations whenever
the inverse is a right inverse of the population moment map. -/
theorem vector_moment_inverse_solves {Ω α : Type*} {d : ℕ}
    (g : α → EuclideanSpace ℝ (Fin d))
    (inverse moment : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) (hi : Function.RightInverse inverse moment) :
    moment (vectorMomentInverseEstimator g inverse X n ω) =
      (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, g (X i ω) := hi _

/-- L6's vector inverse-moment asymptotic law. The covariance is A S Aᵀ,
where S is the actual covariance of the observation's moment vector and A
is the derivative matrix of the inverse. Singular limits are allowed. -/
theorem vector_moment_inverse_asymptotic_normality {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {X : ℕ → Ω → α} (g : α → EuclideanSpace ℝ (Fin d))
    (hXm : ∀ i, Measurable (X i)) (hg : Measurable g) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (h₂ : MemLp (fun ω => g (X 0 ω)) 2 P)
    {inverse : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hi : Continuous inverse)
    (D : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hd : HasFDerivAt inverse D (∫ ω, g (X 0 ω) ∂P))
    {θ : EuclideanSpace ℝ (Fin d)} (hid : inverse (∫ ω, g (X 0 ω) ∂P) = θ) :
    let S := vectorCovariance P (fun ω => g (X 0 ω))
    let A := (toEuclideanCLM (𝕜 := ℝ)).symm D
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n • (vectorMomentInverseEstimator g inverse X n ω - θ))
      atTop D (fun _ => P) (multivariateGaussian 0 S) ∧
    HasLaw D (multivariateGaussian 0 (A * S * Aᵀ)) (multivariateGaussian 0 S) := by
  dsimp only
  let Y (i : ℕ) (ω : Ω) := g (X i ω)
  let μ := ∫ ω, g (X 0 ω) ∂P
  let M (n : ℕ) (ω : Ω) := (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, g (X i ω)
  have hMm n : Measurable (M n) := by dsimp [M]; fun_prop
  have hM := iid_vector_statistic_average_limit X g hXm hg hind hident (h₂.integrable (by norm_num))
  have hCLT := multivariate_clt_covariance h₂
    (hind.comp (fun _ => g) (fun _ => hg)) (fun i => (hident i).comp hg)
  have he (n : ℕ) (ω : Ω) :
      Real.sqrt n • (M n ω - μ) = (Real.sqrt n)⁻¹ •
        ((∑ i ∈ Finset.range n, g (X i ω)) - (n : ℝ) • μ) := by
    have h1 : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
      simpa only [div_eq_mul_inv, one_mul, mul_one] using sqrt_times_average n 1
    have h2 : (Real.sqrt n)⁻¹ * (n : ℝ) = Real.sqrt n := by
      calc
        _ = (Real.sqrt n)⁻¹ * (Real.sqrt n) ^ 2 := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]
        _ = _ := by
          by_cases hs : Real.sqrt (n : ℝ) = 0
          · simp [hs]
          · field_simp
    simp only [M, smul_sub, smul_smul, h1, h2]
  have hCLT' : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (M n ω - μ))
      atTop id (fun _ => P) (multivariateGaussian 0 (vectorCovariance P (fun ω => g (X 0 ω)))) := by
    simpa only [he, μ, Function.comp_def] using hCLT
  constructor
  · have h := vector_delta_method (fun n => (hMm n).aemeasurable) hM hCLT' hi hd
    simpa only [M, μ, hid, vectorMomentInverseEstimator, id_eq] using h
  · have h := gaussian_clm_transform (vectorCovariance_posSemidef h₂)
      (HasLaw.id : HasLaw id (multivariateGaussian 0 (vectorCovariance P (fun ω => g (X 0 ω))))
        (multivariateGaussian 0 (vectorCovariance P (fun ω => g (X 0 ω))))) D
    simpa only [id_eq, map_zero] using h

end LectureNotes
