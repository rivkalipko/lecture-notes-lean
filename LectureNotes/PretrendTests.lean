import LectureNotes.LinearContrasts

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology MatrixProbability Matrix.Norms.Elementwise

/-- A row selects one treated/control follow-up contrast and subtracts the
same two baseline means used by every other row. Indices refer to the full
vector of group-period means. -/
def pretrendContrastMatrix {d p : ℕ} (t0 c0 : Fin d)
    (t c : Fin p → Fin d) : Matrix (Fin p) (Fin d) ℝ := fun i j =>
  (if j = t i then 1 else 0) - (if j = t0 then 1 else 0) -
    (if j = c i then 1 else 0) + (if j = c0 then 1 else 0)

/-- The placebo difference in differences displayed in L10 Example 2. -/
def pretrendEffects {d p : ℕ} (t0 c0 : Fin d) (t c : Fin p → Fin d)
    (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin p) :=
  matrixBlockMap (pretrendContrastMatrix t0 c0 t c) y

theorem pretrendEffects_apply {d p : ℕ} (t0 c0 : Fin d) (t c : Fin p → Fin d)
    (y : EuclideanSpace ℝ (Fin d)) (i : Fin p) :
    pretrendEffects t0 c0 t c y i = (y (t i) - y t0) - (y (c i) - y c0) := by
  classical
  simp only [pretrendEffects, matrixBlockMap_apply, pretrendContrastMatrix,
    add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  simp
  ring

/-- Every placebo effect vanishes exactly when the treated and control
population changes from the common baseline agree in every pre-period. -/
theorem pretrendEffects_eq_zero_iff {d p : ℕ} (t0 c0 : Fin d) (t c : Fin p → Fin d)
    (θ : EuclideanSpace ℝ (Fin d)) :
    pretrendEffects t0 c0 t c θ = 0 ↔ ∀ i, θ (t i) - θ t0 = θ (c i) - θ c0 := by
  constructor
  · intro h i
    have hi := congrArg (fun z : EuclideanSpace ℝ (Fin p) => z i) h
    simpa only [pretrendEffects_apply, PiLp.zero_apply, sub_eq_zero] using hi
  · intro h
    ext i
    simp only [pretrendEffects_apply, h i, sub_self, PiLp.zero_apply]

/-- A shared baseline induces covariance even when the three original
variables are pairwise uncorrelated. Independence across periods is not
assumed in the general pre-trend test; this identity isolates the baseline term. -/
theorem shared_baseline_covariance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {U V B : Ω → ℝ}
    (hU : MemLp U 2 P) (hV : MemLp V 2 P) (hB : MemLp B 2 P)
    (hUV : cov[U,V;P] = 0) (hUB : cov[U,B;P] = 0) (hBV : cov[B,V;P] = 0) :
    cov[fun ω => U ω - B ω, fun ω => V ω - B ω;P] = Var[B;P] := by
  rw [covariance_fun_sub_fun_sub hU hB hV hB,
    hUV, hUB, hBV, covariance_self hB.aemeasurable]
  ring

/-- L10 Example 2: a joint CLT of all group-period means implies the placebo
contrast CLT and its full covariance. Shared baseline terms are retained. -/
theorem pretrend_effects_clt {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d p : ℕ} {T : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {θ : EuclideanSpace ℝ (Fin d)}
    {Z : Ω' → EuclideanSpace ℝ (Fin d)} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef)
    (hT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ))
      atTop Z (fun _ => P) Q)
    (hZ : HasLaw Z (multivariateGaussian 0 S) Q)
    (t0 c0 : Fin d) (t c : Fin p → Fin d) :
    let A := pretrendContrastMatrix t0 c0 t c
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n • (pretrendEffects t0 c0 t c (T n ω) -
        pretrendEffects t0 c0 t c θ))
      atTop (fun ω => pretrendEffects t0 c0 t c (Z ω)) (fun _ => P) Q ∧
    HasLaw (fun ω => pretrendEffects t0 c0 t c (Z ω)) (multivariateGaussian 0 (A*S*Aᵀ)) Q :=
  linear_contrast_clt hS hT hZ (pretrendContrastMatrix t0 c0 t c)

/-- The joint pre-trend Wald acceptance event has asymptotic probability q
under the exact null. Positive definite contrast covariance and p>0 ensure
a nondegenerate chi-square calibration. -/
theorem pretrend_wald_null_coverage {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d p : ℕ} (hp : 0 < p)
    {T : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {θ : EuclideanSpace ℝ (Fin d)}
    {Z : Ω' → EuclideanSpace ℝ (Fin d)} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef)
    (hT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ))
      atTop Z (fun _ => P) Q)
    (hZ : HasLaw Z (multivariateGaussian 0 S) Q)
    (t0 c0 : Fin d) (t c : Fin p → Fin d)
    (hnull : ∀ i, θ (t i) - θ t0 = θ (c i) - θ c0)
    (hV : let A := pretrendContrastMatrix t0 c0 t c; (A*S*Aᵀ).PosDef)
    {Vhat : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ}
    (hVhat : let A := pretrendContrastMatrix t0 c0 t c;
      TendstoInMeasure P Vhat atTop (fun _ => A*S*Aᵀ))
    (hVm : ∀ n, AEMeasurable (Vhat n) P)
    {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω | n * matrixQuadratic (Vhat n ω)⁻¹
      (pretrendEffects t0 c0 t c (T n ω)) ≤ distributionQuantile (chiSquared p) q})
      atTop (𝓝 q) := by
  have hz := (pretrendEffects_eq_zero_iff t0 c0 t c θ).mpr hnull
  have h := linear_contrast_wald_coverage hp hS hT hZ
    (pretrendContrastMatrix t0 c0 t c) hV hVhat hVm hq
  change Tendsto (fun n => P.real {ω | n * matrixQuadratic (Vhat n ω)⁻¹
    (pretrendEffects t0 c0 t c (T n ω) - pretrendEffects t0 c0 t c θ) ≤
      distributionQuantile (chiSquared p) q}) atTop (𝓝 q) at h
  simpa only [hz, sub_zero] using h

end LectureNotes
