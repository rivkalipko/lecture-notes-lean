import LectureNotes.ExponentialMLE
import LectureNotes.BootstrapMoments

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- A method-of-moments estimator obtained by inverting a scalar population
moment. The identification equation is imposed in the theorems below. -/
def momentInverseEstimator {Ω α : Type*} (g : α → ℝ) (inverse : ℝ → ℝ)
    (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) : ℝ :=
  inverse ((∑ i ∈ Finset.range n, g (X i ω)) / n)

/-- L6: continuity of the inverse at the population moment gives consistency;
the sample moment law of large numbers is derived from IID observations. -/
theorem moment_inverse_strong_consistency {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {inverse : ℝ → ℝ} {Y : ℕ → Ω → ℝ}
    (hYint : Integrable (Y 0) P) (hind : iIndepFun Y P)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    {θ : ℝ} (hinverse : ContinuousAt inverse P[Y 0])
    (hid : inverse P[Y 0] = θ) :
    ConvergesAlmostSurely P (momentInverseEstimator id inverse Y) (fun _ => θ) := by
  have hlln := strong_law_of_large_numbers hYint (fun i j hij => hind.indepFun hij) hident
  filter_upwards [hlln] with ω hω
  simpa only [momentInverseEstimator, id_eq, hid, Function.comp_def] using! hinverse.tendsto.comp hω

/-- The moment equation is solved exactly whenever the supplied functions
are inverses on the observed sample moment. -/
theorem moment_inverse_solves {Ω α : Type*} (g : α → ℝ) (inverse moment : ℝ → ℝ)
    (X : ℕ → Ω → α) (n : ℕ) (ω : Ω)
    (hinv : Function.RightInverse inverse moment) :
    moment (momentInverseEstimator g inverse X n ω) =
      (∑ i ∈ Finset.range n, g (X i ω)) / n := hinv _

/-- L6: the inverse-moment estimator's limit follows from the observation CLT
and the delta method; no estimator convergence premise is imposed. -/
theorem moment_inverse_asymptotic_normality {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {Y : ℕ → Ω → ℝ} (hYm : ∀ i, Measurable (Y i)) (hY : MemLp (Y 0) 2 P)
    (hind : iIndepFun Y P) (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    {inverse : ℝ → ℝ} (hinverse : Continuous inverse)
    (hderiv : DifferentiableAt ℝ inverse P[Y 0]) {θ : ℝ} (hid : inverse P[Y 0] = θ)
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 Var[Y 0; P].toNNReal) Q) :
    ConvergesInDistribution P Q
      (fun n ω => Real.sqrt n * (momentInverseEstimator id inverse Y n ω - θ))
      (fun ω => Z ω * deriv inverse P[Y 0]) ∧
    HasLaw (fun ω => Z ω * deriv inverse P[Y 0])
      (gaussianReal 0 (⟨(deriv inverse P[Y 0]) ^ 2, sq_nonneg _⟩ * Var[Y 0; P].toNNReal)) Q := by
  let M (n : ℕ) (ω : Ω) := (∑ i ∈ Finset.range n, Y i ω) / n
  have hMm n : Measurable (M n) := by dsimp [M]; fun_prop
  have hCLT := central_limit_theorem hZ hY hind hident
  have hc : ConvergesInDistribution P Q (fun n ω => Real.sqrt n * (M n ω - P[Y 0])) Z := by
    apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl)) hCLT
    intro n
    apply ae_of_all
    intro ω
    dsimp only
    by_cases hn : n = 0
    · simp [hn]
    · rw [← sqrt_times_average]
      dsimp only [M]
      have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      field_simp
  constructor
  · have hh := delta_method (fun n => (hMm n).aemeasurable)
      (show ∀ᶠ n : ℕ in atTop, Real.sqrt n ≠ 0 from by
        filter_upwards [eventually_gt_atTop 0] with n hn
        exact (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne')
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
      hc hinverse hderiv
    simpa only [momentInverseEstimator, id_eq, M, hid] using hh
  · simpa only [mul_zero] using! gaussianReal_mul_const hZ (deriv inverse P[Y 0])

/-- The two normal moment equations have exactly the displayed solution. -/
theorem normal_moment_equations {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (μ v : ℝ) :
    (sampleMean x = μ ∧ sampleMean (fun i => x i ^ 2) = μ ^ 2 + v) ↔
      (μ = sampleMean x ∧ v = empiricalVariance x) := by
  have hvar := empiricalVariance_eq_secondMoment_sub_sq x
  constructor
  · rintro ⟨hμ, hv⟩
    exact ⟨hμ.symm, by rw [hμ] at hvar; linarith⟩
  · rintro ⟨rfl, hv⟩
    exact ⟨rfl, by linarith⟩

/-- The alternative exponential moment equation uses the actual second moment. -/
theorem exponential_second_moment {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ, x ^ 2 ∂expMeasure r) = 2 / r ^ 2 := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have h := variance_eq_second_moment_sub_mean_sq (expMeasure r) (exponential_memLp_two hr)
  rw [exponential_variance hr] at h
  simp only [id_eq] at h
  rw [exponential_mean hr] at h
  have hs : (1 / r) ^ 2 = 1 / r ^ 2 := by ring
  rw [hs] at h
  linear_combination -h

/-- Positive-rate identification from the first exponential moment. -/
theorem exponential_first_moment_inverse {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    m = 1 / r ↔ r = 1 / m := by
  constructor <;> intro h
  · rw [h]
    field_simp
  · rw [h]
    field_simp

/-- Positive-rate identification from the second exponential moment. -/
theorem exponential_second_moment_inverse {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    m = 2 / r ^ 2 ↔ r = Real.sqrt (2 / m) := by
  have hs : (Real.sqrt (2 / m)) ^ 2 = 2 / m := Real.sq_sqrt (by positivity)
  have hpos : 0 < Real.sqrt (2 / m) := Real.sqrt_pos.mpr (by positivity)
  constructor
  · intro h
    have hh : r ^ 2 = 2 / m := by rw [h]; field_simp
    nlinarith
  · intro h
    rw [h, hs]
    field_simp

end LectureNotes
