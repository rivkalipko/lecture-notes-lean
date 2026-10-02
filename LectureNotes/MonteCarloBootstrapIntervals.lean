import LectureNotes.TriangularMonteCarlo
import LectureNotes.RowCriticalValues
import LectureNotes.BootstrapSmoothMomentIntervals
import LectureNotes.BootstrapVarianceIntervals
import LectureNotes.BootstrapMeanIntervals

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- A positive scaling of a finite simulation sample scales its generalized
quantile exactly, including ties and discrete simulation laws. -/
theorem empirical_quantile_positive_scale {m : ℕ} [NeZero m] (y : Fin m → ℝ)
    (c : ℝ) (hc : 0 < c) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    distributionQuantile (empiricalLaw (fun j => c * y j)) q =
      c * distributionQuantile (empiricalLaw y) q := by
  let e := OrderIso.mulLeft₀ c hc
  have he : empiricalLaw (fun j => c * y j) = (empiricalLaw y).map e :=
    (empiricalLaw_map_statistic y (show Measurable e from by fun_prop)).symm
  rw [he, distributionQuantile_orderIso _ e hq]
  rfl

/-- Data and independent simulation seeds form the actual product experiment.
Monte Carlo quantile consistency and the sampling CLT yield joint coverage;
no coupling of experiments of different sizes is required. -/
theorem monteCarlo_interval_coverage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Γ : ℕ → Type*}
    [∀ n, MeasurableSpace (Γ n)] (Q : ∀ n, Measure (Γ n))
    [∀ n, IsProbabilityMeasure (Q n)] {B : ℕ → ℕ} [∀ n, NeZero (B n)]
    (hB : Tendsto B atTop atTop) (F : ∀ n, Ω × Γ n → ℝ)
    (hF : ∀ n, Measurable (F n)) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (hstrict : StrictMono (cdf ν))
    (hconv : ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n => cdf ((Q n).map (fun γ => F n (ω, γ))) t)
      atTop (𝓝 (cdf ν t)))
    (E S : ℕ → Ω → ℝ) (θ : ℝ) (hS : ∀ n ω, 0 < S n ω)
    (hmT : ∀ n, Measurable (fun ω => (E n ω - θ) / S n ω))
    (hT : ConvergesInDistribution P ν (fun n ω => (E n ω - θ) / S n ω) id)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => (P.prod (Measure.pi (fun _ : Fin (B n) => Q n))).real
      {z | θ ∈ Icc
        (E n z.1 - distributionQuantile (empiricalLaw (fun j => F n (z.1, z.2 j))) b * S n z.1)
        (E n z.1 - distributionQuantile (empiricalLaw (fun j => F n (z.1, z.2 j))) a * S n z.1)})
      atTop (𝓝 (b - a)) := by
  let R n := P.prod (Measure.pi (fun _ : Fin (B n) => Q n))
  let A n (z : Ω × (Fin (B n) → Γ n)) :=
    distributionQuantile (empiricalLaw (fun j => F n (z.1, z.2 j))) a
  let C n (z : Ω × (Fin (B n) → Γ n)) :=
    distributionQuantile (empiricalLaw (fun j => F n (z.1, z.2 j))) b
  have hA := conditional_monteCarlo_quantile_probability P Q hB F hF ν hstrict hconv ha
  have hC := conditional_monteCarlo_quantile_probability P Q hB F hF ν hstrict hconv hb
  have hCDF t : Tendsto (fun n => (R n).real {z | (E n z.1 - θ) / S n z.1 ≤ t})
      atTop (𝓝 (cdf ν t)) := by
    have hc := asymptotic_rejection_probability hT (Iic t) measurableSet_Iic
      (by simp)
    have he n : (R n).real {z | (E n z.1 - θ) / S n z.1 ≤ t} =
        P.real {ω | (E n ω - θ) / S n ω ≤ t} := by
      have hs : {z : Ω × (Fin (B n) → Γ n) | (E n z.1 - θ) / S n z.1 ≤ t} =
          {ω | (E n ω - θ) / S n ω ≤ t} ×ˢ univ := by ext z; simp
      rw [hs, measureReal_prod_prod, probReal_univ, mul_one]
    simp_rw [he]
    simpa only [id_eq, mem_Iic, cdf_eq_real] using! hc
  have hh := row_random_interval_coverage R ν (fun n z => E n z.1) (fun n z => S n z.1)
    A C (fun n z => hS n z.1) hCDF hA hC
    (fun n => (hmT n).comp measurable_fst)
    (fun n => measurable_simulated_quantile (hF n) ha)
    (fun n z => distributionQuantile_mono _ ha hb hab)
  simpa only [cdf_eq_real, distributionQuantile_exact ν a ha,
    distributionQuantile_exact ν b hb, R, A, C] using! hh

/-- Joint law for the observed data and B(n) independent whole-sample bootstrap
index draws, each resampling n+1 observations. -/
def bootstrapMonteCarloJointLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℕ → ℕ) (n : ℕ) :
    Measure (Ω × (Fin (B n) → (Fin (n + 1) → Fin (n + 1)))) :=
  P.prod (Measure.pi (fun _ : Fin (B n) => bootstrapIndexLaw (n + 1)))

instance bootstrapMonteCarloJointLaw_isProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℕ → ℕ) (n : ℕ) :
    IsProbabilityMeasure (bootstrapMonteCarloJointLaw P B n) := by
  unfold bootstrapMonteCarloJointLaw bootstrapIndexLaw
  infer_instance

/-- The actual Monte Carlo array of unscaled bootstrap errors. -/
def bootstrapMonteCarloErrors {Ω : Type*} (X : ℕ → Ω → ℝ)
    (T : ∀ n, (Fin (n + 1) → ℝ) → ℝ) (B : ℕ → ℕ) (n : ℕ)
    (z : Ω × (Fin (B n) → (Fin (n + 1) → Fin (n + 1)))) : Fin (B n) → ℝ :=
  fun j => T n (bootstrapSample (fun i : Fin (n + 1) => X i z.1) (z.2 j)) -
    T n (fun i : Fin (n + 1) => X i z.1)

/-- A valid normalized bootstrap approximation gives a valid actual Monte Carlo
basic interval as B(n) grows. The population scale cancels from its endpoints. -/
theorem monteCarlo_basic_bootstrap_interval_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (T : ∀ n, (Fin (n + 1) → ℝ) → ℝ)
    (hTm : ∀ n, Measurable (T n)) (θ τ : ℝ) (hτ : 0 < τ)
    {B : ℕ → ℕ} [∀ n, NeZero (B n)] (hB : Tendsto B atTop atTop)
    (hT : ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => Real.sqrt ((n : ℝ) + 1) / τ * (T n (fun i => X i ω) - θ)) id)
    (hconv : ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n => cdf
      ((bootstrapLaw (fun i : Fin (n + 1) => X i ω)).map
        (fun b => Real.sqrt ((n : ℝ) + 1) / τ * (T n b - T n (fun i => X i ω)))) t)
      atTop (𝓝 (cdf (gaussianReal 0 1) t)))
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => (bootstrapMonteCarloJointLaw P B n).real {z | θ ∈ Icc
      (T n (fun i => X i z.1) - distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X T B n z)) b)
      (T n (fun i => X i z.1) - distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X T B n z)) a)})
      atTop (𝓝 (b - a)) := by
  have hQ n : IsProbabilityMeasure (bootstrapIndexLaw (n + 1)) := by unfold bootstrapIndexLaw; infer_instance
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  let E n (ω : Ω) := T n (fun i => X i ω)
  let S (n : ℕ) (_ω : Ω) := τ / Real.sqrt ((n : ℝ) + 1)
  let F n (z : Ω × (Fin (n + 1) → Fin (n + 1))) := Real.sqrt ((n : ℝ) + 1) / τ *
    (T n (bootstrapSample (fun i => X i z.1) z.2) - E n z.1)
  have hd n : Measurable (fun ω : Ω => fun i : Fin (n + 1) => X i ω) :=
    measurable_pi_lambda _ (fun i => hX i)
  have hEm n : Measurable (E n) := (hTm n).comp (hd n)
  have hFm n : Measurable (F n) := by
    have hb := measurable_bootstrapSample_pair.comp (((hd n).comp measurable_fst).prodMk measurable_snd)
    exact measurable_const.mul (((hTm n).comp hb).sub ((hEm n).comp measurable_fst))
  have hc : ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n => cdf
      ((bootstrapIndexLaw (n + 1)).map (fun γ => F n (ω, γ))) t)
      atTop (𝓝 (cdf (gaussianReal 0 1) t)) := by
    filter_upwards [hconv] with ω hω
    intro t
    apply (hω t).congr
    intro n
    congr 1
    have hl := bootstrapSample_hasLaw (fun i : Fin (n + 1) => X i ω)
    have hf : Measurable (fun b : Fin (n + 1) → ℝ =>
        Real.sqrt ((n : ℝ) + 1) / τ * (T n b - E n ω)) :=
      measurable_const.mul ((hTm n).sub measurable_const)
    have hh := (HasLaw.mk hf.aemeasurable rfl).comp hl
    simpa only [Function.comp_def, F, E] using! congrArg cdf hh.map_eq.symm
  have hstd : ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => (E n ω - θ) / S n ω) id := by
    convert! hT using 1
    funext n ω
    dsimp only [E, S]
    rw [div_div_eq_mul_div]
    ring
  have hh := monteCarlo_interval_coverage P (fun n => bootstrapIndexLaw (n + 1)) hB F hFm
    (gaussianReal 0 1) (gaussian_cdf_strictMono 0 1 (by norm_num)) hc E S θ
    (fun n ω => div_pos hτ (Real.sqrt_pos.mpr (by positivity)))
    (fun n => (hEm n).sub_const θ |>.div_const _)
    hstd ha hb hab
  have hq n z q (hq : q ∈ Ioo (0 : ℝ) 1) :
      distributionQuantile (empiricalLaw (fun j : Fin (B n) => F n (z.1, z.2 j))) q * S n z.1 =
      distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X T B n z)) q := by
    have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have he := empirical_quantile_positive_scale (bootstrapMonteCarloErrors X T B n z)
      (Real.sqrt ((n : ℝ) + 1) / τ) (div_pos hs hτ) hq
    change _ * (τ / Real.sqrt ((n : ℝ) + 1)) = _
    rw [show (fun j => F n (z.1, z.2 j)) =
      (fun j => (Real.sqrt ((n : ℝ) + 1) / τ) * bootstrapMonteCarloErrors X T B n z j) from rfl, he]
    field_simp
  simpa only [hq _ _ _ ha, hq _ _ _ hb, E, bootstrapMonteCarloJointLaw] using! hh

end LectureNotes
