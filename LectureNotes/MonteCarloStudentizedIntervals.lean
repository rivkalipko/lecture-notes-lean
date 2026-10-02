import LectureNotes.MonteCarloBootstrapIntervals
import LectureNotes.BootstrapStudentizedIntervals

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- Events agreeing outside a vanishing-probability exceptional set have the
same limiting probability, also for different probability spaces in each row. -/
theorem row_probability_limit_of_agree_off_rare_event
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (A B R : ∀ n, Set (Ω n)) {l : ℝ}
    (hB : Tendsto (fun n => (P n).real (B n)) atTop (𝓝 l))
    (hR : Tendsto (fun n => (P n).real (R n)) atTop (𝓝 0))
    (he : ∀ n ω, ω ∉ R n → (ω ∈ A n ↔ ω ∈ B n)) :
    Tendsto (fun n => (P n).real (A n)) atTop (𝓝 l) := by
  have hb n : (P n).real (B n) - (P n).real (R n) ≤ (P n).real (A n) ∧
      (P n).real (A n) ≤ (P n).real (B n) + (P n).real (R n) := by
    have hAB : A n ⊆ B n ∪ R n := by
      intro ω hω
      by_cases hR : ω ∈ R n
      · exact Or.inr hR
      · exact Or.inl ((he n ω hR).mp hω)
    have hBA : B n ⊆ A n ∪ R n := by
      intro ω hω
      by_cases hR : ω ∈ R n
      · exact Or.inr hR
      · exact Or.inl ((he n ω hR).mpr hω)
    have h₁ := (measureReal_mono (μ := P n) hAB).trans (measureReal_union_le _ _)
    have h₂ := (measureReal_mono (μ := P n) hBA).trans (measureReal_union_le _ _)
    exact ⟨by linarith, h₁⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [sub_zero] using hB.sub hR)
    (by simpa only [add_zero] using hB.add hR) (fun n => (hb n).1) (fun n => (hb n).2)

/-- Actual Monte Carlo quantiles yield interval coverage even when estimated
scales are nonpositive on rare events. No independence of pivot and quantiles
is needed; data and the independent simulation seeds have their product law. -/
theorem monteCarlo_interval_coverage_of_rare_nonpositive_scale {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Γ : ℕ → Type*}
    [∀ n, MeasurableSpace (Γ n)] (Q : ∀ n, Measure (Γ n))
    [∀ n, IsProbabilityMeasure (Q n)] {B : ℕ → ℕ} [∀ n, NeZero (B n)]
    (hB : Tendsto B atTop atTop) (F : ∀ n, Ω × Γ n → ℝ)
    (hF : ∀ n, Measurable (F n)) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (hstrict : StrictMono (cdf ν))
    (hconv : ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n => cdf ((Q n).map (fun γ => F n (ω, γ))) t)
      atTop (𝓝 (cdf ν t)))
    (E S : ℕ → Ω → ℝ) (θ : ℝ)
    (hbad : Tendsto (fun n => P.real {ω | S n ω ≤ 0}) atTop (𝓝 0))
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
  have hh := row_random_interval_probability R ν (fun n z => (E n z.1 - θ) / S n z.1)
    A C hCDF hA hC (fun n => (hmT n).comp measurable_fst)
    (fun n => measurable_simulated_quantile (hF n) ha)
    (fun n z => distributionQuantile_mono _ ha hb hab)
  have hmass : Tendsto (fun n => (R n).real
      {z | (E n z.1 - θ) / S n z.1 ∈ Icc (A n z) (C n z)}) atTop (𝓝 (b - a)) := by
    simpa only [cdf_eq_real, distributionQuantile_exact ν a ha,
      distributionQuantile_exact ν b hb] using! hh
  have hbad' : Tendsto (fun n => (R n).real {z | S n z.1 ≤ 0}) atTop (𝓝 0) := by
    have he n : (R n).real {z | S n z.1 ≤ 0} = P.real {ω | S n ω ≤ 0} := by
      have hs : {z : Ω × (Fin (B n) → Γ n) | S n z.1 ≤ 0} =
          {ω | S n ω ≤ 0} ×ˢ univ := by ext z; simp
      rw [hs, measureReal_prod_prod, probReal_univ, mul_one]
    simpa only [he] using hbad
  apply row_probability_limit_of_agree_off_rare_event R _ _ _ hmass hbad'
  intro n z hz
  exact (location_pivot_inversion _ _ _ _ _ (lt_of_not_ge hz)).symm


/-- The B(n) actual bootstrap-t errors, each computed with its own resample
standard deviation. The statistic is totalized on zero-variance resamples. -/
def bootstrapMonteCarloStudentizedErrors {Ω : Type*} (X : ℕ → Ω → ℝ)
    (B : ℕ → ℕ) (n : ℕ)
    (z : Ω × (Fin (B n) → (Fin (n + 1) → Fin (n + 1)))) : Fin (B n) → ℝ :=
  fun j => Real.sqrt ((n : ℝ) + 1) *
    (sampleMean (bootstrapSample (fun i : Fin (n + 1) => X i z.1) (z.2 j)) -
      sampleMean (fun i : Fin (n + 1) => X i z.1)) /
    Real.sqrt (empiricalVariance (bootstrapSample (fun i : Fin (n + 1) => X i z.1) (z.2 j)))

/-- The simulated studentized error array is jointly measurable in data and
all whole-sample resampling indices. -/
theorem measurable_bootstrapMonteCarloStudentizedErrors
    {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (B : ℕ → ℕ) (n : ℕ) :
    Measurable (bootstrapMonteCarloStudentizedErrors X B n) := by
  apply measurable_pi_lambda
  intro j
  have hd : Measurable (fun z : Ω × (Fin (B n) → (Fin (n + 1) → Fin (n + 1))) =>
      fun i : Fin (n + 1) => X i z.1) :=
    measurable_pi_lambda _ (fun i => (hX i).comp measurable_fst)
  have hz : Measurable (fun z : Ω × (Fin (B n) → (Fin (n + 1) → Fin (n + 1))) => z.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  have hs := measurable_bootstrapSample_pair.comp (hd.prodMk hz)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one,
    bootstrapMonteCarloStudentizedErrors] using!
    (measurable_bootstrapStudentizedMean_statistic (n := n + 1)).comp (hd.prodMk hs)

/-- L11's simulated bootstrap-t interval for an IID mean: the actual joint law
of observations and B(n) independent whole-sample index resamples gives nominal
coverage as both sample size and B(n) grow. A finite fourth moment and positive
population variance suffice. Zero observed or resampled variances are allowed. -/
theorem iid_monteCarlo_studentized_bootstrap_mean_interval_coverage
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[X 0; P]) {B : ℕ → ℕ} [∀ n, NeZero (B n)]
    (hB : Tendsto B atTop atTop) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => (bootstrapMonteCarloJointLaw P B n).real {z | P[X 0] ∈ Icc
      (sampleMean (fun i : Fin (n + 1) => X i z.1) -
        distributionQuantile (empiricalLaw (bootstrapMonteCarloStudentizedErrors X B n z)) b *
          (Real.sqrt (empiricalVariance (fun i : Fin (n + 1) => X i z.1)) /
            Real.sqrt ((n : ℝ) + 1)))
      (sampleMean (fun i : Fin (n + 1) => X i z.1) -
        distributionQuantile (empiricalLaw (bootstrapMonteCarloStudentizedErrors X B n z)) a *
          (Real.sqrt (empiricalVariance (fun i : Fin (n + 1) => X i z.1)) /
            Real.sqrt ((n : ℝ) + 1)))}) atTop (𝓝 (b - a)) := by
  have hQ n : IsProbabilityMeasure (bootstrapIndexLaw (n + 1)) := by
    unfold bootstrapIndexLaw
    infer_instance
  let σ := Real.sqrt (Var[X 0; P])
  have hσ : 0 < σ := Real.sqrt_pos.mpr hv
  have hvar : Var[X 0; P] = σ ^ 2 := (Real.sq_sqrt hv.le).symm
  have h₂ : MemLp (X 0) 2 P := hX.mono_exponent (by norm_num)
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  let E (n : ℕ) (ω : Ω) := sampleMean (fun i : Fin (n + 1) => X i ω)
  let V (n : ℕ) (ω : Ω) := empiricalVariance (fun i : Fin (n + 1) => X i ω)
  let S (n : ℕ) (ω : Ω) := Real.sqrt (V n ω) / Real.sqrt ((n : ℝ) + 1)
  let D (n : ℕ) (ω : Ω) := Real.sqrt (V n ω) / σ
  let F (n : ℕ) (z : Ω × (Fin (n + 1) → Fin (n + 1))) :=
    Real.sqrt ((n : ℝ) + 1) *
      (sampleMean (bootstrapSample (fun i : Fin (n + 1) => X i z.1) z.2) - E n z.1) /
      Real.sqrt (empiricalVariance (bootstrapSample (fun i : Fin (n + 1) => X i z.1) z.2))
  have hFm n : Measurable (F n) := by
    have hd : Measurable (fun z : Ω × (Fin (n + 1) → Fin (n + 1)) =>
        fun i : Fin (n + 1) => X i z.1) :=
      measurable_pi_lambda _ (fun i => (hXm i).comp measurable_fst)
    have hs := measurable_bootstrapSample_pair.comp (hd.prodMk measurable_snd)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, F, E] using!
      (measurable_bootstrapStudentizedMean_statistic (n := n + 1)).comp (hd.prodMk hs)
  have hconv : ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n =>
      cdf ((bootstrapIndexLaw (n + 1)).map (fun γ => F n (ω, γ))) t)
      atTop (𝓝 (cdf (gaussianReal 0 1) t)) := by
    filter_upwards [iid_bootstrap_studentized_mean_cdf hXm hX hind hident hv] with ω hω
    intro t
    simpa only [bootstrapStudentizedMeanLaw_index_map, Nat.cast_add, Nat.cast_one, F, E] using! hω t
  have hD : ConvergesInProbability P D (fun _ => 1) :=
    iid_sample_std_factor_consistent hXm h₂ hind hident σ hσ hvar
  have hDm n : Measurable (D n) := by
    dsimp only [D, V]
    unfold empiricalVariance sampleMean
    fun_prop
  have hT : ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => (E n ω - P[X 0]) / S n ω) id := by
    have ht := slutsky_div (by norm_num : (1 : ℝ) ≠ 0)
      (iid_sampleMean_standardized_clt h₂ hind hident σ hσ hvar) hD
      (fun n => (hDm n).aemeasurable)
    apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => div_one _)) ht
    intro n
    apply ae_of_all
    intro ω
    dsimp only [E, S, D, V]
    rw [div_mul_eq_mul_div, div_div_div_cancel_right₀ hσ.ne', div_div_eq_mul_div]
    ring
  have hbad : Tendsto (fun n => P.real {ω | S n ω ≤ 0}) atTop (𝓝 0) := by
    have hh := tendstoInMeasure_iff_measureReal_norm.mp hD 1 (by norm_num)
    apply squeeze_zero (fun _ => measureReal_nonneg) _ hh
    intro n
    refine measureReal_mono ?_ (measure_ne_top P _)
    intro ω hω
    have hn : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hle : Real.sqrt (V n ω) / Real.sqrt ((n : ℝ) + 1) ≤ 0 := hω
    have hz : Real.sqrt (V n ω) = 0 :=
      le_antisymm (by simpa only [zero_mul] using (div_le_iff₀ hn).mp hle) (Real.sqrt_nonneg _)
    change 1 ≤ ‖Real.sqrt (V n ω) / σ - 1‖
    rw [hz]
    norm_num
  have hh := monteCarlo_interval_coverage_of_rare_nonpositive_scale P
    (fun n => bootstrapIndexLaw (n + 1)) hB F hFm (gaussianReal 0 1)
    (gaussian_cdf_strictMono 0 1 (by norm_num)) hconv E S (P[X 0]) hbad
    (fun n => by dsimp only [E, S, V]; unfold empiricalVariance sampleMean; fun_prop)
    hT ha hb hab
  simpa only [bootstrapMonteCarloJointLaw, bootstrapMonteCarloStudentizedErrors, E, S, V, F]
    using! hh

/-- The denominator-N and denominator-(N−1) variance conventions give exactly
the same simulated bootstrap-t endpoint. The reciprocal factors in each
studentized resample and the observed standard error cancel, even when an
observed sample or a resample has zero variance. -/
theorem bootstrap_studentized_endpoint_variance_convention
    {n m : ℕ} [NeZero n] [NeZero m] (hn : 1 < n)
    (x : Fin n → ℝ) (y : Fin m → (Fin n → ℝ))
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    distributionQuantile (empiricalLaw (fun j =>
      Real.sqrt n * (sampleMean (y j) - sampleMean x) /
        Real.sqrt (sampleVariance (y j)))) q *
          (Real.sqrt (sampleVariance x) / Real.sqrt n) =
    distributionQuantile (empiricalLaw (fun j =>
      Real.sqrt n * (sampleMean (y j) - sampleMean x) /
        Real.sqrt (empiricalVariance (y j)))) q *
          (Real.sqrt (empiricalVariance x) / Real.sqrt n) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  let c := Real.sqrt ((n : ℝ) / (n - 1))
  have hc : 0 < c := Real.sqrt_pos.mpr (div_pos (by linarith) (by linarith))
  have hs (z : Fin n → ℝ) : Real.sqrt (sampleVariance z) =
      c * Real.sqrt (empiricalVariance z) := by
    rw [sampleVariance_eq_scaled_empiricalVariance hn, Real.sqrt_mul (by positivity)]
  let e j := Real.sqrt n * (sampleMean (y j) - sampleMean x) /
    Real.sqrt (empiricalVariance (y j))
  have he : (fun j => Real.sqrt n * (sampleMean (y j) - sampleMean x) /
      Real.sqrt (sampleVariance (y j))) = (fun j => c⁻¹ * e j) := by
    funext j
    rw [hs]
    dsimp only [e]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, empirical_quantile_positive_scale e c⁻¹ (inv_pos.mpr hc) hq, hs]
  change c⁻¹ * distributionQuantile (empiricalLaw e) q *
    (c * Real.sqrt (empiricalVariance x) / Real.sqrt n) = _
  field_simp
  dsimp only [e]
  ring

/-- The actual simulated bootstrap-t statistics with the source's
unbiased, denominator-(N−1) sample variance in every resample. -/
def bootstrapMonteCarloSampleVarianceStudentizedErrors {Ω : Type*}
    (X : ℕ → Ω → ℝ) (B : ℕ → ℕ) (n : ℕ)
    (z : Ω × (Fin (B n) → (Fin (n + 1) → Fin (n + 1)))) : Fin (B n) → ℝ :=
  fun j => Real.sqrt ((n : ℝ) + 1) *
    (sampleMean (bootstrapSample (fun i : Fin (n + 1) => X i z.1) (z.2 j)) -
      sampleMean (fun i : Fin (n + 1) => X i z.1)) /
    Real.sqrt (sampleVariance (bootstrapSample (fun i : Fin (n + 1) => X i z.1) (z.2 j)))

/-- L11's simulated bootstrap-t confidence interval, using denominator-(N−1)
standard errors for both data and resamples, has its nominal limiting coverage.
This is the actual joint data/index experiment, with any B(n) tending to infinity. -/
theorem iid_monteCarlo_bootstrap_t_interval_coverage
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[X 0; P]) {B : ℕ → ℕ} [∀ n, NeZero (B n)]
    (hB : Tendsto B atTop atTop) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => (bootstrapMonteCarloJointLaw P B n).real {z | P[X 0] ∈ Icc
      (sampleMean (fun i : Fin (n + 1) => X i z.1) -
        distributionQuantile (empiricalLaw
          (bootstrapMonteCarloSampleVarianceStudentizedErrors X B n z)) b *
          (Real.sqrt (sampleVariance (fun i : Fin (n + 1) => X i z.1)) /
            Real.sqrt ((n : ℝ) + 1)))
      (sampleMean (fun i : Fin (n + 1) => X i z.1) -
        distributionQuantile (empiricalLaw
          (bootstrapMonteCarloSampleVarianceStudentizedErrors X B n z)) a *
          (Real.sqrt (sampleVariance (fun i : Fin (n + 1) => X i z.1)) /
            Real.sqrt ((n : ℝ) + 1)))}) atTop (𝓝 (b - a)) := by
  apply (iid_monteCarlo_studentized_bootstrap_mean_interval_coverage
    hXm hX hind hident hv hB ha hb hab).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  congr 1
  ext z
  have he q (hq : q ∈ Ioo (0 : ℝ) 1) :=
    bootstrap_studentized_endpoint_variance_convention (by omega : 1 < n + 1)
      (fun i : Fin (n + 1) => X i z.1)
      (fun j : Fin (B n) => bootstrapSample (fun i : Fin (n + 1) => X i z.1) (z.2 j)) hq
  have hea := he a ha
  have heb := he b hb
  simp only [Nat.cast_add, Nat.cast_one] at hea heb
  exact (Iff.of_eq (congrArg₂
    (fun (u v : ℝ) => P[X 0] ∈ Icc
      (sampleMean (fun i : Fin (n + 1) => X i z.1) - u)
      (sampleMean (fun i : Fin (n + 1) => X i z.1) - v)) heb hea)).symm

end LectureNotes
