import LectureNotes.MonteCarloBootstrapIntervals

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- The whole Monte Carlo error array is jointly measurable in the data and
all resampling indices. -/
theorem measurable_bootstrapMonteCarloErrors {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (T : ∀ n, (Fin (n + 1) → ℝ) → ℝ) (hT : ∀ n, Measurable (T n))
    (B : ℕ → ℕ) (n : ℕ) : Measurable (bootstrapMonteCarloErrors X T B n) := by
  have hd : Measurable (fun ω : Ω => fun i : Fin (n + 1) => X i ω) :=
    measurable_pi_lambda _ (fun i => hX i)
  unfold bootstrapMonteCarloErrors
  apply measurable_pi_lambda
  intro j
  have hd' : Measurable (fun z : Ω × (Fin (B n) → (Fin (n + 1) → Fin (n + 1))) =>
      fun i : Fin (n + 1) => X i z.1) := measurable_pi_lambda _ (fun i => (hX i).comp measurable_fst)
  have hz : Measurable (fun z : Ω × (Fin (B n) → (Fin (n + 1) → Fin (n + 1))) => z.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  have hb := measurable_bootstrapSample_pair.comp (hd'.prodMk hz)
  simpa only [Function.comp_def] using! ((hT n).comp hb).sub ((hT n).comp hd')

/-- A two-sided Monte Carlo bootstrap test has its nominal size when both the
sampling and conditional bootstrap limits are valid and B(n) tends to infinity. -/
theorem monteCarlo_basic_bootstrap_test_size {Ω : Type*} [MeasurableSpace Ω]
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
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => (bootstrapMonteCarloJointLaw P B n).real {z |
      T n (fun i => X i z.1) - θ ∉ Icc
        (distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X T B n z)) (α / 2))
        (distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X T B n z)) (1 - α / 2))})
      atTop (𝓝 α) := by
  have ha : α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hb : 1 - α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hab : α / 2 ≤ 1 - α / 2 := by linarith [hα.2]
  let E n (z : Ω × (Fin (B n) → (Fin (n + 1) → Fin (n + 1)))) := T n (fun i => X i z.1)
  let A n (z : Ω × (Fin (B n) → (Fin (n + 1) → Fin (n + 1)))) :=
    distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X T B n z)) (α / 2)
  let C n (z : Ω × (Fin (B n) → (Fin (n + 1) → Fin (n + 1)))) :=
    distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X T B n z)) (1 - α / 2)
  have hEm n : Measurable (E n) := by
    apply (hTm n).comp
    exact measurable_pi_lambda _ (fun i => (hX i).comp measurable_fst)
  have hAm n : Measurable (A n) :=
    (measurable_empirical_quantile ha).comp (measurable_bootstrapMonteCarloErrors X hX T hTm B n)
  have hCm n : Measurable (C n) :=
    (measurable_empirical_quantile hb).comp (measurable_bootstrapMonteCarloErrors X hX T hTm B n)
  have hm n : MeasurableSet {z | θ ∈ Icc (E n z - C n z) (E n z - A n z)} :=
    (measurableSet_le ((hEm n).sub (hCm n)) measurable_const).inter
      (measurableSet_le measurable_const ((hEm n).sub (hAm n)))
  have hc := monteCarlo_basic_bootstrap_interval_coverage X hX T hTm θ τ hτ hB hT hconv ha hb hab
  have he n : {z | E n z - θ ∉ Icc (A n z) (C n z)} =
      {z | θ ∈ Icc (E n z - C n z) (E n z - A n z)}ᶜ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_Icc]
    apply not_congr
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub hc
  convert! hh using 1
  · funext n
    change (bootstrapMonteCarloJointLaw P B n).real {z | E n z - θ ∉ Icc (A n z) (C n z)} = _
    rw [he, measureReal_compl (hm n), probReal_univ]
  · ring

/-- Actual IID mean bootstrap intervals, using B(n) independent index resamples
and their empirical quantiles. Only finite second moment is required. -/
theorem iid_monteCarlo_bootstrap_mean_interval_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[X 0; P]) {B : ℕ → ℕ} [∀ n, NeZero (B n)]
    (hB : Tendsto B atTop atTop) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => (bootstrapMonteCarloJointLaw P B n).real {z | P[X 0] ∈ Icc
      (sampleMean (fun i : Fin (n + 1) => X i z.1) -
        distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X (fun _ => sampleMean) B n z)) b)
      (sampleMean (fun i : Fin (n + 1) => X i z.1) -
        distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X (fun _ => sampleMean) B n z)) a)})
      atTop (𝓝 (b - a)) := by
  let τ := Real.sqrt (Var[X 0; P])
  have hτ : 0 < τ := Real.sqrt_pos.mpr hv
  have hvar : Var[X 0; P] = τ ^ 2 := (Real.sq_sqrt hv.le).symm
  apply monteCarlo_basic_bootstrap_interval_coverage X hXm (fun _ => sampleMean)
    (fun _ => by unfold sampleMean; fun_prop) (P[X 0]) τ hτ hB
    (iid_sampleMean_standardized_clt hX hind hident τ hτ hvar) _ ha hb hab
  simpa only [bootstrapMeanErrorLaw, Nat.cast_add, Nat.cast_one] using!
    iid_bootstrap_mean_cdf hXm hX hind hident τ hτ hvar

/-- Actual IID sample-variance bootstrap intervals with finite fourth moment.
No positive variance of X itself is needed beyond the positive influence variance. -/
theorem iid_monteCarlo_bootstrap_variance_interval_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P])
    {B : ℕ → ℕ} [∀ n, NeZero (B n)] (hB : Tendsto B atTop atTop) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => (bootstrapMonteCarloJointLaw P B n).real {z | Var[X 0; P] ∈ Icc
      (sampleVariance (fun i : Fin (n + 1) => X i z.1) -
        distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X (fun _ => sampleVariance) B n z)) b)
      (sampleVariance (fun i : Fin (n + 1) => X i z.1) -
        distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X (fun _ => sampleVariance) B n z)) a)})
      atTop (𝓝 (b - a)) := by
  let τ := Real.sqrt (Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P])
  have hτ : 0 < τ := Real.sqrt_pos.mpr hv
  have hvar : Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P] = τ ^ 2 := (Real.sq_sqrt hv.le).symm
  apply monteCarlo_basic_bootstrap_interval_coverage X hXm (fun _ => sampleVariance)
    (fun _ => by unfold sampleVariance sampleMean; fun_prop) (Var[X 0; P]) τ hτ hB
    (iid_sampleVariance_standardized_clt hXm hX hind hident τ hτ hvar) _ ha hb hab
  simpa only [bootstrapSampleVarianceErrorLaw, Nat.cast_add, Nat.cast_one] using!
    iid_bootstrap_sampleVariance_cdf hXm hX hind hident τ hτ hvar

/-- L8's actual simulated bootstrap interval for a smooth function of mean and
sample variance. Both sampling and conditional limits are derived from IID
finite-fourth-moment data and an actual strict derivative. -/
theorem iid_monteCarlo_bootstrap_smooth_moment_interval_coverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (h : C(ℝ × ℝ, ℝ)) (D : (ℝ × ℝ) →L[ℝ] ℝ)
    (hd : HasStrictFDerivAt h D (P[X 0], Var[X 0; P]))
    (hv : 0 < Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P])
    {B : ℕ → ℕ} [∀ n, NeZero (B n)] (hB : Tendsto B atTop atTop) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => (bootstrapMonteCarloJointLaw P B n).real {z |
      h (P[X 0], Var[X 0; P]) ∈ Icc
        (smoothMomentStatistic h (fun i : Fin (n + 1) => X i z.1) -
          distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X (fun _ => smoothMomentStatistic h) B n z)) b)
        (smoothMomentStatistic h (fun i : Fin (n + 1) => X i z.1) -
          distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X (fun _ => smoothMomentStatistic h) B n z)) a)})
      atTop (𝓝 (b - a)) := by
  let τ := Real.sqrt (Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P])
  have hτ : 0 < τ := Real.sqrt_pos.mpr hv
  have hvar : Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P] = τ ^ 2 :=
    (Real.sq_sqrt hv.le).symm
  apply monteCarlo_basic_bootstrap_interval_coverage X hXm (fun _ => smoothMomentStatistic h)
    (fun _ => measurable_smoothMomentStatistic h) (h (P[X 0], Var[X 0; P])) τ hτ hB
    (iid_mean_variance_function_standardized_clt hXm hX hind hident h.continuous D hd.hasFDerivAt τ hτ hvar)
    _ ha hb hab
  simpa only [bootstrapSmoothMomentErrorLaw, Nat.cast_add, Nat.cast_one] using!
    iid_bootstrap_smooth_moment_cdf hXm hX hind hident h D hd τ hτ hvar

/-- L8's actual Monte Carlo bootstrap variance test under its variance null. -/
theorem iid_monteCarlo_bootstrap_variance_test_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hv : 0 < Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P])
    (v₀ : ℝ) (hnull : Var[X 0; P] = v₀)
    {B : ℕ → ℕ} [∀ n, NeZero (B n)] (hB : Tendsto B atTop atTop)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => (bootstrapMonteCarloJointLaw P B n).real {z |
      sampleVariance (fun i : Fin (n + 1) => X i z.1) - v₀ ∉ Icc
        (distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X (fun _ => sampleVariance) B n z)) (α / 2))
        (distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X (fun _ => sampleVariance) B n z)) (1 - α / 2))})
      atTop (𝓝 α) := by
  let τ := Real.sqrt (Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P])
  have hτ : 0 < τ := Real.sqrt_pos.mpr hv
  have hvar : Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P] = τ ^ 2 := (Real.sq_sqrt hv.le).symm
  have hT := iid_sampleVariance_standardized_clt hXm hX hind hident τ hτ hvar
  rw [hnull] at hT
  apply monteCarlo_basic_bootstrap_test_size X hXm (fun _ => sampleVariance)
    (fun _ => by unfold sampleVariance sampleMean; fun_prop) v₀ τ hτ hB hT _ hα
  simpa only [bootstrapSampleVarianceErrorLaw, Nat.cast_add, Nat.cast_one] using!
    iid_bootstrap_sampleVariance_cdf hXm hX hind hident τ hτ hvar

/-- The simulated smooth-moment bootstrap test has asymptotic size α under
its null, for any divergent number of Monte Carlo draws B(n). -/
theorem iid_monteCarlo_bootstrap_smooth_moment_test_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (h : C(ℝ × ℝ, ℝ)) (D : (ℝ × ℝ) →L[ℝ] ℝ)
    (hd : HasStrictFDerivAt h D (P[X 0], Var[X 0; P]))
    (hv : 0 < Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P])
    (γ₀ : ℝ) (hnull : h (P[X 0], Var[X 0; P]) = γ₀)
    {B : ℕ → ℕ} [∀ n, NeZero (B n)] (hB : Tendsto B atTop atTop)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => (bootstrapMonteCarloJointLaw P B n).real {z |
      smoothMomentStatistic h (fun i : Fin (n + 1) => X i z.1) - γ₀ ∉ Icc
        (distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X (fun _ => smoothMomentStatistic h) B n z)) (α / 2))
        (distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X (fun _ => smoothMomentStatistic h) B n z)) (1 - α / 2))})
      atTop (𝓝 α) := by
  let τ := Real.sqrt (Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P])
  have hτ : 0 < τ := Real.sqrt_pos.mpr hv
  have hvar : Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P] = τ ^ 2 :=
    (Real.sq_sqrt hv.le).symm
  have hT := iid_mean_variance_function_standardized_clt hXm hX hind hident
    h.continuous D hd.hasFDerivAt τ hτ hvar
  rw [hnull] at hT
  apply monteCarlo_basic_bootstrap_test_size X hXm (fun _ => smoothMomentStatistic h)
    (fun _ => measurable_smoothMomentStatistic h) γ₀ τ hτ hB hT _ hα
  simpa only [bootstrapSmoothMomentErrorLaw, Nat.cast_add, Nat.cast_one] using!
    iid_bootstrap_smooth_moment_cdf hXm hX hind hident h D hd τ hτ hvar

/-- The lecture's C² smooth-function simulation test, with the needed positive
influence variance and B(n)→∞ supplied explicitly. -/
theorem iid_C2_monteCarlo_bootstrap_moment_test_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (h : C(ℝ × ℝ, ℝ)) (hh : ContDiff ℝ 2 h)
    (hv : 0 < Var[fun ω => (fderiv ℝ h (P[X 0], Var[X 0; P]))
      (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P])
    (γ₀ : ℝ) (hnull : h (P[X 0], Var[X 0; P]) = γ₀)
    {B : ℕ → ℕ} [∀ n, NeZero (B n)] (hB : Tendsto B atTop atTop)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => (bootstrapMonteCarloJointLaw P B n).real {z |
      smoothMomentStatistic h (fun i : Fin (n + 1) => X i z.1) - γ₀ ∉ Icc
        (distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X (fun _ => smoothMomentStatistic h) B n z)) (α / 2))
        (distributionQuantile (empiricalLaw (bootstrapMonteCarloErrors X (fun _ => smoothMomentStatistic h) B n z)) (1 - α / 2))})
      atTop (𝓝 α) :=
  iid_monteCarlo_bootstrap_smooth_moment_test_size hXm hX hind hident h
    (fderiv ℝ h (P[X 0], Var[X 0; P])) (hh.hasStrictFDerivAt (by norm_num)) hv γ₀ hnull hB hα

end LectureNotes
