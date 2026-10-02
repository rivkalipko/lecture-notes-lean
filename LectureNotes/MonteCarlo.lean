import LectureNotes.EmpiricalQuantiles
import LectureNotes.VarianceAsymptotics
import LectureNotes.QuantileMeasurability

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- Quantile convergence only needs a strict crossing on the right of the
chosen quantile. This condition permits atoms and bounded supports. -/
theorem distributionQuantile_tendsto_of_crossing (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hcross : ∀ x, distributionQuantile ν q < x → q < cdf ν x)
    (hconv : ∀ x, Tendsto (fun n => cdf (μ n) x) atTop (𝓝 (cdf ν x))) :
    Tendsto (fun n => distributionQuantile (μ n) q) atTop (𝓝 (distributionQuantile ν q)) := by
  apply tendsto_order.mpr
  constructor
  · intro x hx
    have hlt : cdf ν x < q := (lt_distributionQuantile_iff ν hq).mp hx
    filter_upwards [(hconv x).eventually (gt_mem_nhds hlt)] with n hn
    exact (lt_distributionQuantile_iff (μ n) hq).mpr hn
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := exists_between hx
    filter_upwards [(hconv y).eventually (lt_mem_nhds (hcross y hy))] with n hn
    exact ((distributionQuantile_le_iff (μ n) hq).mpr hn.le).trans_lt hyx

/-- The generalized-inverse quantile computed from a nonempty finite
simulation output is a measurable statistic, even with repeated outputs. -/
theorem measurable_empirical_quantile {n : ℕ} [NeZero n] {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun x : Fin n → ℝ => distributionQuantile (empiricalLaw x) q) := by
  apply measurable_distributionQuantile _ _ hq
  intro t
  simp_rw [empiricalLaw_cdf]
  exact measurable_empiricalCDF (fun (i : Fin n) (x : Fin n → ℝ) => x i) (fun i => measurable_pi_apply i) t

/-- Independent simulation replications give strongly consistent empirical
quantiles at every quantile satisfying the explicit crossing condition. The
finite-sample implementation is the ceiling-rank order statistic proved above. -/
theorem monteCarlo_quantile_strong_consistency {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hYm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hcross : ∀ x, distributionQuantile (P.map (Y 0)) q < x → q < cdf (P.map (Y 0)) x) :
    ConvergesAlmostSurely P
      (fun B ω => distributionQuantile (empiricalLaw (fun b : Fin (B + 1) => Y b ω)) q)
      (fun _ => distributionQuantile (P.map (Y 0)) q) := by
  have : IsProbabilityMeasure (P.map (Y 0)) := Measure.isProbabilityMeasure_map (hYm 0).aemeasurable
  filter_upwards [empiricalCDF_glivenko_cantelli_uniform hYm hind hident] with ω hω
  apply distributionQuantile_tendsto_of_crossing _ _ hq hcross
  intro t
  simp_rw [empiricalLaw_cdf]
  exact (hω.tendsto_at t).comp (tendsto_add_atTop_nat 1)

/-- A measurable statistic applied separately to independent simulated data
sets has the intended pushforward law in every replication. -/
theorem monteCarlo_statistics_iid {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {μ : Measure α} {X : ℕ → Ω → α}
    (g : α → ℝ) (hg : Measurable g) (hind : iIndepFun X P)
    (hlaw : ∀ b, HasLaw (X b) μ P) :
    iIndepFun (fun b ω => g (X b ω)) P ∧
      (∀ b, HasLaw (fun ω => g (X b ω)) (μ.map g) P) := by
  refine ⟨hind.comp (fun _ => g) (fun _ => hg), ?_⟩
  intro b
  exact (HasLaw.mk hg.aemeasurable rfl).comp (hlaw b)

/-- The Monte Carlo average consistently estimates the mean of the output
statistic when that mean is integrable. -/
theorem monteCarlo_mean_strong_consistency {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hY : Integrable (Y 0) P) (hind : iIndepFun Y P)
    (hident : ∀ b, IdentDistrib (Y b) (Y 0) P P) :
    ConvergesAlmostSurely P (fun B ω => sampleMean (fun b : Fin B => Y b ω))
      (fun _ => P[Y 0]) := by
  filter_upwards [strong_law_of_large_numbers hY (fun _ _ h => hind.indepFun h) hident] with ω hω
  convert! hω using 1
  funext B
  simp only [sampleMean, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun b => Y b ω) B]
  ring

/-- Simulation frequencies consistently estimate every fixed measurable
event probability. This includes the CDF algorithm with a lower half-line. -/
theorem monteCarlo_event_strong_consistency {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ℕ → Ω → α} (hYm : ∀ b, Measurable (Y b)) (hind : iIndepFun Y P)
    (hident : ∀ b, IdentDistrib (Y b) (Y 0) P P) (A : Set α) (hA : MeasurableSet A) :
    ConvergesAlmostSurely P
      (fun B ω => sampleMean (fun b : Fin B => A.indicator (fun _ => (1 : ℝ)) (Y b ω)))
      (fun _ => P.real (Y 0 ⁻¹' A)) := by
  classical
  let g : α → ℝ := A.indicator (fun _ => 1)
  have hg : Measurable g := measurable_const.indicator hA
  have hgi : Integrable (fun ω => g (Y 0 ω)) P := by
    have he : (fun ω => g (Y 0 ω)) = (Y 0 ⁻¹' A).indicator (fun _ => (1 : ℝ)) := by
      ext ω
      simp [g, Set.indicator_apply]
    rw [he]
    exact (integrable_const _).indicator (hA.preimage (hYm 0))
  have hh := monteCarlo_mean_strong_consistency hgi
    (hind.comp (fun _ => g) (fun _ => hg)) (fun b => (hident b).comp hg)
  have he : (∫ ω, g (Y 0 ω) ∂P) = P.real (Y 0 ⁻¹' A) := by
    change (∫ ω, (Y 0 ⁻¹' A).indicator (fun _ => (1 : ℝ)) ω ∂P) = _
    exact integral_indicator_one (hA.preimage (hYm 0))
  change ConvergesAlmostSurely P (fun B ω => sampleMean (fun b : Fin B => g (Y b ω)))
    (fun _ => ∫ ω, g (Y 0 ω) ∂P) at hh
  rw [he] at hh
  simpa only [g, Set.indicator_apply] using hh

/-- The Monte Carlo sample variance with denominator B−1 consistently
estimates the output variance under a finite second moment. -/
theorem monteCarlo_variance_strong_consistency {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hYm : ∀ b, Measurable (Y b)) (hY : MemLp (Y 0) 2 P)
    (hind : iIndepFun Y P) (hident : ∀ b, IdentDistrib (Y b) (Y 0) P P) :
    ConvergesAlmostSurely P (fun B ω => sampleVariance (fun b : Fin B => Y b ω))
      (fun _ => Var[Y 0; P]) :=
  sampleVariance_strong_consistency hYm hY hind hident

end LectureNotes
