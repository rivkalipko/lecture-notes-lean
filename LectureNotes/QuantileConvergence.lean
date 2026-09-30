import LectureNotes.QuantileIntervals

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem distributionQuantile_le_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q x : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    distributionQuantile μ q ≤ x ↔ q ≤ cdf μ x := by
  constructor
  · intro h
    have hc := (distributionQuantile_bracket μ q hq).2
    rw [← cdf_eq_real] at hc
    exact hc.trans ((monotone_cdf μ) h)
  · intro h
    have hb : BddBelow {t | q ≤ cdf μ t} := by
      obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds hq.1)).exists
      refine ⟨a, fun t ht => ?_⟩
      by_contra hlt
      have hm := (monotone_cdf μ) (le_of_not_ge hlt)
      change q ≤ cdf μ t at ht
      linarith
    exact csInf_le hb h

theorem lt_distributionQuantile_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q x : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    x < distributionQuantile μ q ↔ cdf μ x < q := by
  simpa only [not_le] using not_congr (distributionQuantile_le_iff μ (x := x) hq)

theorem distributionQuantile_mono (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    distributionQuantile μ a ≤ distributionQuantile μ b := by
  apply (distributionQuantile_le_iff μ ha).mpr
  rw [cdf_eq_real]
  exact hab.trans (distributionQuantile_bracket μ b hb).2

/-- Convergent CDFs give convergent quantiles at a strictly increasing,
atomless limiting distribution. The approximating laws may be discrete. -/
theorem distributionQuantile_tendsto (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hstrict : StrictMono (cdf ν))
    (hconv : ∀ x, Tendsto (fun n => cdf (μ n) x) atTop (𝓝 (cdf ν x)))
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => distributionQuantile (μ n) q) atTop (𝓝 (distributionQuantile ν q)) := by
  have he : cdf ν (distributionQuantile ν q) = q := by
    rw [cdf_eq_real, distributionQuantile_exact ν q hq]
  apply tendsto_order.mpr
  constructor
  · intro x hx
    have hlt : cdf ν x < q := (lt_distributionQuantile_iff ν hq).mp hx
    filter_upwards [(hconv x).eventually (gt_mem_nhds hlt)] with n hn
    exact (lt_distributionQuantile_iff (μ n) hq).mpr hn
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := exists_between hx
    have hlt : q < cdf ν y := by simpa only [he] using hstrict hy
    filter_upwards [(hconv y).eventually (lt_mem_nhds hlt)] with n hn
    exact ((distributionQuantile_le_iff (μ n) hq).mpr hn.le).trans_lt hyx

/-- The conditional-law quantile step used by the bootstrap. Almost-sure
convergence of the conditional CDFs is an explicit validity condition; no
independence between the data and their critical values is assumed. -/
theorem bootstrap_quantile_consistency {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B : ℕ → Ω → Measure ℝ) (ν : Measure ℝ)
    [∀ n ω, IsProbabilityMeasure (B n ω)] [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hstrict : StrictMono (cdf ν))
    (hconv : ∀ᵐ ω ∂P, ∀ x, Tendsto (fun n => cdf (B n ω) x) atTop (𝓝 (cdf ν x)))
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hm : ∀ n, AEMeasurable (fun ω => distributionQuantile (B n ω) q) P) :
    ConvergesInProbability P (fun n ω => distributionQuantile (B n ω) q)
      (fun _ => distributionQuantile ν q) := by
  apply almost_sure_implies_probability hm
  filter_upwards [hconv] with ω hω
  exact distributionQuantile_tendsto (fun n => B n ω) ν hstrict hω hq

/-- Replacing a fixed critical value by a consistent data-dependent value
preserves its asymptotic acceptance probability at an atomless limiting law. -/
theorem random_critical_value_probability {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T C : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {ν : Measure ℝ}
    [IsProbabilityMeasure ν] [NullSingletonClass ν] {c : ℝ}
    (hT : ConvergesInDistribution P Q T Z) (hZ : HasLaw Z ν Q)
    (hC : ConvergesInProbability P C (fun _ => c))
    (hm : ∀ n, AEMeasurable (C n) P) :
    Tendsto (fun n => P.real {ω | T n ω ≤ C n ω}) atTop (𝓝 (cdf ν c)) := by
  have hd : ConvergesInDistribution P Q (fun n ω => T n ω - C n ω) (fun ω => Z ω - c) :=
    TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun z : ℝ × ℝ => z.1 - z.2) (by fun_prop) hT hC hm
  have hzm : AEMeasurable (fun ω => Z ω - c) Q := hZ.aemeasurable.sub aemeasurable_const
  have hz : (Q.map (fun ω => Z ω - c)) (frontier (Iic (0 : ℝ))) = 0 := by
    rw [frontier_Iic, Measure.map_apply_of_aemeasurable
      hzm (measurableSet_singleton _)]
    have he : (fun ω => Z ω - c) ⁻¹' {0} = Z ⁻¹' {c} := by ext ω; simp [sub_eq_zero]
    rw [he, ← Measure.map_apply_of_aemeasurable hZ.aemeasurable (measurableSet_singleton c),
      hZ.map_eq, measure_singleton]
  have h := asymptotic_rejection_probability hd (Iic 0) measurableSet_Iic hz
  have he : Q.real {ω | Z ω ≤ c} = cdf ν c := by
    exact (hZ.measureReal_eq (p := fun x => x ≤ c) measurableSet_Iic).trans (cdf_eq_real _ _).symm
  simpa only [mem_Iic, sub_nonpos, he] using h

/-- A bootstrap upper-tail quantile test has asymptotic size `1-q` once the
conditional CDF validity and the sampling limit hold. -/
theorem bootstrap_upper_tail_size {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : ℕ → Ω → ℝ} {Z : Ω' → ℝ} (ν : Measure ℝ)
    [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (B : ℕ → Ω → Measure ℝ) [∀ n ω, IsProbabilityMeasure (B n ω)]
    (hT : ConvergesInDistribution P Q T Z) (hZ : HasLaw Z ν Q)
    (hstrict : StrictMono (cdf ν))
    (hconv : ∀ᵐ ω ∂P, ∀ x, Tendsto (fun n => cdf (B n ω) x) atTop (𝓝 (cdf ν x)))
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hm : ∀ n, Measurable (T n))
    (hb : ∀ n, Measurable (fun ω => distributionQuantile (B n ω) q)) :
    Tendsto (fun n => P.real {ω | distributionQuantile (B n ω) q < T n ω}) atTop (𝓝 (1 - q)) := by
  have hc := bootstrap_quantile_consistency B ν hstrict hconv hq (fun n => (hb n).aemeasurable)
  have ht := random_critical_value_probability hT hZ hc (fun n => (hb n).aemeasurable)
  rw [cdf_eq_real, distributionQuantile_exact ν q hq] at ht
  have he (n) : P.real {ω | distributionQuantile (B n ω) q < T n ω} =
      1 - P.real {ω | T n ω ≤ distributionQuantile (B n ω) q} := by
    have hs : {ω | distributionQuantile (B n ω) q < T n ω} =
        {ω | T n ω ≤ distributionQuantile (B n ω) q}ᶜ := by ext ω; simp
    rw [hs, measureReal_compl (measurableSet_le (hm n) (hb n)), probReal_univ]
  simp_rw [he]
  exact tendsto_const_nhds.sub ht

/-- Quantiles commute with increasing bijective reparameterizations. This
holds with atoms as well; the lower generalized-inverse convention is fixed. -/
theorem distributionQuantile_orderIso (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (e : ℝ ≃o ℝ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    distributionQuantile (μ.map e) q = e (distributionQuantile μ q) := by
  have hm : Measurable e := e.monotone.measurable
  have : IsProbabilityMeasure (μ.map e) := Measure.isProbabilityMeasure_map hm.aemeasurable
  have hc (t : ℝ) : cdf (μ.map e) t = cdf μ (e.symm t) := by
    rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply hm measurableSet_Iic]
    congr 1
    ext x
    exact e.le_symm_apply.symm
  have he (t : ℝ) : distributionQuantile (μ.map e) q ≤ t ↔ e (distributionQuantile μ q) ≤ t := by
    rw [distributionQuantile_le_iff _ hq, hc, ← distributionQuantile_le_iff μ hq,
      e.le_symm_apply]
  exact le_antisymm ((he _).mpr le_rfl) ((he _).mp le_rfl)

/-- Transforming both equal-tail endpoints gives the quantile interval of
the transformed posterior for an increasing bijection. -/
theorem quantile_interval_orderIso (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (e : ℝ ≃o ℝ) {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    e '' Icc (distributionQuantile μ a) (distributionQuantile μ b) =
      Icc (distributionQuantile (μ.map e) a) (distributionQuantile (μ.map e) b) := by
  rw [distributionQuantile_orderIso μ e ha, distributionQuantile_orderIso μ e hb]
  exact e.image_Icc _ _

end LectureNotes
