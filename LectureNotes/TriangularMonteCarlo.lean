import LectureNotes.MonteCarlo
import LectureNotes.DKW
import LectureNotes.RowDeltaMethod

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- A positive separation from the population CDF at two bracketing points
turns a quantile error into a uniform empirical-CDF error. -/
theorem empirical_quantile_error_subset {m : ℕ} [NeZero m]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {q c ε δ : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε)
    (hlo : cdf μ (c - ε / 2) + δ < q)
    (hhi : q + δ < cdf μ (c + ε / 2)) :
    {y : Fin m → ℝ | ε ≤ |distributionQuantile (empiricalLaw y) q - c|} ⊆
      {y | δ < empiricalCDFSupError μ y} := by
  intro y hy
  have hb (t : ℝ) : |empiricalCDF y t - cdf μ t| ≤ empiricalCDFSupError μ y :=
    le_csSup (empiricalCDF_error_bddAbove μ y) (mem_range_self t)
  change ε ≤ |distributionQuantile (empiricalLaw y) q - c| at hy
  rcases le_abs.mp hy with hr | hl
  · have hQ : c + ε / 2 < distributionQuantile (empiricalLaw y) q := by linarith
    have he := (lt_distributionQuantile_iff (empiricalLaw y) hq).1 hQ
    rw [empiricalLaw_cdf] at he
    have hab := neg_le_abs (empiricalCDF y (c + ε / 2) - cdf μ (c + ε / 2))
    have hh := hb (c + ε / 2)
    change δ < empiricalCDFSupError μ y
    linarith

  · have hQ : distributionQuantile (empiricalLaw y) q ≤ c - ε / 2 := by linarith
    have he := (distributionQuantile_le_iff (empiricalLaw y) hq).1 hQ
    rw [empiricalLaw_cdf] at he
    have hab := le_abs_self (empiricalCDF y (c - ε / 2) - cdf μ (c - ε / 2))
    have hh := hb (c - ε / 2)
    change δ < empiricalCDFSupError μ y
    linarith

theorem monteCarlo_quantile_error_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {m : ℕ} [NeZero m] (Y : Fin m → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y P) (hlaw : ∀ i, HasLaw (Y i) μ P)
    {q c ε δ : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε) (hδ : 0 < δ)
    (hlo : cdf μ (c - ε / 2) + δ < q)
    (hhi : q + δ < cdf μ (c + ε / 2)) :
    P.real {ω | ε ≤ |distributionQuantile (empiricalLaw (fun i => Y i ω)) q - c|} ≤
      2 * Real.exp (-2 * m * δ ^ 2) := by
  apply (measureReal_mono (μ := P) (fun ω hω =>
    empirical_quantile_error_subset μ hq hε hlo hhi hω)).trans
  exact dkw_inequality μ (Nat.pos_of_ne_zero (NeZero.ne m)) Y hY hind hlaw hδ

theorem dkw_rate_tendsto_zero {B : ℕ → ℕ} (hB : Tendsto B atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => 2 * Real.exp (-2 * B n * δ ^ 2)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n => (B n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hB
  have hneg : Tendsto (fun n => -2 * (B n : ℝ) * δ ^ 2) atTop atBot := by
    convert tendsto_neg_atTop_atBot.comp (hnat.const_mul_atTop (show 0 < 2 * δ ^ 2 by positivity)) using 1
    funext n
    dsimp only [Function.comp_apply]
    ring
  simpa using (Real.tendsto_exp_atBot.comp hneg).const_mul 2

/-- Monte Carlo quantiles remain consistent when both the simulated law and
the replication count vary. Only within-row independence is required. -/
theorem triangular_monteCarlo_quantile_probability {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (μ : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (μ n)] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (hstrict : StrictMono (cdf ν))
    {B : ℕ → ℕ} [∀ n, NeZero (B n)] (hB : Tendsto B atTop atTop)
    (Y : ∀ n, Fin (B n) → Ω n → ℝ) (hY : ∀ n i, Measurable (Y n i))
    (hind : ∀ n, iIndepFun (Y n) (P n))
    (hlaw : ∀ n i, HasLaw (Y n i) (μ n) (P n))
    (hconv : ∀ t, Tendsto (fun n => cdf (μ n) t) atTop (𝓝 (cdf ν t)))
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    RowProbabilityZero P (fun n ω =>
      distributionQuantile (empiricalLaw (fun i => Y n i ω)) q - distributionQuantile ν q) := by
  intro ε hε
  let c := distributionQuantile ν q
  have hc : cdf ν c = q := by
    rw [cdf_eq_real]
    exact distributionQuantile_exact ν q hq
  have hlo : cdf ν (c - ε / 2) < q := by
    rw [← hc]
    exact hstrict (by linarith)
  have hhi : q < cdf ν (c + ε / 2) := by
    rw [← hc]
    exact hstrict (by linarith)
  let δ := min (q - cdf ν (c - ε / 2)) (cdf ν (c + ε / 2) - q) / 3
  have hδ : 0 < δ := div_pos (lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi)) (by norm_num)
  have hdlo : cdf ν (c - ε / 2) < q - δ := by
    have hm := min_le_left (q - cdf ν (c - ε / 2)) (cdf ν (c + ε / 2) - q)
    dsimp [δ]
    linarith
  have hdhi : q + δ < cdf ν (c + ε / 2) := by
    have hm := min_le_right (q - cdf ν (c - ε / 2)) (cdf ν (c + ε / 2) - q)
    dsimp [δ]
    linarith
  have he := (hconv (c - ε / 2)).eventually (gt_mem_nhds hdlo)
  have hf := (hconv (c + ε / 2)).eventually (lt_mem_nhds hdhi)
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _
    (dkw_rate_tendsto_zero hB hδ)
  filter_upwards [he, hf] with n hn hn'
  simpa only [Real.norm_eq_abs] using monteCarlo_quantile_error_bound
    (μ n) (Y n) (hY n) (hind n) (hlaw n) hq hε hδ (by linarith) hn'

/-- Joint measurability of the empirical quantile of independent seed outputs.
The statement also applies to dependent seeds; independence is needed only
for the error bound. -/
theorem measurable_simulated_quantile {Ω Γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Γ] {S : Ω × Γ → ℝ} (hS : Measurable S)
    {m : ℕ} [NeZero m] {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun z : Ω × (Fin m → Γ) =>
      distributionQuantile (empiricalLaw (fun b => S (z.1, z.2 b))) q) := by
  apply (measurable_empirical_quantile hq).comp
  exact measurable_pi_lambda _ fun b =>
    hS.comp (measurable_fst.prodMk ((measurable_pi_apply b).comp measurable_snd))

theorem measureReal_prod_event {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set (Ω × Γ)} (hA : MeasurableSet A) :
    (P.prod Q).real A = ∫ ω, Q.real (Prod.mk ω ⁻¹' A) ∂P := by
  rw [← integral_indicator_one hA]
  change (∫ z, A.indicator (fun _ => (1 : ℝ)) z ∂P.prod Q) = _
  rw [integral_prod _ ((integrable_const (1 : ℝ)).indicator hA)]
  apply integral_congr_ae
  filter_upwards [] with ω
  have he : (fun γ => A.indicator (fun _ => (1 : ℝ)) (ω, γ)) =
      (Prod.mk ω ⁻¹' A).indicator (fun _ => (1 : ℝ)) := by
    rfl
  rw [he]
  exact integral_indicator_one (hA.preimage measurable_prodMk_left)

/-- Simulation error with B(n)→∞ vanishes under the actual joint law of the
observed data and independently generated simulation seeds. Conditional-law
validity is an explicit almost-sure premise and may vary with n. -/
theorem conditional_monteCarlo_quantile_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Γ : ℕ → Type*}
    [∀ n, MeasurableSpace (Γ n)] (Q : ∀ n, Measure (Γ n))
    [∀ n, IsProbabilityMeasure (Q n)] {B : ℕ → ℕ} [∀ n, NeZero (B n)]
    (hB : Tendsto B atTop atTop) (S : ∀ n, Ω × Γ n → ℝ)
    (hS : ∀ n, Measurable (S n)) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (hstrict : StrictMono (cdf ν))
    (hconv : ∀ᵐ ω ∂P, ∀ t, Tendsto
      (fun n => cdf ((Q n).map (fun γ => S n (ω, γ))) t) atTop (𝓝 (cdf ν t)))
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    RowProbabilityZero (fun n => P.prod (Measure.pi (fun _ : Fin (B n) => Q n)))
      (fun n z => distributionQuantile (empiricalLaw (fun b => S n (z.1, z.2 b))) q -
        distributionQuantile ν q) := by
  let R n := Measure.pi (fun _ : Fin (B n) => Q n)
  let E n : Ω × (Fin (B n) → Γ n) → ℝ := fun z =>
    distributionQuantile (empiricalLaw (fun b => S n (z.1, z.2 b))) q - distributionQuantile ν q
  have hE n : Measurable (E n) := (measurable_simulated_quantile (hS n) hq).sub measurable_const
  have hR n : IsProbabilityMeasure (R n) := by dsimp [R]; infer_instance
  intro ε hε
  let A n : Set (Ω × (Fin (B n) → Γ n)) := {z | ε ≤ ‖E n z‖}
  have hA n : MeasurableSet (A n) := measurableSet_le measurable_const (hE n).norm
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => (R n).real (Prod.mk ω ⁻¹' A n)) atTop (𝓝 0) := by
    filter_upwards [hconv] with ω hω
    let μ n := (Q n).map (fun γ => S n (ω, γ))
    have hSm n : Measurable (fun γ => S n (ω, γ)) :=
      (hS n).comp (measurable_const.prodMk measurable_id)
    have hμ n : IsProbabilityMeasure (μ n) :=
      Measure.isProbabilityMeasure_map (hSm n).aemeasurable
    have hYm n (b : Fin (B n)) : Measurable (fun z : Fin (B n) → Γ n => S n (ω, z b)) :=
      (hSm n).comp (measurable_pi_apply b)
    have hind n : iIndepFun (fun b (z : Fin (B n) → Γ n) => S n (ω, z b)) (R n) :=
      iIndepFun_pi (fun _ => (hSm n).aemeasurable)
    have hlaw n (b : Fin (B n)) :
        HasLaw (fun z : Fin (B n) → Γ n => S n (ω, z b)) (μ n) (R n) := by
      have he : HasLaw (fun z : Fin (B n) → Γ n => z b) (Q n) (R n) :=
        ⟨(measurable_pi_apply b).aemeasurable, (measurePreserving_eval _ b).map_eq⟩
      exact (HasLaw.mk (hSm n).aemeasurable rfl).comp he
    exact triangular_monteCarlo_quantile_probability R μ ν hstrict hB
      (fun n b z => S n (ω, z b)) hYm hind hlaw hω hq ε hε
  have hc := tendsto_integral_of_dominated_convergence (μ := P) (fun _ => (1 : ℝ))
    (fun n => (measurable_measure_prodMk_left (hA n)).ennreal_toReal.aestronglyMeasurable)
    (integrable_const 1)
    (fun n => ae_of_all _ fun ω => by
      change ‖(R n).real (Prod.mk ω ⁻¹' A n)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one (μ := R n)) hlim
  simp only [integral_zero] at hc
  change Tendsto (fun n => ∫ ω, (R n).real (Prod.mk ω ⁻¹' A n) ∂P) atTop (𝓝 0) at hc
  have he n : (P.prod (R n)).real (A n) = ∫ ω, (R n).real (Prod.mk ω ⁻¹' A n) ∂P :=
    measureReal_prod_event P (R n) (hA n)
  change Tendsto (fun n => (P.prod (R n)).real (A n)) atTop (𝓝 0)
  simpa only [← he] using hc

end LectureNotes
