import LectureNotes.TwoSampleMeanCLT
import LectureNotes.VarianceAsymptotics
import LectureNotes.NormalTestPower

noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped Topology NNReal

/-- A bound for a weighted average of relative variance errors. It avoids
requiring the deterministic weights to have limits. -/
theorem weighted_relative_error_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (u v : ℝ) :
    |(a * u + b * v) / (a + b) - 1| ≤ |u - 1| + |v - 1| := by
  have hd : 0 < a + b := add_pos ha hb
  have he : (a * u + b * v) / (a + b) - 1 =
      (a * (u - 1) + b * (v - 1)) / (a + b) := by field_simp; ring
  rw [he, abs_div, abs_of_pos hd, div_le_iff₀ hd]
  have ht := abs_add_le (a * (u - 1)) (b * (v - 1))
  simp only [abs_mul, abs_of_pos ha, abs_of_pos hb] at ht
  nlinarith [mul_nonneg ha.le (abs_nonneg (v - 1)),
    mul_nonneg hb.le (abs_nonneg (u - 1))]

theorem two_sample_relative_variance_limit {m n : ℕ → ℕ}
    (hm : ∀ k, 0 < m k) (hn : ∀ k, 0 < n k)
    {vx vy : ℝ} (hvx : 0 < vx) (hvy : 0 < vy) {sx sy : ℕ → ℝ}
    (hx : Tendsto sx atTop (𝓝 vx)) (hy : Tendsto sy atTop (𝓝 vy)) :
    Tendsto (fun k => (sx k / m k + sy k / n k) / (vx / m k + vy / n k))
      atTop (𝓝 1) := by
  have hdx : Tendsto (fun k => |sx k / vx - 1|) atTop (𝓝 0) := by
    simpa only [div_self hvx.ne', sub_self, abs_zero] using ((hx.div_const vx).sub_const 1).abs
  have hdy : Tendsto (fun k => |sy k / vy - 1|) atTop (𝓝 0) := by
    simpa only [div_self hvy.ne', sub_self, abs_zero] using ((hy.div_const vy).sub_const 1).abs
  have hlim : Tendsto (fun k => |(sx k / m k + sy k / n k) /
      (vx / m k + vy / n k) - 1|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) _ (by simpa only [add_zero] using hdx.add hdy)
    intro k
    have h := weighted_relative_error_bound
      (div_pos hvx (show (0 : ℝ) < m k by exact_mod_cast hm k))
      (div_pos hvy (show (0 : ℝ) < n k by exact_mod_cast hn k))
      (sx k / vx) (sy k / vy)
    convert! h using 1 <;> congr 2 <;> field_simp
  have hzero : Tendsto (fun k => (sx k / m k + sy k / n k) /
      (vx / m k + vy / n k) - 1) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using hlim
  simpa only [sub_add_cancel, zero_add] using hzero.add_const 1

/-- The estimated Welch standard error divided by the true standard error
converges almost surely to one, including arbitrarily imbalanced sample sizes. -/
theorem two_sample_standard_error_ratio_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hX : MemLp (X 0) 2 P) (hY : MemLp (Y 0) 2 P)
    (hind : iIndepFun (Sum.elim X Y) P)
    (hidentX : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hvx : 0 < Var[X 0; P]) (hvy : 0 < Var[Y 0; P])
    (m n : ℕ → ℕ) (hmpos : ∀ k, 0 < m k) (hnpos : ∀ k, 0 < n k)
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop) :
    ∀ᵐ ω ∂P, Tendsto
      (fun k => Real.sqrt (sampleVariance (fun i : Fin (m k) => X i ω) / m k +
        sampleVariance (fun i : Fin (n k) => Y i ω) / n k) /
          twoSampleStandardError (m k) (n k) Var[X 0; P] Var[Y 0; P]) atTop (𝓝 1) := by
  have hiX : iIndepFun X P := by
    simpa only [Sum.elim_inl] using iIndepFun.precomp
      (g := fun i : ℕ => (Sum.inl i : ℕ ⊕ ℕ)) Sum.inl_injective hind
  have hiY : iIndepFun Y P := by
    simpa only [Sum.elim_inr] using iIndepFun.precomp
      (g := fun i : ℕ => (Sum.inr i : ℕ ⊕ ℕ)) Sum.inr_injective hind
  filter_upwards [sampleVariance_strong_consistency hXm hX hiX hidentX,
    sampleVariance_strong_consistency hYm hY hiY hidentY] with ω hx hy
  have h := two_sample_relative_variance_limit hmpos hnpos hvx hvy (hx.comp hm) (hy.comp hn)
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simp only [Function.comp_def, Real.sqrt_one] at hh
  convert! hh using 1
  funext k
  dsimp only [twoSampleStandardError]
  exact (Real.sqrt_div' _ (by positivity)).symm

/-- The actual Welch statistic, centered at a specified mean difference.
Finite samples with zero estimated standard error use Lean's division convention;
the asymptotic theorem below includes these rare events. -/
def welchStatistic {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) (Δ : ℝ) : ℝ :=
  (sampleMean x - sampleMean y - Δ) /
    Real.sqrt (sampleVariance x / m + sampleVariance y / n)

/-- L8: Welch studentization is asymptotically standard normal under finite
second moments, positive group variances and arbitrary diverging group sizes. -/
theorem two_sample_welch_clt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hX : MemLp (X 0) 2 P) (hY : MemLp (Y 0) 2 P)
    (hind : iIndepFun (Sum.elim X Y) P)
    (hidentX : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hvx : 0 < Var[X 0; P]) (hvy : 0 < Var[Y 0; P])
    (m n : ℕ → ℕ) (hmpos : ∀ k, 0 < m k) (hnpos : ∀ k, 0 < n k)
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun k ω => welchStatistic (fun i : Fin (m k) => X i ω)
        (fun i : Fin (n k) => Y i ω) (P[X 0] - P[Y 0])) id := by
  let R (k : ℕ) (ω : Ω) := Real.sqrt
    (sampleVariance (fun i : Fin (m k) => X i ω) / m k +
      sampleVariance (fun i : Fin (n k) => Y i ω) / n k) /
        twoSampleStandardError (m k) (n k) Var[X 0; P] Var[Y 0; P]
  have hRm k : Measurable (R k) := by unfold R sampleVariance sampleMean; fun_prop
  have hR : ConvergesInProbability P R (fun _ => 1) :=
    almost_sure_implies_probability (fun k => (hRm k).aemeasurable)
      (two_sample_standard_error_ratio_ae hXm hYm hX hY hind hidentX hidentY hvx hvy m n hmpos hnpos hm hn)
  have hZ := two_sample_mean_clt hXm hYm hX hY hind hidentX hidentY hvx hvy m n hmpos hnpos hm hn
  have h := slutsky_div (by norm_num : (1 : ℝ) ≠ 0) hZ hR (fun k => (hRm k).aemeasurable)
  simp only [div_one] at h
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl)) h
  intro k
  apply ae_of_all
  intro ω
  have hs := (twoSampleStandardError_pos (hmpos k) (hnpos k) hvx hvy).ne'
  dsimp only [R, welchStatistic]
  by_cases hz : Real.sqrt (sampleVariance (fun i : Fin (m k) => X i ω) / m k +
    sampleVariance (fun i : Fin (n k) => Y i ω) / n k) = 0
  · simp [hz]
  · field_simp

/-- The source's upper-tail Welch test has asymptotic size α under equality
of the population means. The critical value is the exact normal quantile. -/
theorem two_sample_welch_null_size {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hX : MemLp (X 0) 2 P) (hY : MemLp (Y 0) 2 P)
    (hind : iIndepFun (Sum.elim X Y) P)
    (hidentX : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hvx : 0 < Var[X 0; P]) (hvy : 0 < Var[Y 0; P])
    (hnull : P[X 0] = P[Y 0])
    (m n : ℕ → ℕ) (hmpos : ∀ k, 0 < m k) (hnpos : ∀ k, 0 < n k)
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun k => P.real {ω | distributionQuantile (gaussianReal 0 1) (1 - α) <
      welchStatistic (fun i : Fin (m k) => X i ω) (fun i : Fin (n k) => Y i ω) 0})
      atTop (𝓝 α) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have h := two_sample_welch_clt hXm hYm hX hY hind hidentX hidentY hvx hvy m n hmpos hnpos hm hn
  rw [hnull, sub_self] at h
  have hb : (gaussianReal 0 1).map id
      (frontier (Ioi (distributionQuantile (gaussianReal 0 1) (1 - α)))) = 0 := by
    rw [Measure.map_id, frontier_Ioi, measure_singleton]
  have ht := asymptotic_rejection_probability h
    (Ioi (distributionQuantile (gaussianReal 0 1) (1 - α))) measurableSet_Ioi hb
  have hs := normal_upper_quantile_size (by norm_num : (0 : ℝ≥0) < 1)
    measurable_id (HasLaw.id : HasLaw id (gaussianReal 0 1) (gaussianReal 0 1)) hα
  simp only [NNReal.coe_one, Real.sqrt_one, zero_add, mul_one, id_eq] at hs
  simpa only [Set.mem_Ioi, id_eq, hs] using ht

end LectureNotes
