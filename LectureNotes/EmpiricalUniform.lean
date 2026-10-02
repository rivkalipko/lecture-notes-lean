import LectureNotes.EmpiricalDistribution
import LectureNotes.QuantileConvergence
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- The empirical probability of the open lower tail. Keeping this separate
from the usual empirical CDF preserves atoms at the partition cutoffs. -/
def empiricalCDFLeft {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i, if x i < t then (1 : ℝ) else 0) / n

theorem empiricalCDF_le_left {n : ℕ} (x : Fin n → ℝ) {s t : ℝ} (hst : s < t) :
    empiricalCDF x s ≤ empiricalCDFLeft x t := by
  unfold empiricalCDF empiricalCDFLeft
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum
  intro i _
  by_cases h : x i ≤ s
  · simp [h, h.trans_lt hst]
  · simp only [if_neg h]
    split <;> norm_num

theorem empiricalCDFLeft_strong_consistency {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (t : ℝ) :
    ConvergesAlmostSurely P (fun n ω => empiricalCDFLeft (fun i : Fin n => X i ω) t)
      (fun _ => P.real {ω | X 0 ω < t}) := by
  let g : ℝ → ℝ := (Iio t).indicator (fun _ => 1)
  have hg : Measurable g := measurable_const.indicator measurableSet_Iio
  have hset : MeasurableSet {ω | X 0 ω < t} := measurableSet_lt (hX 0) measurable_const
  have hi : Integrable (fun ω => g (X 0 ω)) P := by
    have h := (integrable_const (μ := P) (1 : ℝ)).indicator hset
    simpa only [g, indicator_apply, mem_Iio, mem_ofPred_eq] using! h
  have hmean : (∫ ω, g (X 0 ω) ∂P) = P.real {ω | X 0 ω < t} := by
    simpa only [g, indicator_apply, mem_Iio, mem_ofPred_eq, Pi.one_apply] using
      integral_indicator_one (μ := P) hset
  have h := strong_law_of_large_numbers (X := fun i ω => g (X i ω)) hi
    (fun _ _ hij => (hind.comp (fun _ => g) (fun _ => hg)).indepFun hij)
    (fun i => (hident i).comp hg)
  change ConvergesAlmostSurely P
    (fun n ω => (∑ i ∈ Finset.range n, g (X i ω)) / n)
    (fun _ => ∫ ω, g (X 0 ω) ∂P) at h
  rw [hmean] at h
  simpa only [empiricalCDFLeft, ← Fin.sum_univ_eq_sum_range, g, indicator_apply,
    mem_Iio] using h

/-- A finite regular probability grid brackets every number in `[0,1]`. -/
theorem probability_grid_bracket {m : ℕ} (hm : 0 < m) {y : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∃ j : Fin m, (j : ℝ) / m ≤ y ∧ y ≤ ((j : ℝ) + 1) / m := by
  let k := min (Nat.floor ((m : ℝ) * y)) (m - 1)
  have hk : k < m := lt_of_le_of_lt (min_le_right _ _) (by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkfloor : (k : ℝ) ≤ (Nat.floor ((m : ℝ) * y) : ℝ) := by
    exact_mod_cast (min_le_left (Nat.floor ((m : ℝ) * y)) (m - 1))
  have hlo : (k : ℝ) ≤ m * y := hkfloor.trans (Nat.floor_le (mul_nonneg hmR.le hy0))
  have hup : (m : ℝ) * y ≤ k + 1 := by
    by_cases h : Nat.floor ((m : ℝ) * y) ≤ m - 1
    · simp only [k, min_eq_left h]
      exact (Nat.lt_floor_add_one _).le
    · have he : (m - 1 : ℕ) + 1 = m := by omega
      have heR : ((m - 1 : ℕ) : ℝ) + 1 = m := by exact_mod_cast he
      rw [show k = m - 1 from min_eq_right (le_of_not_ge h), heR]
      exact mul_le_of_le_one_right hmR.le hy1
  exact ⟨⟨k, hk⟩, (div_le_iff₀ hmR).mpr (by nlinarith),
    (le_div_iff₀ hmR).mpr (by nlinarith)⟩

/-- Finite quantile checks control the empirical CDF simultaneously at every
real argument, including atoms. Closed and open lower tails are both checked.
The mesh constant is deliberately only a convergence bound, not a DKW bound. -/
theorem empiricalCDF_quantile_grid_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (x : Fin n → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ j : Fin m, 0 < (j : ℕ) →
      |empiricalCDF x (distributionQuantile μ ((j : ℝ) / m)) -
        cdf μ (distributionQuantile μ ((j : ℝ) / m))| ≤ ε)
    (ho : ∀ j : Fin m, 0 < (j : ℕ) →
      |empiricalCDFLeft x (distributionQuantile μ ((j : ℝ) / m)) -
        μ.real (Iio (distributionQuantile μ ((j : ℝ) / m)))| ≤ ε) (t : ℝ) :
    |empiricalCDF x t - cdf μ t| ≤ ε + 2 / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne := hmR.ne'
  have hy0 : 0 ≤ cdf μ t := by rw [cdf_eq_real]; exact measureReal_nonneg
  have hy1 : cdf μ t ≤ 1 := cdf_le_one μ t
  obtain ⟨j, hjlo, hjhi⟩ := probability_grid_bracket hm hy0 hy1
  have hjrange : (j : ℝ) < m := by exact_mod_cast j.isLt
  have hstep : ((j : ℝ) + 1) / m = (j : ℝ) / m + 1 / m := by ring
  have htwostep : ((j : ℝ) + 2) / m = (j : ℝ) / m + 2 / m := by ring
  have hmesh : 0 ≤ 1 / (m : ℝ) := by positivity
  have hmesh2 : 2 / (m : ℝ) = 1 / m + 1 / m := by ring
  apply abs_le.mpr
  constructor
  · by_cases hj : (j : ℕ) = 0
    · have hzero : (j : ℝ) = 0 := by exact_mod_cast hj
      rw [hzero] at hjhi
      have hg := empiricalCDF_nonneg x t
      nlinarith
    · have hjp : (0 : ℝ) < j := by exact_mod_cast (Nat.pos_of_ne_zero hj)
      have hq : (j : ℝ) / m ∈ Ioo (0 : ℝ) 1 :=
        ⟨div_pos hjp hmR, (div_lt_one hmR).mpr hjrange⟩
      have hcut := (distributionQuantile_le_iff μ hq).mpr hjlo
      have hg := empiricalCDF_mono hn x hcut
      have hp := (distributionQuantile_bracket μ _ hq).2
      rw [← cdf_eq_real] at hp
      have he := (abs_le.mp (hc j (Nat.pos_of_ne_zero hj))).1
      rw [hstep] at hjhi
      nlinarith
  · by_cases htop : (j : ℕ) + 2 < m
    · let k : Fin m := ⟨(j : ℕ) + 2, htop⟩
      have hk : (k : ℝ) = (j : ℝ) + 2 := by simp [k]
      have hkp : (0 : ℝ) < k := by rw [hk]; positivity
      have hkrange : (k : ℝ) < m := by exact_mod_cast k.isLt
      have hq : (k : ℝ) / m ∈ Ioo (0 : ℝ) 1 :=
        ⟨div_pos hkp hmR, (div_lt_one hmR).mpr hkrange⟩
      have hless : cdf μ t < (k : ℝ) / m := by
        rw [hk]
        exact hjhi.trans_lt ((div_lt_div_iff_of_pos_right hmR).mpr (by linarith))
      have hcut := (lt_distributionQuantile_iff μ hq).mpr hless
      have hg := empiricalCDF_le_left x hcut
      have hp := (distributionQuantile_bracket μ _ hq).1
      have he := (abs_le.mp (ho k (by dsimp [k]; omega))).2
      have hp' : μ.real (Iio (distributionQuantile μ ((k : ℝ) / m))) ≤
          (j : ℝ) / m + 2 / m := by simpa only [← htwostep, ← hk] using hp
      clear hp
      linarith
    · have htopR : (m : ℝ) ≤ (j : ℝ) + 2 := by exact_mod_cast (le_of_not_gt htop)
      have hlast : 1 ≤ (j : ℝ) / m + 2 / m := by
        rw [← htwostep]
        exact (one_le_div hmR).mpr htopR
      have hg := empiricalCDF_le_one hn x t
      linarith

theorem empiricalCDF_both_strong_consistency {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (t : ℝ) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => empiricalCDF (fun i : Fin n => X i ω) t) atTop
        (𝓝 (cdf (P.map (X 0)) t)) ∧
      Tendsto (fun n => empiricalCDFLeft (fun i : Fin n => X i ω) t) atTop
        (𝓝 ((P.map (X 0)).real (Iio t))) := by
  have : IsProbabilityMeasure (P.map (X 0)) := Measure.isProbabilityMeasure_map (hX 0).aemeasurable
  have hec : P.real {ω | X 0 ω ≤ t} = cdf (P.map (X 0)) t := by
    rw [cdf_eq_real, map_measureReal_apply (hX 0) measurableSet_Iic]
    rfl
  have heo : P.real {ω | X 0 ω < t} = (P.map (X 0)).real (Iio t) := by
    rw [map_measureReal_apply (hX 0) measurableSet_Iio]
    rfl
  have hc : ConvergesAlmostSurely P
      (fun n ω => empiricalCDF (fun i : Fin n => X i ω) t) (fun _ => cdf (P.map (X 0)) t) := by
    simpa only [empiricalCDF, ← Fin.sum_univ_eq_sum_range, cdfIndicator, hec] using
      empiricalCDF_strong_consistency hX hind hident t
  have ho := empiricalCDFLeft_strong_consistency hX hind hident t
  rw [heo] at ho
  exact hc.and ho

theorem exists_probability_mesh {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ 2 / (m : ℝ) < ε := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / ε)
  have hmR : (0 : ℝ) < m := (div_pos (by norm_num : (0 : ℝ) < 2) hε).trans hm
  refine ⟨m, by exact_mod_cast hmR, (div_lt_iff₀ hmR).mpr ?_⟩
  have hh := (div_lt_iff₀ hε).mp hm
  nlinarith

/-- L4 Glivenko–Cantelli in its stronger almost-sure form. The convergence is
uniform on the entire real line, with no continuity assumption on the law. -/
theorem empiricalCDF_glivenko_cantelli_uniform {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, TendstoUniformly (fun n t => empiricalCDF (fun i : Fin n => X i ω) t)
      (cdf (P.map (X 0))) atTop := by
  let μ := P.map (X 0)
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (hX 0).aemeasurable
  have hall : ∀ᵐ ω ∂P, ∀ m j : ℕ,
      Tendsto (fun n => empiricalCDF (fun i : Fin n => X i ω)
        (distributionQuantile μ ((j : ℝ) / m))) atTop
          (𝓝 (cdf μ (distributionQuantile μ ((j : ℝ) / m)))) ∧
      Tendsto (fun n => empiricalCDFLeft (fun i : Fin n => X i ω)
        (distributionQuantile μ ((j : ℝ) / m))) atTop
          (𝓝 (μ.real (Iio (distributionQuantile μ ((j : ℝ) / m))))) :=
    ae_all_iff.mpr (fun m => ae_all_iff.mpr (fun j =>
      empiricalCDF_both_strong_consistency hX hind hident (distributionQuantile μ ((j : ℝ) / m))))
  filter_upwards [hall] with ω hω
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨m, hm, hmesh⟩ := exists_probability_mesh (half_pos hε)
  have hgrid : ∀ᶠ n in atTop, ∀ j : Fin m,
      |empiricalCDF (fun i : Fin n => X i ω) (distributionQuantile μ ((j : ℝ) / m)) -
        cdf μ (distributionQuantile μ ((j : ℝ) / m))| < ε / 2 ∧
      |empiricalCDFLeft (fun i : Fin n => X i ω) (distributionQuantile μ ((j : ℝ) / m)) -
        μ.real (Iio (distributionQuantile μ ((j : ℝ) / m)))| < ε / 2 := by
    apply eventually_all.mpr
    intro j
    have hc : Tendsto (fun n => |empiricalCDF (fun i : Fin n => X i ω)
        (distributionQuantile μ ((j : ℝ) / m)) -
          cdf μ (distributionQuantile μ ((j : ℝ) / m))|) atTop (𝓝 0) := by
      simpa using ((hω m j).1.sub_const (cdf μ (distributionQuantile μ ((j : ℝ) / m)))).abs
    have ho : Tendsto (fun n => |empiricalCDFLeft (fun i : Fin n => X i ω)
        (distributionQuantile μ ((j : ℝ) / m)) -
          μ.real (Iio (distributionQuantile μ ((j : ℝ) / m)))|) atTop (𝓝 0) := by
      simpa using ((hω m j).2.sub_const (μ.real (Iio (distributionQuantile μ ((j : ℝ) / m))))).abs
    exact (hc.eventually (gt_mem_nhds (half_pos hε))).and
      (ho.eventually (gt_mem_nhds (half_pos hε)))
  filter_upwards [hgrid, eventually_gt_atTop 0] with n hn hnp
  intro t
  rw [Real.dist_eq, abs_sub_comm]
  exact (empiricalCDF_quantile_grid_bound μ hnp hm _ (half_pos hε).le
    (fun j _ => (hn j).1.le) (fun j _ => (hn j).2.le) t).trans_lt (by linarith)

/-- The real supremum error appearing in the lecture's uniform statement. -/
def empiricalCDFSupError (μ : Measure ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sSup (range (fun t => |empiricalCDF x t - cdf μ t|))

theorem empiricalCDF_error_bddAbove (μ : Measure ℝ) {n : ℕ} (x : Fin n → ℝ) :
    BddAbove (range (fun t => |empiricalCDF x t - cdf μ t|)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨t, rfl⟩
  have he0 := empiricalCDF_nonneg x t
  have he1 : empiricalCDF x t ≤ 1 := by
    by_cases hn : 0 < n
    · exact empiricalCDF_le_one hn x t
    · have hn0 : n = 0 := by omega
      subst n
      simp [empiricalCDF]
  exact abs_le.mpr ⟨by linarith [cdf_le_one μ t], by linarith [cdf_nonneg μ t]⟩

theorem empiricalCDFSupError_nonneg (μ : Measure ℝ) {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ empiricalCDFSupError μ x :=
  (abs_nonneg _).trans (le_csSup (empiricalCDF_error_bddAbove μ x) (mem_range_self 0))

theorem empiricalCDFSupError_le (μ : Measure ℝ) {n : ℕ} (x : Fin n → ℝ) {ε : ℝ}
    (h : ∀ t, |empiricalCDF x t - cdf μ t| ≤ ε) : empiricalCDFSupError μ x ≤ ε :=
  csSup_le (range_nonempty _) (by rintro _ ⟨t, rfl⟩; exact h t)

/-- The actual supremum over all real arguments tends to zero almost surely. -/
theorem empiricalCDF_glivenko_cantelli_sup {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ConvergesAlmostSurely P
      (fun n ω => empiricalCDFSupError (P.map (X 0)) (fun i : Fin n => X i ω)) (fun _ => 0) := by
  filter_upwards [empiricalCDF_glivenko_cantelli_uniform hX hind hident] with ω hω
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp hω) (ε / 2) (half_pos hε)] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (empiricalCDFSupError_nonneg _ _)]
  apply (empiricalCDFSupError_le _ _ (fun t => ?_)).trans_lt (half_lt_self hε)
  simpa only [Real.dist_eq, abs_sub_comm] using (hn t).le

theorem measurable_empiricalCDF {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (t : ℝ) :
    Measurable (fun ω => empiricalCDF (fun i => X i ω) t) := by
  unfold empiricalCDF
  exact (Finset.measurable_sum _ (fun i _ =>
    (measurable_cdfIndicator t).comp (hX i))).div_const (n : ℝ)

theorem measurable_empiricalCDFLeft {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (t : ℝ) :
    Measurable (fun ω => empiricalCDFLeft (fun i => X i ω) t) := by
  unfold empiricalCDFLeft
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_lt (hX i) measurable_const) measurable_const measurable_const

/-- L4 Theorem 2(1), with the supremum over the entire real line. The finite
quantile grid is used only inside the proof; the conclusion is uniform in
the CDF argument and allows arbitrary atoms in the observation law. -/
theorem empiricalCDF_glivenko_cantelli_probability {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ConvergesInProbability P
      (fun n ω => empiricalCDFSupError (P.map (X 0)) (fun i : Fin n => X i ω)) (fun _ => 0) := by
  let μ := P.map (X 0)
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (hX 0).aemeasurable
  rw [ConvergesInProbability, tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  obtain ⟨m, hm, hmesh⟩ := exists_probability_mesh (half_pos hε)
  let q (j : Fin m) := distributionQuantile μ ((j : ℝ) / m)
  let B (n : ℕ) (ω : Ω) := ∑ j : Fin m,
    (|empiricalCDF (fun i : Fin n => X i ω) (q j) - cdf μ (q j)| +
     |empiricalCDFLeft (fun i : Fin n => X i ω) (q j) - μ.real (Iio (q j))|)
  have hBm (n : ℕ) : Measurable (B n) := by
    apply Finset.measurable_sum
    intro j _
    exact ((measurable_empiricalCDF (fun i : Fin n => X i) (fun i => hX i) (q j)).sub_const _).abs.add
      ((measurable_empiricalCDFLeft (fun i : Fin n => X i) (fun i => hX i) (q j)).sub_const _).abs
  have hBn (n : ℕ) (ω : Ω) : 0 ≤ B n ω :=
    Finset.sum_nonneg (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hBa : ConvergesAlmostSurely P B (fun _ => 0) := by
    have hall : ∀ᵐ ω ∂P, ∀ j : Fin m,
      Tendsto (fun n => empiricalCDF (fun i : Fin n => X i ω) (q j)) atTop (𝓝 (cdf μ (q j))) ∧
      Tendsto (fun n => empiricalCDFLeft (fun i : Fin n => X i ω) (q j)) atTop
        (𝓝 (μ.real (Iio (q j)))) :=
      ae_all_iff.mpr (fun j => empiricalCDF_both_strong_consistency hX hind hident (q j))
    filter_upwards [hall] with ω hω
    have hj (j : Fin m) : Tendsto (fun n =>
        |empiricalCDF (fun i : Fin n => X i ω) (q j) - cdf μ (q j)| +
        |empiricalCDFLeft (fun i : Fin n => X i ω) (q j) - μ.real (Iio (q j))|)
        atTop (𝓝 0) := by
      simpa using (((hω j).1.sub_const (cdf μ (q j))).abs.add
        ((hω j).2.sub_const (μ.real (Iio (q j)))).abs)
    simpa only [B, Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => hj j)
  have hBp := almost_sure_implies_probability (fun n => (hBm n).aemeasurable) hBa
  have hbound (n : ℕ) (hn : 0 < n) (ω : Ω) :
      empiricalCDFSupError μ (fun i : Fin n => X i ω) ≤ B n ω + 2 / m := by
    have hsingle (j : Fin m) :
        |empiricalCDF (fun i : Fin n => X i ω) (q j) - cdf μ (q j)| +
          |empiricalCDFLeft (fun i : Fin n => X i ω) (q j) - μ.real (Iio (q j))| ≤ B n ω := by
      change _ ≤ ∑ k : Fin m,
        (|empiricalCDF (fun i : Fin n => X i ω) (q k) - cdf μ (q k)| +
          |empiricalCDFLeft (fun i : Fin n => X i ω) (q k) - μ.real (Iio (q k))|)
      apply Finset.single_le_sum (s := Finset.univ) (a := j)
        (f := fun k : Fin m =>
          |empiricalCDF (fun i : Fin n => X i ω) (q k) - cdf μ (q k)| +
            |empiricalCDFLeft (fun i : Fin n => X i ω) (q k) - μ.real (Iio (q k))|)
      · intro k _
        exact add_nonneg (abs_nonneg _) (abs_nonneg _)
      · exact Finset.mem_univ j
    apply empiricalCDFSupError_le
    intro t
    apply empiricalCDF_quantile_grid_bound μ hn hm _ (hBn n ω)
    · intro j _
      apply (le_add_of_nonneg_right (abs_nonneg _)).trans
      exact hsingle j
    · intro j _
      apply (le_add_of_nonneg_left (abs_nonneg _)).trans
      exact hsingle j
  have hprob := (tendstoInMeasure_iff_measureReal_norm.mp hBp) (ε / 2) (half_pos hε)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hprob
  filter_upwards [eventually_gt_atTop 0] with n hn
  apply measureReal_mono _ (measure_ne_top P _)
  intro ω hω
  simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (empiricalCDFSupError_nonneg _ _), abs_of_nonneg (hBn n ω)] at hω ⊢
  have hh := hbound n hn ω
  linarith

end LectureNotes
