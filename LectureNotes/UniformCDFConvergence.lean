import LectureNotes.EmpiricalUniform
import LectureNotes.CDFConvergence

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- A real probability law with no atoms has a continuous CDF. -/
theorem continuous_cdf_of_atomless (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Continuous (cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hz : ENNReal.ofReal (cdf μ t - Function.leftLim (cdf μ) t) = 0 := by
    rw [← StieltjesFunction.measure_singleton, measure_cdf, measure_singleton]
  have he : Function.leftLim (cdf μ) t = cdf μ t :=
    le_antisymm ((monotone_cdf μ).leftLim_le le_rfl)
      (sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hz))
  have hl := (monotone_cdf μ).continuousWithinAt_Iio_iff_leftLim_eq.mpr he
  have hr := (cdf μ).right_continuous t
  simpa only [Iio_union_Ici, continuousWithinAt_univ] using hl.union hr

/-- A finite probability grid controls the discrepancy from an atomless CDF. -/
theorem cdf_quantile_grid_bound (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [IsProbabilityMeasure ν]
    {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ j : Fin m, 0 < (j : ℕ) →
      |cdf ν (distributionQuantile μ ((j : ℝ) / m)) -
        cdf μ (distributionQuantile μ ((j : ℝ) / m))| ≤ ε)
 (t : ℝ) :
    |cdf ν t - cdf μ t| ≤ ε + 2 / m := by
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
      have hg : 0 ≤ cdf ν t := by rw [cdf_eq_real]; exact measureReal_nonneg
      nlinarith
    · have hjp : (0 : ℝ) < j := by exact_mod_cast (Nat.pos_of_ne_zero hj)
      have hq : (j : ℝ) / m ∈ Ioo (0 : ℝ) 1 :=
        ⟨div_pos hjp hmR, (div_lt_one hmR).mpr hjrange⟩
      have hcut := (distributionQuantile_le_iff μ hq).mpr hjlo
      have hg := monotone_cdf ν hcut
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
      have hg := monotone_cdf ν hcut.le
      have hp : cdf μ (distributionQuantile μ ((k : ℝ) / m)) = (k : ℝ) / m := by
        rw [cdf_eq_real]
        exact distributionQuantile_exact μ _ hq
      have he := (abs_le.mp (hc k (by dsimp [k]; omega))).2
      rw [hp, hk, htwostep] at he
      rw [hk, htwostep] at hg
      linarith
    · have htopR : (m : ℝ) ≤ (j : ℝ) + 2 := by exact_mod_cast (le_of_not_gt htop)
      have hlast : 1 ≤ (j : ℝ) / m + 2 / m := by
        rw [← htwostep]
        exact (one_le_div hmR).mpr htopR
      have hg := cdf_le_one ν t
      linarith

/-- Pólya's theorem: pointwise convergence of CDFs to an atomless probability
law is uniform over the whole real line, even when approximating laws have atoms. -/
theorem cdf_tendstoUniformly_of_pointwise (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (h : ∀ t, Tendsto (fun n => cdf (μ n) t) atTop (𝓝 (cdf ν t))) :
    TendstoUniformly (fun n t => cdf (μ n) t) (cdf ν) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨m, hm, hmesh⟩ := exists_probability_mesh (half_pos hε)
  have hgrid : ∀ᶠ n in atTop, ∀ j : Fin m,
      |cdf (μ n) (distributionQuantile ν ((j : ℝ) / m)) -
        cdf ν (distributionQuantile ν ((j : ℝ) / m))| < ε / 2 := by
    apply eventually_all.mpr
    intro j
    have hc : Tendsto (fun n => |cdf (μ n) (distributionQuantile ν ((j : ℝ) / m)) -
        cdf ν (distributionQuantile ν ((j : ℝ) / m))|) atTop (𝓝 0) := by
      simpa using ((h (distributionQuantile ν ((j : ℝ) / m))).sub_const
        (cdf ν (distributionQuantile ν ((j : ℝ) / m)))).abs
    exact hc.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hgrid] with n hn
  intro t
  rw [Real.dist_eq, abs_sub_comm]
  exact (cdf_quantile_grid_bound ν (μ n) hm (half_pos hε).le
    (fun j _ => (hn j).le) t).trans_lt (by linarith)

/-- Weak convergence to an atomless real probability law implies uniform CDF
convergence. This is useful for conditional bootstrap distributions. -/
theorem probabilityMeasure_tendsto_uniform_cdf (μ : ℕ → ProbabilityMeasure ℝ)
    (ν : ProbabilityMeasure ℝ) [NullSingletonClass (ν : Measure ℝ)]
    (h : Tendsto μ atTop (𝓝 ν)) :
    TendstoUniformly (fun n t => cdf (μ n : Measure ℝ) t) (cdf (ν : Measure ℝ)) atTop := by
  apply cdf_tendstoUniformly_of_pointwise
  intro t
  exact (probabilityMeasure_tendsto_iff_cdf μ ν).mp h t (continuous_cdf_of_atomless _).continuousAt

end LectureNotes
