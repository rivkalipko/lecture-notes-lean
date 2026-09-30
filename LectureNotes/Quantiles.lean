import LectureNotes.MonotoneLikelihoodRatio

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

/-- The lower generalized inverse of the cumulative distribution function.
The calibration theorems use probabilities strictly between zero and one. -/
def distributionQuantile (μ : Measure ℝ) (q : ℝ) : ℝ := sInf {x | q ≤ cdf μ x}

/-- A quantile brackets its target probability between the open and closed
lower tails, so jumps of the distribution are retained. -/
theorem distributionQuantile_bracket (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) :
    μ.real (Iio (distributionQuantile μ q)) ≤ q ∧
      q ≤ μ.real (Iic (distributionQuantile μ q)) := by
  let S : Set ℝ := {x | q ≤ cdf μ x}
  have hbelow : ∃ a, cdf μ a < q :=
    ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds hq.1)).exists
  have habove : ∃ b, q < cdf μ b :=
    ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds hq.2)).exists
  have hne : S.Nonempty := by obtain ⟨b, hb⟩ := habove; exact ⟨b, hb.le⟩
  have hbdd : BddBelow S := by
    obtain ⟨a, ha⟩ := hbelow
    refine ⟨a, fun x hx => ?_⟩
    by_contra h
    have := (monotone_cdf μ) (le_of_not_ge h)
    exact (not_lt_of_ge (hx.trans this)) ha
  let c := distributionQuantile μ q
  have hleft (x : ℝ) (hx : x < c) : cdf μ x < q := by
    by_contra h
    exact (not_le_of_gt hx) (csInf_le hbdd (show x ∈ S from le_of_not_gt h))
  have hright (x : ℝ) (hx : c < x) : q ≤ cdf μ x := by
    obtain ⟨t, ht, htx⟩ := exists_lt_of_csInf_lt hne hx
    exact ht.trans ((monotone_cdf μ) htx.le)
  have hqc : q ≤ cdf μ c := by
    apply ge_of_tendsto ((cdf μ).right_continuous c |>.mono Ioi_subset_Ici_self)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hright x hx
  have hlim : Function.leftLim (cdf μ) c ≤ q := by
    apply le_of_tendsto ((monotone_cdf μ).tendsto_leftLim c)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hleft x hx).le
  refine ⟨?_, ?_⟩
  · change μ.real (Iio c) ≤ q
    rw [measureReal_def, ← measure_cdf μ,
      StieltjesFunction.measure_Iio _ (tendsto_cdf_atBot μ), sub_zero]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (ENNReal.ofReal_le_ofReal hlim)
    simpa only [ENNReal.toReal_ofReal hq.1.le] using h
  · rwa [← cdf_eq_real]

/-- Exact CDF calibration at a quantile when the distribution has no atoms. -/
theorem distributionQuantile_exact (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) :
    μ.real (Iic (distributionQuantile μ q)) = q := by
  have h := distributionQuantile_bracket μ q hq
  rw [measureReal_congr (Iio_ae_eq_Iic)] at h
  exact le_antisymm h.1 h.2

/-- The boundary atom is the difference between the closed and open tails. -/
theorem lower_tail_atom_mass (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ) :
    μ.real (Iic c) = μ.real (Iio c) + μ.real {c} := by
  have he : Iio c ∪ {c} = Iic c := by ext x; simp [le_iff_lt_or_eq]
  rw [← he, measureReal_union]
  · exact disjoint_left.mpr (by intro x hx he; simp only [mem_singleton_iff] at he; subst x; exact lt_irrefl c (show c < c from hx))
  · exact measurableSet_singleton c

theorem exists_tie_randomization (A B q : ℝ) (hB : 0 ≤ B) (hA : A ≤ q) (hq : q ≤ A + B) :
    ∃ γ ∈ Icc (0 : ℝ) 1, A + γ * B = q := by
  by_cases hz : B = 0
  · refine ⟨0, by norm_num, ?_⟩
    simp only [zero_mul, add_zero]
    linarith
  · have hB' : 0 < B := lt_of_le_of_ne hB (Ne.symm hz)
    refine ⟨(q - A) / B, ⟨div_nonneg (sub_nonneg.mpr hA) hB,
      (div_le_one hB').mpr (by linarith)⟩, ?_⟩
    rw [div_mul_cancel₀ _ hz]
    ring

theorem lowerTailTest_power {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℝ) (hT : Measurable T)
    (c γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1) :
    (lowerTailTest T hT c γ hγ).power P =
      P.real {x | T x < c} + γ * P.real {x | T x = c} := by
  have hA : MeasurableSet {x | T x < c} := measurableSet_lt hT measurable_const
  have hB : MeasurableSet {x | T x = c} := measurableSet_eq_fun hT measurable_const
  have he (x : Ω) : (lowerTailTest T hT c γ hγ).reject x =
      ({x | T x < c}.indicator (fun _ => (1 : ℝ))) x +
      ({x | T x = c}.indicator (fun _ => γ)) x := by
    simp only [lowerTailTest, indicator_apply, mem_setOf_eq]
    split_ifs <;> simp_all
  unfold StatisticalTest.power
  simp_rw [he]
  rw [integral_add ((integrable_const 1).indicator hA) ((integrable_const γ).indicator hB),
    integral_indicator hA, integral_indicator hB]
  simp [mul_comm]

/-- Every measurable real statistic admits a lower-tail randomized test of
any prescribed size strictly between zero and one. No atomlessness assumption. -/
theorem exists_calibrated_lowerTailTest {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℝ) (hT : Measurable T)
    (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) :
    ∃ c γ, ∃ hγ : γ ∈ Icc (0 : ℝ) 1, (lowerTailTest T hT c γ hγ).power P = α := by
  let μ := P.map T
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hT.aemeasurable
  let c := distributionQuantile μ α
  have hb := distributionQuantile_bracket μ α hα
  rw [lower_tail_atom_mass μ c] at hb
  obtain ⟨γ, hγ, he⟩ := exists_tie_randomization (μ.real (Iio c)) (μ.real {c}) α
    (measureReal_nonneg) hb.1 hb.2
  refine ⟨c, γ, hγ, ?_⟩
  rw [lowerTailTest_power]
  convert he using 1 <;> simp only [μ, map_measureReal_apply hT measurableSet_Iio,
    map_measureReal_apply hT (measurableSet_singleton c), preimage, mem_Iio, mem_singleton_iff]

end LectureNotes
