import LectureNotes.Quantiles

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set

/-- Every nonconstant lower-tail rule has a likelihood threshold under MLR,
even when its cutoff is not attained by the statistic. -/
theorem mlr_cutoff_threshold {Ω Θ : Type*} [MeasurableSpace Ω] [Preorder Θ]
    (ν : Measure Ω) (f : Θ → Ω → ℝ) (T : Ω → ℝ) (hT : Measurable T)
    (hpos : ∀ θ x, 0 < f θ x) (hmlr : HasMonotoneLikelihoodRatio f T)
    {θ₁ θ₂ : Θ} (hθ : θ₁ ≤ θ₂) (c γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1)
    (hlo : ∃ x, 0 < (lowerTailTest T hT c γ hγ).reject x)
    (hhi : ∃ x, (lowerTailTest T hT c γ hγ).reject x < 1) :
    ∃ k, 0 ≤ k ∧ (lowerTailTest T hT c γ hγ).HasLikelihoodThreshold ν (f θ₂) (f θ₁) k := by
  classical
  by_cases hc : ∃ z, T z = c
  · obtain ⟨z, rfl⟩ := hc
    exact ⟨f θ₁ z / f θ₂ z, div_nonneg (hpos θ₁ z).le (hpos θ₂ z).le,
      mlr_lower_tail_threshold f T hT hpos hmlr hθ z γ hγ⟩
  have hne (x) : T x ≠ c := fun h => hc ⟨x, h⟩
  obtain ⟨lo, hlo⟩ := hlo
  obtain ⟨hi, hhi⟩ := hhi
  have hloc : T lo < c := by
    by_contra h
    simp [lowerTailTest, h, hne] at hlo
  have hhic : c < T hi := by
    by_contra h
    have hh : T hi < c := lt_of_le_of_ne (le_of_not_gt h) (hne hi)
    simp [lowerTailTest, hh] at hhi
  let r := fun x => f θ₁ x / f θ₂ x
  have hr (x y) (h : T x ≤ T y) : r y ≤ r x := by
    apply (div_le_div_iff₀ (hpos θ₂ y) (hpos θ₂ x)).mpr
    have hm := hmlr θ₁ θ₂ hθ x y h
    nlinarith
  let A : Set ℝ := r '' {x | c < T x}
  have hA : A.Nonempty := ⟨r hi, hi, hhic, rfl⟩
  have hbdd : BddAbove A := ⟨r lo, by
    rintro a ⟨x, hx, rfl⟩
    exact hr lo x (hloc.trans hx).le⟩
  have hk : 0 ≤ sSup A := (div_nonneg (hpos θ₁ hi).le (hpos θ₂ hi).le).trans
    (le_csSup hbdd ⟨hi, hhic, rfl⟩)
  refine ⟨sSup A, hk, ae_of_all _ (fun x => ?_)⟩
  constructor
  · intro hx
    have hx' : sSup A < r x := (lt_div_iff₀ (hpos θ₂ x)).mpr hx
    have ht : T x < c := by
      by_contra h
      have hg : c < T x := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (hne x))
      exact (not_lt_of_ge (le_csSup hbdd ⟨x, hg, rfl⟩)) hx'
    simp [lowerTailTest, ht]
  · intro hx
    have hx' : r x < sSup A := (div_lt_iff₀ (hpos θ₂ x)).mpr hx
    have ht : c < T x := by
      by_contra h
      have hl : T x < c := lt_of_le_of_ne (le_of_not_gt h) (hne x)
      have hb : sSup A ≤ r x := csSup_le hA (by
        rintro a ⟨y, hy, rfl⟩
        exact hr x y (hl.trans hy).le)
      exact (not_lt_of_ge hb) hx'
    simp [lowerTailTest, not_lt.mpr ht.le, ne_of_gt ht]

/-- Calibration at an interior size supplies sample points with nonzero
rejection and nonzero acceptance probabilities. -/
theorem calibrated_test_nontrivial {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (φ : StatisticalTest Ω)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hcal : φ.power P = α) :
    (∃ x, 0 < φ.reject x) ∧ ∃ x, φ.reject x < 1 := by
  constructor
  · by_contra h
    push_neg at h
    have he : φ.reject = fun _ => 0 := funext (fun x => le_antisymm (h x) (φ.nonneg x))
    simp [StatisticalTest.power, he] at hcal
    linarith [hα.1]
  · by_contra h
    push_neg at h
    have he : φ.reject = fun _ => 1 := funext (fun x => le_antisymm (φ.le_one x) (h x))
    simp [StatisticalTest.power, he] at hcal
    linarith [hα.2]

/-- L9's composite-null MLR theorem, including existence and calibration of
the cutoff. The statistic may be discrete, continuous, or have mixed law. -/
theorem exists_mlr_ump {Ω Θ : Type*} [MeasurableSpace Ω] [LinearOrder Θ]
    (ν : Measure Ω) (f : Θ → Ω → ℝ) (T : Ω → ℝ) (hT : Measurable T)
    (hm : ∀ θ, Measurable (f θ)) (hi : ∀ θ, Integrable (f θ) ν)
    (hpos : ∀ θ x, 0 < f θ x) (hnorm : ∀ θ, (∫ x, f θ x ∂ν) = 1)
    (hmlr : HasMonotoneLikelihoodRatio f T) (θ₀ : Θ) (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) :
    ∃ c γ, ∃ hγ : γ ∈ Icc (0 : ℝ) 1,
      let φ := lowerTailTest T hT c γ hγ
      φ.densityPower ν (f θ₀) = α ∧
      φ.IsUMP (fun θ => ν.withDensity (fun x => ENNReal.ofReal (f θ x))) (Ici θ₀) (Iio θ₀) α := by
  let P := fun θ => ν.withDensity (fun x => ENNReal.ofReal (f θ x))
  letI (θ : Θ) : IsProbabilityMeasure (P θ) :=
    density_model_isProbabilityMeasure (hi θ) (ae_of_all _ (fun x => (hpos θ x).le)) (hnorm θ)
  obtain ⟨c, γ, hγ, hcal⟩ := exists_calibrated_lowerTailTest (P θ₀) T hT α hα
  let φ := lowerTailTest T hT c γ hγ
  have hnt := calibrated_test_nontrivial (P θ₀) φ hα hcal
  have bridge (ψ : StatisticalTest Ω) θ : ψ.densityPower ν (f θ) = ψ.power (P θ) :=
    ψ.densityPower_eq_power (hm θ).aemeasurable (ae_of_all _ (fun x => (hpos θ x).le))
  have hsize : φ.densityPower ν (f θ₀) = α := (bridge φ θ₀).trans hcal
  refine ⟨c, γ, hγ, hsize, ?_, ?_⟩
  · intro θ hθ
    obtain ⟨k, hk, hth⟩ := mlr_cutoff_threshold ν f T hT hpos hmlr hθ c γ hγ hnt.1 hnt.2
    rw [← bridge φ θ]
    apply le_trans (threshold_power_ge_size φ (hi θ) (hi θ₀)
      (fun x => (hpos θ x).le) (fun x => (hpos θ₀ x).le) (hnorm θ) (hnorm θ₀) hk hth)
    exact hsize.le
  · intro ψ hψ θ hθ
    obtain ⟨k, hk, hth⟩ := mlr_cutoff_threshold ν f T hT hpos hmlr hθ.le c γ hγ hnt.1 hnt.2
    rw [← bridge ψ θ, ← bridge φ θ]
    apply φ.neyman_pearson ψ (hi θ₀) (hi θ) hk hth
    rw [hsize, bridge ψ θ₀]
    exact hψ θ₀ (mem_Ici.mpr le_rfl)

/-- The additional power-monotonicity assertion in L9. A weak MLR condition
implies nonincreasing power, not strict decrease. -/
theorem mlr_calibrated_power_antitone {Ω Θ : Type*} [MeasurableSpace Ω] [Preorder Θ]
    (ν : Measure Ω) (f : Θ → Ω → ℝ) (T : Ω → ℝ) (hT : Measurable T)
    (hi : ∀ θ, Integrable (f θ) ν) (hpos : ∀ θ x, 0 < f θ x)
    (hnorm : ∀ θ, (∫ x, f θ x ∂ν) = 1)
    (hmlr : HasMonotoneLikelihoodRatio f T) (c γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1)
    (P : Measure Ω) [IsProbabilityMeasure P] {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hcal : (lowerTailTest T hT c γ hγ).power P = α) :
    Antitone (fun θ => (lowerTailTest T hT c γ hγ).densityPower ν (f θ)) := by
  have hnt := calibrated_test_nontrivial P _ hα hcal
  intro θ₁ θ₂ hθ
  obtain ⟨k, hk, hth⟩ := mlr_cutoff_threshold ν f T hT hpos hmlr hθ c γ hγ hnt.1 hnt.2
  exact threshold_power_ge_size _ (hi θ₂) (hi θ₁) (fun x => (hpos θ₂ x).le)
    (fun x => (hpos θ₁ x).le) (hnorm θ₂) (hnorm θ₁) hk hth

end LectureNotes
