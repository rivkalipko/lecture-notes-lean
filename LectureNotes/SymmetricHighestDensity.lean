import LectureNotes.HighestDensityPlateaus
import LectureNotes.QuantileReparameterization
import LectureNotes.QuantileIntervals
import LectureNotes.GaussianBayesRisk

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- A density symmetric about `m` and nonincreasing with distance from `m`.
Nonstrict monotonicity permits flat regions and compact support. -/
def SymmetricUnimodalDensity (p : ℝ → ℝ) (m : ℝ) : Prop :=
  ∀ x y, |x - m| ≤ |y - m| → p y ≤ p x

/-- Radial monotonicity includes symmetry about the center. -/
theorem SymmetricUnimodalDensity.reflect {p : ℝ → ℝ} {m : ℝ}
    (hu : SymmetricUnimodalDensity p m) (x : ℝ) : p (2 * m - x) = p x := by
  have he : |2 * m - x - m| = |x - m| := by
    rw [show 2 * m - x - m = -(x - m) by ring, abs_neg]
  exact le_antisymm (hu x (2 * m - x) he.ge) (hu (2 * m - x) x he.le)

/-- The actual density measure is invariant under reflection in its center. -/
theorem symmetricUnimodal_density_reflection {p : ℝ → ℝ} {m : ℝ}
    (hp : Measurable p) (hu : SymmetricUnimodalDensity p m) :
    (volume.withDensity (fun x => ENNReal.ofReal (p x))).map (fun x => 2 * m - x) =
      volume.withDensity (fun x => ENNReal.ofReal (p x)) := by
  let e := MeasurableEquiv.subLeft (2 * m)
  change (volume.withDensity (fun x => ENNReal.ofReal (p x))).map e = _
  rw [map_withDensity_equiv volume e _ hp.ennreal_ofReal]
  have he : (volume : Measure ℝ).map e = volume := Measure.map_sub_left_eq_self volume _
  rw [he]
  congr 1
  funext x
  have heinv : e.symm x = 2 * m - x := by
    apply e.injective
    simp only [MeasurableEquiv.apply_symm_apply]
    change x = 2 * m - (2 * m - x)
    ring
  rw [heinv, hu.reflect]

/-- Atomlessness gives the usual CDF difference for a closed interval. -/
theorem atomless_interval_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {a b : ℝ} (hab : a ≤ b) :
    μ.real (Icc a b) = cdf μ b - cdf μ a := by
  rw [← measureReal_congr Ioc_ae_eq_Icc, measureReal_def, ← measure_cdf μ,
    StieltjesFunction.measure_Ioc, measure_cdf,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ((monotone_cdf μ) hab))]

/-- An interval centered at a symmetric unimodal density's mode selects all
strictly larger density values and only values at least its endpoint cutoff. -/
theorem symmetricUnimodal_interval_threshold {p : ℝ → ℝ} {m r : ℝ}
    (hu : SymmetricUnimodalDensity p m) (hr : m ≤ r) :
    {x | p r < p x} ⊆ Icc (2 * m - r) r ∧
      Icc (2 * m - r) r ⊆ {x | p r ≤ p x} := by
  have harr : |r - m| = r - m := abs_of_nonneg (sub_nonneg.mpr hr)
  constructor
  · intro x hx
    by_contra h
    have hd : |r - m| ≤ |x - m| := by
      rw [harr]
      simp only [mem_Icc, not_and_or, not_le] at h
      rcases h with h | h
      · have := neg_le_abs (x - m)
        linarith
      · exact le_trans (by linarith) (le_abs_self (x - m))
    exact not_lt_of_ge (hu r x hd) hx
  · intro x hx
    apply hu x r
    rw [harr, abs_le]
    constructor <;> linarith [hx.1, hx.2]

/-- A proper credible interval under a symmetric unimodal density has a
positive endpoint cutoff, even when the density has plateaus. -/
theorem symmetricUnimodal_interval_cutoff_pos {p : ℝ → ℝ} {m r : ℝ}
    (hi : Integrable p volume) (hn : ∀ x, 0 ≤ p x)
    (hu : SymmetricUnimodalDensity p m) (hr : m ≤ r)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (p x)))]
    (hc : (volume.withDensity (fun x => ENNReal.ofReal (p x))).real
      (Icc (2 * m - r) r) < 1) : 0 < p r := by
  by_contra h
  have hz : p r = 0 := le_antisymm (le_of_not_gt h) (hn r)
  have hzero : (volume.withDensity (fun x => ENNReal.ofReal (p x))).real
      (Icc (2 * m - r) r)ᶜ = 0 := by
    rw [density_event_eq_integral hi hn _ measurableSet_Icc.compl]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have hh : p x ≤ p r := le_of_not_gt (fun hpx =>
      hx ((symmetricUnimodal_interval_threshold hu hr).1 hpx))
    exact le_antisymm (hz ▸ hh) (hn x)
  rw [measureReal_compl measurableSet_Icc, probReal_univ] at hzero
  linarith

/-- Positive left-tail content forces a positive density at every point
between that tail and the mode. -/
theorem symmetricUnimodal_density_pos_of_cdf_pos {p : ℝ → ℝ} {m x : ℝ}
    (hi : Integrable p volume) (hn : ∀ x, 0 ≤ p x)
    (hu : SymmetricUnimodalDensity p m) (hx : x ≤ m)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (p x)))]
    (hc : 0 < cdf (volume.withDensity (fun x => ENNReal.ofReal (p x))) x) :
    0 < p x := by
  by_contra h
  have hz : p x = 0 := le_antisymm (le_of_not_gt h) (hn x)
  have hzero : cdf (volume.withDensity (fun x => ENNReal.ofReal (p x))) x = 0 := by
    rw [cdf_eq_real, density_event_eq_integral hi hn _ measurableSet_Iic]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    have hyx : |x - m| ≤ |y - m| := by
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith [show y ≤ x from hy])]
      linarith [show y ≤ x from hy]
    exact le_antisymm (hz ▸ hu x y hyx) (hn y)
  linarith

/-- The CDF is strictly increasing on the left of the mode wherever the
left-tail probability is positive. This also covers bounded support. -/
theorem symmetricUnimodal_cdf_strict_left {p : ℝ → ℝ} {m x y : ℝ}
    (hi : Integrable p volume) (hn : ∀ x, 0 ≤ p x)
    (hu : SymmetricUnimodalDensity p m) (hxy : x < y) (hym : y ≤ m)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (p x)))]
    (hc : 0 < cdf (volume.withDensity (fun x => ENNReal.ofReal (p x))) x) :
    cdf (volume.withDensity (fun x => ENNReal.ofReal (p x))) x <
      cdf (volume.withDensity (fun x => ENNReal.ofReal (p x))) y := by
  have hpx := symmetricUnimodal_density_pos_of_cdf_pos hi hn hu (hxy.le.trans hym) hc
  have hl : (y - x) * p x ≤ ∫ z in Icc x y, p z := by
    have h := setIntegral_mono_on (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) :
      IntegrableOn (fun _ : ℝ => p x) (Icc x y) volume) hi.integrableOn
      measurableSet_Icc (fun z hz => hu z x (by
        rw [abs_of_nonpos (by linarith [hz.2]), abs_of_nonpos (by linarith)]
        linarith [hz.1]))
    simpa only [integral_const, measureReal_restrict_apply_univ,
      Real.volume_real_Icc_of_le hxy.le, smul_eq_mul] using h
  have hm := atomless_interval_cdf
    (volume.withDensity (fun x => ENNReal.ofReal (p x))) hxy.le
  rw [density_event_eq_integral hi hn _ measurableSet_Icc] at hm
  have hp : 0 < (y - x) * p x := mul_pos (sub_pos.mpr hxy) hpx
  linarith

/-- The equal-tailed quantiles of a symmetric unimodal density are reflected
about its mode. No global strictness of the CDF or positivity of the density
on the whole line is required. -/
theorem symmetricUnimodal_quantile_reflection {p : ℝ → ℝ} {m : ℝ}
    (hp : Measurable p) (hi : Integrable p volume) (hn : ∀ x, 0 ≤ p x)
    (hu : SymmetricUnimodalDensity p m)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (p x)))]
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    distributionQuantile (volume.withDensity (fun x => ENNReal.ofReal (p x))) (α / 2) =
      2 * m - distributionQuantile (volume.withDensity (fun x => ENNReal.ofReal (p x)))
        (1 - α / 2) := by
  let μ := volume.withDensity (fun x => ENNReal.ofReal (p x))
  have hsym : μ.map (fun x => 2 * m - x) = μ := symmetricUnimodal_density_reflection hp hu
  have hF (x : ℝ) : cdf μ (2 * m - x) = 1 - cdf μ x := by
    have h := cdf_map_strictAnti μ (g := fun x => 2 * m - x) (by intro x y hxy; linarith) x
    rwa [hsym] at h
  have hm : cdf μ m = 1 / 2 := by
    have h := hF m
    rw [show 2 * m - m = m by ring] at h
    linarith
  have ha : α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hb : 1 - α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  let l := distributionQuantile μ (α / 2)
  let r := distributionQuantile μ (1 - α / 2)
  have hr : m < r := (lt_distributionQuantile_iff μ hb).mpr (by rw [hm]; linarith [hα.2])
  have hl : cdf μ l = α / 2 := by rw [cdf_eq_real]; exact distributionQuantile_exact μ _ ha
  have hrr : cdf μ r = 1 - α / 2 := by rw [cdf_eq_real]; exact distributionQuantile_exact μ _ hb
  have hleft : cdf μ (2 * m - r) = α / 2 := by rw [hF, hrr]; ring
  have hle : l ≤ 2 * m - r := (distributionQuantile_le_iff μ ha).mpr hleft.ge
  change l = 2 * m - r
  apply le_antisymm hle
  by_contra h
  have hh := symmetricUnimodal_cdf_strict_left hi hn hu (lt_of_not_ge h)
    (show 2 * m - r ≤ m by linarith) (show 0 < cdf μ l by rw [hl]; linarith [hα.1])
  change cdf μ l < cdf μ (2 * m - r) at hh
  rw [hl, hleft] at hh
  exact (lt_irrefl _) hh

/-- For every interior credibility level, a symmetric unimodal density's
usual equal-tailed quantile interval is an HPD region and has minimum
Lebesgue volume among measurable sets of at least that content. Flat density
regions may give other optimizers; uniqueness is not asserted. -/
theorem symmetricUnimodal_equalTailed_highestDensity {p : ℝ → ℝ} {m : ℝ}
    (hp : Measurable p) (hi : Integrable p volume) (hn : ∀ x, 0 ≤ p x)
    (hu : SymmetricUnimodalDensity p m)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (p x)))]
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    let μ := volume.withDensity (fun x => ENNReal.ofReal (p x))
    let l := distributionQuantile μ (α / 2)
    let r := distributionQuantile μ (1 - α / 2)
    μ.real (Iic l) = α / 2 ∧ μ.real (Ioi r) = α / 2 ∧
      μ.real (Icc l r) = 1 - α ∧ 0 < p r ∧
      {x | p r < p x} ⊆ Icc l r ∧ Icc l r ⊆ {x | p r ≤ p x} ∧
      ∀ C : Set ℝ, MeasurableSet C → 1 - α ≤ μ.real C →
        volume (Icc l r) ≤ volume C := by
  let μ := volume.withDensity (fun x => ENNReal.ofReal (p x))
  let l := distributionQuantile μ (α / 2)
  let r := distributionQuantile μ (1 - α / 2)
  have ha : α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hb : 1 - α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hab : α / 2 < 1 - α / 2 := by linarith [hα.2]
  have he : l = 2 * m - r := symmetricUnimodal_quantile_reflection hp hi hn hu hα
  have hr : m < r := by
    have ho : l < r := distributionQuantile_strictMono μ ha hb hab
    rw [he] at ho
    linarith
  have hcal : μ.real (Icc l r) = 1 - α := by
    rw [quantile_interval_probability μ ha hb hab.le]
    ring
  have hk : 0 < p r := symmetricUnimodal_interval_cutoff_pos hi hn hu hr.le (by
    change μ.real (Icc (2 * m - r) r) < 1
    rw [← he, hcal]
    linarith [hα.1])
  have hbr := symmetricUnimodal_interval_threshold hu hr.le
  rw [← he] at hbr
  refine ⟨distributionQuantile_exact μ _ ha, ?_, hcal, hk, hbr.1, hbr.2, ?_⟩
  · rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ,
      distributionQuantile_exact μ _ hb]
    ring
  · intro C hC hc
    apply highest_density_plateau_minimum_volume hi hn hk measurableSet_Icc
      hbr.1 hbr.2 C hC
    change μ.real (Icc l r) ≤ μ.real C
    rwa [hcal]

end LectureNotes
