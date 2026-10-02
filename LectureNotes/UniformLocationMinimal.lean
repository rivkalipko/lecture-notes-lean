import LectureNotes.UniformSufficiency
import LectureNotes.RationalIntervalDecode

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- A translated uniform observation lies strictly inside its interval almost
surely; the chosen closed-endpoint density differs only on null boundaries. -/
theorem uniformLocation_ae_interior (θ : ℝ) :
    ∀ᵐ x ∂uniformLocationLaw θ, x ∈ Ioo θ (θ + 1) := by
  have hs : ∀ᵐ x ∂uniformLocationLaw θ, x ∈ Icc θ (θ + 1) :=
    ae_restrict_mem measurableSet_Icc
  have he : ∀ᵐ x ∂uniformLocationLaw θ, (x ∈ Ioo θ (θ + 1)) = (x ∈ Icc θ (θ + 1)) :=
    ae_restrict_of_ae (Ioo_ae_eq_Icc (μ := volume) (a := θ) (b := θ + 1))
  filter_upwards [hs, he] with x hx he
  exact Eq.mpr he hx

/-- A finite nonempty translated-uniform sample has range strictly less than
one almost surely. This supplies the positive-length interval required for
rational-parameter likelihoods to recover both extreme observations. -/
theorem uniformLocation_range_lt_one_ae {n : ℕ} (hn : 0 < n) (θ : ℝ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => uniformLocationLaw θ),
      sampleMaximum x - 1 < sampleMinimum x := by
  have : NeZero n := ⟨hn.ne'⟩
  have hs : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => uniformLocationLaw θ),
      ∀ i, x i ∈ Ioo θ (θ + 1) := ae_all_iff.mpr (fun i =>
    ((measurePreserving_eval (μ := fun _ : Fin n => uniformLocationLaw θ) i).hasLaw.ae_iff
      (show Measurable (fun x : ℝ => x ∈ Ioo θ (θ + 1)) by measurability)).mpr
      (uniformLocation_ae_interior θ))
  filter_upwards [hs] with x hx
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := x)
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := x)
  change x i = sampleMaximum x at hi
  change x j = sampleMinimum x at hj
  have hmax : sampleMaximum x < θ + 1 := by rw [← hi]; exact (hx i).2
  have hmin : θ < sampleMinimum x := by rw [← hj]; exact (hx j).1
  linarith

/-- The minimum–maximum pair is minimal sufficient for the full translated
unit-interval experiment (L5). The proof handles parameter-dependent zeros
using countably many rational likelihoods and an explicit measurable decoder. -/
theorem uniformLocation_extremes_minimal_sufficient {n : ℕ} (hn : 0 < n) :
    IsMinimalSufficientStatistic (fun θ : ℝ => Measure.pi (fun _ : Fin n => uniformLocationLaw θ))
      (fun x : Fin n → ℝ => (sampleMinimum x, sampleMaximum x)) := by
  classical
  let P (θ : ℝ) : Measure (Fin n → ℝ) := Measure.pi (fun _ => uniformLocationLaw θ)
  let ν : Measure (Fin n → ℝ) := Measure.pi (fun _ => (volume : Measure ℝ))
  let f (θ : ℝ) (x : Fin n → ℝ) := ∏ i, (Icc θ (θ + 1)).indicator (1 : ℝ → ℝ≥0∞) (x i)
  have hf (θ : ℝ) : Measurable (f θ) := by
    dsimp only [f]
    exact Finset.measurable_prod _ (fun i _ =>
      (measurable_one.indicator measurableSet_Icc).comp (measurable_pi_apply i))
  have hbase (θ : ℝ) : volume.withDensity ((Icc θ (θ + 1)).indicator (1 : ℝ → ℝ≥0∞)) =
      uniformLocationLaw θ := by
    rw [withDensity_indicator measurableSet_Icc, withDensity_one]
    rfl
  have hP (θ : ℝ) : ν.withDensity (f θ) = P θ :=
    (iid_product_withDensity volume (uniformLocationLaw θ)
      ((Icc θ (θ + 1)).indicator (1 : ℝ → ℝ≥0∞))
      (measurable_one.indicator measurableSet_Icc) (hbase θ) n).symm
  have hdomν (θ : ℝ) : P θ ≪ ν := by rw [← hP θ]; exact withDensity_absolutelyContinuous _ _
  obtain ⟨ι, hcount, mixtureParameters, w, μ, hfinite, hmix, hμν, hdomμ⟩ :=
    exists_dominating_countable_mixture P ν hdomν
  letI : Countable ι := hcount
  letI : IsFiniteMeasure μ := hfinite
  let decode (r : ℚ → ℝ≥0∞) : ℝ × ℝ := ((rationalIntervalDecode r).2, (rationalIntervalDecode r).1 + 1)
  have hd : Measurable decode := by
    exact rationalIntervalDecode_measurable.snd.prodMk
      (rationalIntervalDecode_measurable.fst.add_const 1)
  apply minimal_sufficient_of_mixture_ratio_recovery P
    (uniformLocation_extremes_sufficient hn) μ mixtureParameters w hmix hdomμ
    (fun q : ℚ => (q : ℝ)) decode hd
  have hwidth : ∀ᵐ x ∂μ, sampleMaximum x - 1 < sampleMinimum x := by
    rw [hmix]
    exact ae_mixture_of_ae_models P mixtureParameters w (uniformLocation_range_lt_one_ae hn)
  have hratio : ∀ᵐ x ∂μ, ∀ q : ℚ, (P (q : ℝ)).rnDeriv μ x ≠ 0 ↔ f (q : ℝ) x ≠ 0 :=
    ae_all_iff.mpr (fun q => rnDeriv_nonzero_iff_density (P (q : ℝ)) μ ν hμν (hdomμ _)
      (hf _) (hP _))
  filter_upwards [hwidth, hratio] with x hx hr
  have hdecode := rationalIntervalDecode_recover hx (fun q : ℚ => (P (q : ℝ)).rnDeriv μ x) (by
    intro q
    rw [hr q]
    dsimp only [f]
    rw [uniformLocation_product_factorization hn]
    by_cases hh : (q : ℝ) ≤ sampleMinimum x ∧ sampleMaximum x ≤ (q : ℝ) + 1
    · simp only [if_pos hh, ne_eq, one_ne_zero, not_false_eq_true, true_iff]
      constructor <;> linarith [hh.1, hh.2]
    · simp only [if_neg hh, ne_eq, not_true_eq_false, false_iff]
      intro hh'
      apply hh
      constructor <;> linarith [hh'.1, hh'.2])
  dsimp only [decode]
  rw [hdecode]
  simp

end LectureNotes
