import LectureNotes.FisherNeyman

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- A statistic-dependent density relative to a sigma-finite carrier is enough
for sufficiency. A finite mixture normalizes the carrier by a function of the
statistic, so no integrability of the original carrier is required. -/
theorem sufficient_of_sigmaFinite_reference_factorization {Θ Ω S : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace S] [StandardBorelSpace S]
    {P : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (P θ)]
    (ρ : Measure Ω) [SigmaFinite ρ] {T : Ω → S} (hT : Measurable T)
    (hfact : ∀ θ, ∃ g : S → ℝ≥0∞, Measurable g ∧
      ρ.withDensity (fun x => g (T x)) = P θ) : IsSufficientStatistic P T := by
  classical
  choose g hg hP using hfact
  have hdom (θ : Θ) : P θ ≪ ρ := by
    rw [← hP θ]
    exact withDensity_absolutelyContinuous _ _
  obtain ⟨ι, hcount, parameters, w, μ, hfinite, hmix, _, hdomμ⟩ :=
    exists_dominating_countable_mixture P ρ hdom
  letI : Countable ι := hcount
  letI : IsFiniteMeasure μ := hfinite
  let q (s : S) : ℝ≥0∞ := ∑' i, w i * g (parameters i) s
  have hq : Measurable q := by dsimp only [q]; fun_prop
  have hqμ : ρ.withDensity (fun x => q (T x)) = μ := by
    rw [hmix]
    have he : (fun x => q (T x)) = ∑' i, (fun x => w i * g (parameters i) (T x)) := by
      funext x
      exact (ENNReal.tsum_apply (f := fun i x => w i * g (parameters i) (T x)) (x := x)).symm
    rw [he, withDensity_tsum (f := fun i x => w i * g (parameters i) (T x))
      (fun i => measurable_const.mul ((hg (parameters i)).comp hT))]
    congr 1
    funext i
    change ρ.withDensity (w i • (fun x => g (parameters i) (T x))) = w i • P (parameters i)
    rw [withDensity_smul (w i) (f := fun x => g (parameters i) (T x)) ((hg (parameters i)).comp hT), hP]
  have hqfinite : ∀ᵐ x ∂ρ, q (T x) ≠ ⊤ := by
    have hr := Measure.rnDeriv_withDensity ρ (f := fun x => q (T x)) (hq.comp hT)
    rw [hqμ] at hr
    filter_upwards [hr, Measure.rnDeriv_ne_top μ ρ] with x hx hf
    exact hx ▸ hf
  have hqpositive : ∀ᵐ x ∂μ, q (T x) ≠ 0 := by
    rw [← hqμ, ae_withDensity_iff (f := fun x => q (T x)) (hq.comp hT)]
    exact ae_of_all _ (fun _ h => h)
  apply sufficient_of_reference_factorization μ hT
  intro θ
  refine ⟨fun s => g θ s / q s, (hg θ).div hq, ?_⟩
  have hzero : ∀ᵐ x ∂ρ, g θ (T x) ≠ 0 → q (T x) ≠ 0 := by
    have h : ∀ᵐ x ∂P θ, q (T x) ≠ 0 := (hdomμ θ).ae_le hqpositive
    rw [← hP θ, ae_withDensity_iff (f := fun x => g θ (T x)) ((hg θ).comp hT)] at h
    exact h
  change μ.withDensity (fun x => g θ (T x) / q (T x)) = P θ
  rw [← hqμ, ← withDensity_mul ρ (f := fun x => q (T x)) (g := fun x => g θ (T x) / q (T x))
    (hq.comp hT) (((hg θ).div hq).comp hT), ← hP θ]
  apply withDensity_congr_ae
  filter_upwards [hqfinite, hzero] with x hfin hz
  exact ENNReal.mul_div_cancel' (fun h0 => by
    by_contra hg0
    exact hz hg0 h0) (fun h => (hfin h).elim)

/-- Fisher–Neyman sufficiency in the usual displayed-density form, allowing
an infinite total carrier mass. Finiteness of the carrier density almost
everywhere is the standard sigma-finiteness condition. -/
theorem sufficient_of_density_factorization_sigmaFinite {Θ Ω S : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace S] [StandardBorelSpace S]
    {P : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (P θ)]
    (ν : Measure Ω) [SigmaFinite ν] (f : Θ → Ω → ℝ≥0∞)
    (hP : ∀ θ, ν.withDensity (f θ) = P θ)
    {T : Ω → S} (hT : Measurable T) (h : Ω → ℝ≥0∞) (hh : Measurable h)
    (hfinite : ∀ᵐ x ∂ν, h x ≠ ⊤)
    (hfact : ∀ θ, ∃ g : S → ℝ≥0∞, Measurable g ∧
      f θ =ᵐ[ν] (fun x => h x * g (T x))) : IsSufficientStatistic P T := by
  letI : SigmaFinite (ν.withDensity h) := SigmaFinite.withDensity_of_ne_top hfinite
  apply sufficient_of_sigmaFinite_reference_factorization (ν.withDensity h) hT
  intro θ
  obtain ⟨g, hg, he⟩ := hfact θ
  refine ⟨g, hg, ?_⟩
  rw [← withDensity_mul ν (g := fun x => g (T x)) hh (hg.comp hT)]
  change ν.withDensity (fun x => h x * g (T x)) = P θ
  rw [withDensity_congr_ae he.symm, hP θ]

end LectureNotes
