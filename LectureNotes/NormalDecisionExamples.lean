import LectureNotes.GaussianStein
set_option autoImplicit false

/-! L13 Examples 2–3: admissibility of every constant estimator in a normal
IID experiment, improvement from averaging, and the normal Bayes rule risk. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

theorem constant_estimator_admissible {Ω : Type*} [MeasurableSpace Ω]
    (P : ℝ → Measure Ω) (c : ℝ) (hac : ∀ θ, P θ ≪ P c) :
    Admissible (fun δ : {f : Ω → ℝ // Measurable f} =>
      risk P (fun a θ => ENNReal.ofReal ((a - θ) ^ 2)) δ.val)
      ⟨fun _ => c, measurable_const⟩ := by
  rintro ⟨⟨δ, hδ⟩, hle, θ, hlt⟩
  have hz : (∫⁻ x, ENNReal.ofReal ((δ x - c) ^ 2) ∂P c) = 0 := by
    have h := hle c
    simpa only [risk, sub_self, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero,
      lintegral_zero, nonpos_iff_eq_zero] using h
  have hzero : ∀ᵐ x ∂P c, δ x = c := by
    have hm : Measurable (fun x => ENNReal.ofReal ((δ x - c) ^ 2)) := by fun_prop
    filter_upwards [(lintegral_eq_zero_iff hm).mp hz] with x hx
    change ENNReal.ofReal ((δ x - c) ^ 2) = 0 at hx
    have hs := ENNReal.ofReal_eq_zero.mp hx
    nlinarith [sq_nonneg (δ x - c)]
  have heq : risk P (fun a θ => ENNReal.ofReal ((a - θ) ^ 2)) δ θ =
      risk P (fun a θ => ENNReal.ofReal ((a - θ) ^ 2)) (fun _ => c) θ := by
    apply lintegral_congr_ae
    filter_upwards [(hac θ).ae_eq hzero] with x hx
    rw [hx]
  exact (ne_of_lt hlt) heq

/-- Absolute continuity is preserved by a finite independent product. -/
theorem finite_pi_absolutelyContinuous {n : ℕ}
    (μ ν : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (h : ∀ i, μ i ≪ ν i) : Measure.pi μ ≪ Measure.pi ν := by
  induction n with
  | zero =>
    have he : μ = ν := by ext i; exact Fin.elim0 i
    rw [he]
  | succ n ih =>
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    have hem := (measurePreserving_piFinSuccAbove μ 0).symm _
    have hen := (measurePreserving_piFinSuccAbove ν 0).symm _
    have hp := (h 0).prod (ih (fun j => μ (Fin.succAbove 0 j))
      (fun j => ν (Fin.succAbove 0 j)) (fun j => h (Fin.succAbove 0 j)))
    have hm := e.measurableEmbedding.absolutelyContinuous_map hp
    rwa [hem.map_eq, hen.map_eq] at hm

theorem normal_iid_constant_admissible (n : ℕ) (v : ℝ≥0) (hv : 0 < v) (c : ℝ) :
    Admissible (fun δ : {f : (Fin n → ℝ) → ℝ // Measurable f} =>
      risk (fun θ => Measure.pi (fun _ : Fin n => gaussianReal θ v))
        (fun a θ => ENNReal.ofReal ((a - θ) ^ 2)) δ.val)
      ⟨fun _ => c, measurable_const⟩ := by
  apply constant_estimator_admissible
  intro θ
  apply finite_pi_absolutelyContinuous
  intro i
  exact (gaussianReal_absolutelyContinuous θ hv.ne').trans
    (gaussianReal_absolutelyContinuous' c hv.ne')


theorem normal_sampleMean_squared_risk {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {θ : ℝ} {v : ℝ≥0}
    (hX : ∀ i, HasLaw (X i) (gaussianReal θ v) P) (hind : iIndepFun X P) :
    mse P (fun ω => sampleMean (fun i => X i ω)) θ = (v : ℝ) / n := by
  simpa using affine_normal_risk (normal_sampleMean hn hX hind) 0 1

theorem normal_sampleMean_strict_improvement {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 1 < n)
    {X : Fin n → Ω → ℝ} {θ : ℝ} {v : ℝ≥0} (hv : 0 < v)
    (hX : ∀ i, HasLaw (X i) (gaussianReal θ v) P) (hind : iIndepFun X P) (i : Fin n) :
    mse P (fun ω => sampleMean (fun j => X j ω)) θ < mse P (X i) θ := by
  rw [normal_sampleMean_squared_risk (by omega) hX hind]
  have hr : mse P (X i) θ = (v : ℝ) := by simpa using affine_normal_risk (hX i) 0 1
  rw [hr, div_lt_iff₀ (by exact_mod_cast (show 0 < n by omega))]
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  nlinarith

/-- The displayed risk of the normal-normal Bayes estimator in L13 Example 3. -/
theorem normal_bayes_estimator_risk {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {θ : ℝ}
    (hX : ∀ i, HasLaw (X i) (gaussianReal θ 1) P) (hind : iIndepFun X P)
    (precision τ : ℝ) (hprecision : 0 < precision) :
    mse P (fun ω => precision / (precision + n) * τ +
      (n : ℝ) / (precision + n) * sampleMean (fun i => X i ω)) θ =
      (1 / (n : ℝ)) * ((n : ℝ) / (precision + n)) ^ 2 +
        (precision / (precision + n)) ^ 2 * (τ - θ) ^ 2 := by
  rw [affine_normal_risk (normal_sampleMean hn hX hind)]
  simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast]
  have hd : precision + (n : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

end LectureNotes
