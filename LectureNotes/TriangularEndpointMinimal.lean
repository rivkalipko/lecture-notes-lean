import LectureNotes.TriangularSufficiency

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Strict rational upper cuts recover a positive real number. -/
theorem positiveRationalCutDecode_recover_strict {m : ℝ} (hm : 0 < m)
    (r : {q : ℚ // 0 < q} → ℝ≥0∞)
    (hr : ∀ q, r q ≠ 0 ↔ m < (q.1 : ℝ)) : positiveRationalCutDecode r = m := by
  have he : (⨅ q : {q : ℚ // 0 < q}, if r q ≠ 0 then ((q.1 : ℝ) : EReal) else ⊤) = (m : EReal) := by
    apply le_antisymm
    · by_contra hh
      obtain ⟨q, hmq, hq⟩ := EReal.exists_rat_btwn_of_lt (lt_of_not_ge hh)
      have hmqR : m < (q : ℝ) := by exact_mod_cast hmq
      have hqpos : (0 : ℚ) < q := by exact_mod_cast hm.trans hmqR
      have hcut : r ⟨q, hqpos⟩ ≠ 0 := (hr ⟨q, hqpos⟩).mpr hmqR
      have hle := iInf_le (fun q : {q : ℚ // 0 < q} =>
        if r q ≠ 0 then ((q.1 : ℝ) : EReal) else ⊤) ⟨q, hqpos⟩
      change (⨅ q : {q : ℚ // 0 < q}, if r q ≠ 0 then ((q.1 : ℝ) : EReal) else ⊤) ≤
        (if r ⟨q, hqpos⟩ ≠ 0 then ((q : ℝ) : EReal) else ⊤) at hle
      rw [if_pos hcut] at hle
      exact (not_lt_of_ge hle) hq
    · apply le_iInf
      intro q
      split_ifs with hq
      · exact_mod_cast ((hr q).mp hq).le
      · exact le_top
  unfold positiveRationalCutDecode
  rw [he, EReal.toReal_coe]


/-- L5 Example 16: the sample maximum is minimal sufficient for the triangular
endpoint family with density 2x/θ² on the strict interval (0,θ). -/
theorem triangularEndpoint_maximum_minimal_sufficient {n : ℕ} (hn : 0 < n) :
    IsMinimalSufficientStatistic (triangularEndpointExperiment n)
      (sampleMaximum : (Fin n → ℝ) → ℝ) := by
  classical
  let ν : Measure (Fin n → ℝ) := Measure.pi (fun _ => (volume : Measure ℝ))
  let f (θ : {θ : ℝ // 0 < θ}) (x : Fin n → ℝ) :=
    ∏ i, ENNReal.ofReal (triangularEndpointDensity θ.1 (x i))
  letI (θ : {θ : ℝ // 0 < θ}) : IsProbabilityMeasure (triangularEndpointLaw θ.1) :=
    triangularEndpointLaw_probability θ.2
  have hd (θ : {θ : ℝ // 0 < θ}) : Measurable
      (fun x => ENNReal.ofReal (triangularEndpointDensity θ.1 x)) :=
    (triangularEndpointDensity_measurable θ.1).ennreal_ofReal
  have hf (θ : {θ : ℝ // 0 < θ}) : Measurable (f θ) := by
    dsimp only [f]
    exact Finset.measurable_prod _ (fun i _ => (hd θ).comp (measurable_pi_apply i))
  have hP (θ : {θ : ℝ // 0 < θ}) : ν.withDensity (f θ) = triangularEndpointExperiment n θ := by
    exact (iid_product_withDensity volume (triangularEndpointLaw θ.1)
      (fun x => ENNReal.ofReal (triangularEndpointDensity θ.1 x)) (hd θ) rfl n).symm
  have hdomν (θ : {θ : ℝ // 0 < θ}) : triangularEndpointExperiment n θ ≪ ν := by
    rw [← hP θ]
    exact withDensity_absolutelyContinuous _ _
  obtain ⟨ι, hcount, mixtureParameters, w, μ, hfinite, hmix, hμν, hdomμ⟩ :=
    exists_dominating_countable_mixture (triangularEndpointExperiment n) ν hdomν
  letI : Countable ι := hcount
  letI : IsFiniteMeasure μ := hfinite
  let parameters (q : {q : ℚ // 0 < q}) : {θ : ℝ // 0 < θ} :=
    ⟨q.1, by exact_mod_cast q.2⟩
  apply minimal_sufficient_of_mixture_ratio_recovery (triangularEndpointExperiment n)
    (triangularEndpoint_maximum_sufficient hn) μ mixtureParameters w hmix hdomμ
    parameters positiveRationalCutDecode positiveRationalCutDecode_measurable
  have hsuppθ (θ : {θ : ℝ // 0 < θ}) :
      ∀ᵐ x ∂triangularEndpointExperiment n θ, ∀ i, 0 < x i := by
    apply ae_all_iff.mpr
    intro i
    have hlaw : HasLaw (fun x : Fin n → ℝ => x i) (triangularEndpointLaw θ.1)
        (triangularEndpointExperiment n θ) :=
      (measurePreserving_eval (μ := fun _ : Fin n => triangularEndpointLaw θ.1) i).hasLaw
    have hs := (hlaw.ae_iff (show Measurable (fun x : ℝ => x ∈ Ioo 0 θ.1) by measurability)).mpr
      (triangularEndpoint_ae_support θ.1)
    exact hs.mono (fun x hx => hx.1)
  have hsupp : ∀ᵐ x ∂μ, ∀ i, 0 < x i := by
    rw [hmix]
    exact ae_mixture_of_ae_models (triangularEndpointExperiment n) mixtureParameters w hsuppθ
  have hratio : ∀ᵐ x ∂μ, ∀ q : {q : ℚ // 0 < q},
      (triangularEndpointExperiment n (parameters q)).rnDeriv μ x ≠ 0 ↔ f (parameters q) x ≠ 0 :=
    ae_all_iff.mpr (fun q => rnDeriv_nonzero_iff_density
      (triangularEndpointExperiment n (parameters q)) μ ν hμν (hdomμ (parameters q))
      (hf (parameters q)) (hP (parameters q)))
  filter_upwards [hsupp, hratio] with x hx hr
  apply positiveRationalCutDecode_recover_strict
    ((hx ⟨0, hn⟩).trans_le (le_sampleMaximum x ⟨0, hn⟩))
  intro q
  rw [hr q]
  dsimp only [f, parameters]
  rw [triangularEndpoint_product_factorization hn (q.1 : ℝ) (by exact_mod_cast q.2), if_pos hx]
  have hc : ENNReal.ofReal ((1 / (q.1 : ℝ) ^ 2) ^ n) ≠ 0 := by
    apply (ENNReal.ofReal_pos.mpr _).ne'
    have hq : (0 : ℝ) < q.1 := by exact_mod_cast q.2
    positivity
  have hp : (∏ i, ENNReal.ofReal (2 * x i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) (hx i))).ne'
  by_cases hq : sampleMaximum x < (q.1 : ℝ)
  · rw [if_pos hq]
    exact iff_of_true (mul_ne_zero hp hc) hq
  · simp [hq]

end LectureNotes
