import LectureNotes.GaussianBayesRisk

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

/-- No measurable estimator in the normal means model has worst-case risk
below `p v`. The proof takes increasingly diffuse proper normal priors. -/
theorem normal_means_minimax_lower_bound {p : ℕ} (v : ℝ≥0) (hv : 0 < v)
    (δ : (Fin p → ℝ) → Fin p → ℝ) (hδ : Measurable δ) :
    ENNReal.ofReal (p * (v : ℝ)) ≤ worstRisk (normalMeansSquaredRisk v) δ := by
  have hbound (n : ℕ) :
      ENNReal.ofReal (p * (v : ℝ) * (1 - 1 / ((n : ℝ) + 1 + 1))) ≤
        worstRisk (normalMeansSquaredRisk v) δ := by
    let w : ℝ≥0 := v * (n + 1)
    have hw : 0 < w := by dsimp [w]; positivity
    have he : p * ((v : ℝ) * w / (v + w)) =
        p * (v : ℝ) * (1 - 1 / ((n : ℝ) + 1 + 1)) := by
      have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
      dsimp [w]
      simp only [NNReal.coe_natCast]
      field_simp
      ring
    rw [← he]
    refine (normal_bayes_risk_lower_bound v w hv hw δ hδ).trans ?_
    calc
      _ ≤ ∫⁻ _θ : Fin p → ℝ, worstRisk (normalMeansSquaredRisk v) δ
          ∂Measure.pi (fun _ => gaussianReal 0 w) :=
        lintegral_mono (fun θ => le_iSup (fun θ => normalMeansSquaredRisk v δ θ) θ)
      _ = _ := by simp
  have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1 + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun n : ℕ => p * (v : ℝ) * (1 - 1 / ((n : ℝ) + 1 + 1)))
      atTop (𝓝 (p * (v : ℝ))) := by
    have hc : Tendsto (fun _ : ℕ => p * (v : ℝ)) atTop (𝓝 (p * (v : ℝ))) := tendsto_const_nhds
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using hc.mul (hone.sub hzero)
  exact le_of_tendsto (ENNReal.tendsto_ofReal hlim) (Eventually.of_forall hbound)

/-- The decision space consists of all measurable estimators, with no
integrability, boundedness, linearity, or equivariance restriction. -/
abbrev NormalMeansRule (p : ℕ) :=
  {δ : (Fin p → ℝ) → Fin p → ℝ // Measurable δ}

theorem normal_means_identity_minimax {p : ℕ} (v : ℝ≥0) (hv : 0 < v) :
    IsMinimax (fun (δ : NormalMeansRule p) => normalMeansSquaredRisk v δ.1)
      ⟨id, measurable_id⟩ := by
  intro δ
  simp only [worstRisk, normalMeansSquaredRisk_identity, iSup_const]
  exact normal_means_minimax_lower_bound v hv δ.1 δ.2

theorem jamesStein_minimax {p : ℕ} (v : ℝ≥0) (hv : 0 < v) (hp : 3 ≤ p) :
    IsMinimax (fun (δ : NormalMeansRule p) => normalMeansSquaredRisk v δ.1)
      ⟨jamesStein v, jamesStein_measurable v⟩ := by
  apply minimax_of_pointwise_le (normal_means_identity_minimax v hv)
  intro θ
  exact (jamesStein_extended_risk_strict v hv hp θ).le

/-- A measurable rule bounded by the constant identity risk attains the exact
minimax value, although its pointwise risks may all be strictly smaller. -/
theorem normal_worstRisk_eq_of_le_identity {p : ℕ} (v : ℝ≥0) (hv : 0 < v)
    (δ : (Fin p → ℝ) → Fin p → ℝ) (hδ : Measurable δ)
    (hle : ∀ θ, normalMeansSquaredRisk v δ θ ≤ normalMeansSquaredRisk v id θ) :
    worstRisk (normalMeansSquaredRisk v) δ = ENNReal.ofReal (p * (v : ℝ)) := by
  apply le_antisymm
  · apply iSup_le
    intro θ
    simpa only [normalMeansSquaredRisk_identity] using hle θ
  · exact normal_means_minimax_lower_bound v hv δ hδ

theorem jamesStein_worstRisk {p : ℕ} (v : ℝ≥0) (hv : 0 < v) (hp : 3 ≤ p) :
    worstRisk (normalMeansSquaredRisk v) (jamesStein (p := p) v) =
      ENNReal.ofReal (p * (v : ℝ)) :=
  normal_worstRisk_eq_of_le_identity v hv _ (jamesStein_measurable v)
    (fun θ => (jamesStein_extended_risk_strict v hv hp θ).le)

end LectureNotes
