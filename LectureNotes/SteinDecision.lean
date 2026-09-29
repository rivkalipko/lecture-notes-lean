import LectureNotes.JamesStein

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

def normalMeansSquaredRisk {p : ℕ} (v : ℝ≥0)
    (δ : (Fin p → ℝ) → Fin p → ℝ) (θ : Fin p → ℝ) : ℝ≥0∞ :=
  risk (fun θ => Measure.pi (fun j => gaussianReal (θ j) v))
    (fun a θ => ENNReal.ofReal (∑ i, (a i - θ i) ^ 2)) δ θ

theorem normal_means_loss_integrable {p : ℕ} (θ : Fin p → ℝ) (v : ℝ≥0) :
    Integrable (fun y : Fin p → ℝ => ∑ i, (y i - θ i) ^ 2)
      (Measure.pi (fun j => gaussianReal (θ j) v)) := by
  apply integrable_finsetSum
  intro i _
  have hY : HasLaw (fun y : Fin p → ℝ => y i) (gaussianReal (θ i) v)
      (Measure.pi (fun j => gaussianReal (θ j) v)) :=
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  exact ((((hY.identDistrib HasLaw.id).memLp_iff.mpr (memLp_id_gaussianReal 2)).sub
    (memLp_const (θ i))).integrable_sq)

theorem jamesStein_loss_integrable {p : ℕ} (θ : Fin p → ℝ) (v : ℝ≥0)
    (hv : 0 < v) (hp : 3 ≤ p) :
    Integrable (fun y => ∑ i, (jamesStein v y i - θ i) ^ 2)
      (Measure.pi (fun j => gaussianReal (θ j) v)) := by
  cases p with
  | zero => omega
  | succ n =>
    let a : ℝ := (((n + 1 : ℕ) : ℝ) - 2) * v
    have h := (regularized_stein_loss_limit (Measure.pi (fun j => gaussianReal (θ j) v)) θ a
      (normal_inverse_square_integrable θ v hv hp) (normal_means_loss_integrable θ v)
      (eps := fun _ => 0) (fun _ => le_rfl) tendsto_const_nhds).1
    have he (y : Fin (n + 1) → ℝ) i :
        y i + regularizedSteinCorrection a 0 y i = jamesStein v y i := by
      unfold a regularizedSteinCorrection jamesStein normalSquareNorm
      ring
    simpa only [he] using h

theorem normalMeansSquaredRisk_eq {p : ℕ} (v : ℝ≥0)
    (δ : (Fin p → ℝ) → Fin p → ℝ) (θ : Fin p → ℝ)
    (hi : Integrable (fun y => ∑ i, (δ y i - θ i) ^ 2)
      (Measure.pi (fun j => gaussianReal (θ j) v))) :
    normalMeansSquaredRisk v δ θ = ENNReal.ofReal
      (∫ y, ∑ i, (δ y i - θ i) ^ 2 ∂Measure.pi (fun j => gaussianReal (θ j) v)) := by
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))).symm

theorem normalMeansSquaredRisk_identity {p : ℕ} (v : ℝ≥0) (θ : Fin p → ℝ) :
    normalMeansSquaredRisk v id θ = ENNReal.ofReal (p * (v : ℝ)) := by
  rw [normalMeansSquaredRisk_eq v id θ (normal_means_loss_integrable θ v)]
  congr 1
  exact normal_means_identity_risk (fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩)

theorem jamesStein_extended_risk_strict {p : ℕ} (v : ℝ≥0) (hv : 0 < v)
    (hp : 3 ≤ p) (θ : Fin p → ℝ) :
    normalMeansSquaredRisk v (jamesStein v) θ < normalMeansSquaredRisk v id θ := by
  rw [normalMeansSquaredRisk_eq v (jamesStein v) θ (jamesStein_loss_integrable θ v hv hp),
    normalMeansSquaredRisk_identity]
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  exact (ENNReal.ofReal_lt_ofReal_iff (mul_pos hp' (by exact_mod_cast hv))).mpr
    (jamesStein_strict_improvement θ v hv hp)

theorem jamesStein_dominates_identity {p : ℕ} (v : ℝ≥0) (hv : 0 < v) (hp : 3 ≤ p) :
    Dominates (normalMeansSquaredRisk (p := p) v) (jamesStein v) id :=
  ⟨fun θ => (jamesStein_extended_risk_strict v hv hp θ).le,
    ⟨0, jamesStein_extended_risk_strict v hv hp 0⟩⟩

theorem normal_means_identity_inadmissible {p : ℕ} (v : ℝ≥0) (hv : 0 < v) (hp : 3 ≤ p) :
    ¬ Admissible (normalMeansSquaredRisk (p := p) v) id := by
  intro h
  exact h ⟨jamesStein v, jamesStein_dominates_identity v hv hp⟩

end LectureNotes
