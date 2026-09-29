import LectureNotes.GaussianStein

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

/-- Coordinate integration by parts under the actual independent normal law.
The derivative is with respect to the selected coordinate with the others fixed. -/
theorem normal_coordinate_stein {n : ℕ} (θ : Fin (n + 1) → ℝ)
    (v : ℝ≥0) (hv : v ≠ 0) (i : Fin (n + 1))
    {g g' : (Fin (n + 1) → ℝ) → ℝ}
    (hgm : Measurable g) (hg'm : Measurable g')
    (hd : ∀ z : Fin n → ℝ, ∀ x : ℝ,
      HasDerivAt (fun t => g (i.insertNth t z)) (g' (i.insertNth x z)) x)
    {C C' : ℝ} (hg : ∀ y, |g y| ≤ C) (hg' : ∀ y, |g' y| ≤ C') :
    (∫ y, (y i - θ i) * g y ∂Measure.pi (fun j => gaussianReal (θ j) v)) =
      (v : ℝ) * ∫ y, g' y ∂Measure.pi (fun j => gaussianReal (θ j) v) := by
  let P := Measure.pi (fun j => gaussianReal (θ j) v)
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hem : MeasurePreserving e
      ((gaussianReal (θ i) v).prod (Measure.pi (fun j => gaussianReal (θ (i.succAbove j)) v))) P :=
    (measurePreserving_piFinSuccAbove (fun j => gaussianReal (θ j) v) i).symm _
  have hxi : Integrable (fun y : Fin (n + 1) → ℝ => y i - θ i) P := by
    have hi : Integrable (fun x : ℝ => x - θ i) (gaussianReal (θ i) v) :=
      ((memLp_id_gaussianReal 2).integrable (by norm_num)).sub (integrable_const (θ i))
    exact (measurePreserving_eval (fun j => gaussianReal (θ j) v) i).integrable_comp_of_integrable hi
  have hleft : Integrable (fun y => (y i - θ i) * g y) P :=
    hxi.mul_bdd hgm.aestronglyMeasurable
      (ae_of_all _ (by simpa only [Real.norm_eq_abs] using hg))
  have hright : Integrable g' P :=
    (integrable_const C').mono' hg'm.aestronglyMeasurable
      (ae_of_all _ (by simpa only [Real.norm_eq_abs] using hg'))
  rw [← hem.integral_comp' (fun y => (y i - θ i) * g y), ← hem.integral_comp' g']
  have hlc : Integrable (fun z => (e z i - θ i) * g (e z))
      ((gaussianReal (θ i) v).prod (Measure.pi (fun j => gaussianReal (θ (i.succAbove j)) v))) := by
    simpa only [Function.comp_apply] using! hem.integrable_comp_of_integrable hleft
  have hrc : Integrable (fun z => g' (e z))
      ((gaussianReal (θ i) v).prod (Measure.pi (fun j => gaussianReal (θ (i.succAbove j)) v))) := by
    simpa only [Function.comp_apply] using! hem.integrable_comp_of_integrable hright
  rw [integral_prod_symm _ hlc, integral_prod_symm _ hrc, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  have he (x : ℝ) : e (x, z) = i.insertNth x z := rfl
  simp_rw [he, Fin.insertNth_apply_same]
  apply gaussian_stein_identity_bounded hv (hd z)
  · exact hg'm.comp (e.measurable.comp (measurable_id.prodMk measurable_const))
  · exact fun x => hg (i.insertNth x z)
  · exact fun x => hg' (i.insertNth x z)

/-- Stein's unbiased risk formula for bounded smooth corrections. All risks
are actual integrals, and square integrability is proved from Gaussian moments. -/
theorem normal_stein_risk {n : ℕ} (θ : Fin (n + 1) → ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (g dg : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hgm : Measurable g) (hdgm : Measurable dg)
    (hd : ∀ i, ∀ z : Fin n → ℝ, ∀ x : ℝ,
      HasDerivAt (fun t => g (i.insertNth t z) i) (dg (i.insertNth x z) i) x)
    {C C' : ℝ} (hg : ∀ y i, |g y i| ≤ C) (hdg : ∀ y i, |dg y i| ≤ C') :
    (∫ y, ∑ i, (y i + g y i - θ i) ^ 2 ∂Measure.pi (fun j => gaussianReal (θ j) v)) =
      (n + 1 : ℕ) * (v : ℝ) +
        ∫ y, ∑ i, (g y i ^ 2 + 2 * v * dg y i) ∂Measure.pi (fun j => gaussianReal (θ j) v) := by
  let P := Measure.pi (fun j => gaussianReal (θ j) v)
  have hY i : HasLaw (fun y : Fin (n + 1) → ℝ => y i) (gaussianReal (θ i) v) P :=
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  have hY₂ i : MemLp (fun y : Fin (n + 1) → ℝ => y i - θ i) 2 P :=
    (((hY i).identDistrib HasLaw.id).memLp_iff.mpr (memLp_id_gaussianReal 2)).sub (memLp_const _)
  have hgi i : Measurable (fun y => g y i) := (measurable_pi_apply i).comp hgm
  have hdgi i : Measurable (fun y => dg y i) := (measurable_pi_apply i).comp hdgm
  have hg₂ i : MemLp (fun y => g y i) 2 P := by
    apply MemLp.of_bound (hgi i).aestronglyMeasurable C
    exact ae_of_all _ (by simpa only [Real.norm_eq_abs] using fun y => hg y i)
  have hdgint i : Integrable (fun y => dg y i) P :=
    (integrable_const C').mono' (hdgi i).aestronglyMeasurable
      (ae_of_all _ (by simpa only [Real.norm_eq_abs] using fun y => hdg y i))
  have hcross i : Integrable (fun y => (y i - θ i) * g y i) P :=
    (hY₂ i).integrable_mul (hg₂ i)
  have hri i : Integrable (fun y => g y i ^ 2 + 2 * v * dg y i) P := by
    simpa only [Pi.add_apply] using! (hg₂ i).integrable_sq.add ((hdgint i).const_mul (2 * v))
  have he i : (∫ y, (y i + g y i - θ i) ^ 2 ∂P) =
      (v : ℝ) + ∫ y, (g y i ^ 2 + 2 * v * dg y i) ∂P := by
    have hpoint y : (y i + g y i - θ i) ^ 2 =
        (y i - θ i) ^ 2 + g y i ^ 2 + 2 * ((y i - θ i) * g y i) := by ring
    simp_rw [hpoint]
    have hab : Integrable (fun y => (y i - θ i) ^ 2 + g y i ^ 2) P := by
      simpa only [Pi.add_apply] using! (hY₂ i).integrable_sq.add (hg₂ i).integrable_sq
    rw [integral_add hab ((hcross i).const_mul 2),
      integral_add (hY₂ i).integrable_sq (hg₂ i).integrable_sq, integral_const_mul,
      normal_coordinate_stein θ v hv i (hgi i) (hdgi i) (hd i)
        (fun y => hg y i) (fun y => hdg y i),
      integral_add (hg₂ i).integrable_sq ((hdgint i).const_mul (2 * v)), integral_const_mul]
    have hr := affine_normal_risk (hY i) 0 1
    simp only [mse, zero_add, one_mul, one_pow, sub_self, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero] at hr
    rw [hr]
    ring
  change (∫ y, ∑ i, (y i + g y i - θ i) ^ 2 ∂P) = _
  rw [integral_finsetSum _ (fun i _ => ?_)]
  · simp_rw [he]
    rw [Finset.sum_add_distrib, ← integral_finsetSum _ (fun i _ => hri i)]
    simp [Finset.sum_const, Fintype.card_fin, P]
  · have h := ((hY₂ i).add (hg₂ i)).integrable_sq
    convert! h using 1
    funext y
    simp only [Pi.add_apply]
    congr 1
    ring

end LectureNotes
