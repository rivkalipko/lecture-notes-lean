import LectureNotes.SteinDecision

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Transport a density along a measurable equivalence. -/
theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  apply Measure.ext_of_lintegral _
  intro g hg
  rw [lintegral_map hg e.measurable,
    lintegral_withDensity_eq_lintegral_mul _ hf (g := fun a => g (e a))
      (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _
      (f := fun y => f (e.symm y)) (by fun_prop) hg]
  simp only [Pi.mul_apply]
  rw [lintegral_map (f := fun y => f (e.symm y) * g y) (by fun_prop) e.measurable]
  simp

/-- The product density of independent normal coordinates, relative to the
usual product Lebesgue measure. -/
theorem normal_pi_withDensity {p : ℕ} (θ : Fin p → ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun i => gaussianReal (θ i) v) =
      volume.withDensity (fun y => ∏ i, gaussianPDF (θ i) v (y i)) := by
  induction p with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    change (Measure.pi (fun i : Fin 0 => gaussianReal (θ i) v)) =
      (volume : Measure (Fin 0 → ℝ)).withDensity (1 : (Fin 0 → ℝ) → ℝ≥0∞)
    rw [withDensity_one]
    change Measure.pi _ = Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ))
    congr 1
    ext i
    exact Fin.elim0 i
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hn := measurePreserving_piFinSuccAbove (fun i => gaussianReal (θ i) v) 0
    have hl := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    apply e.measurableEmbedding.map_injective
    rw [hn.map_eq, map_withDensity_equiv _ e _ (by fun_prop)]
    rw [hl.map_eq, ih, gaussianReal_of_var_ne_zero _ hv, prod_withDensity]
    · congr 1
      ext z
      simp [e, Fin.prod_univ_succ]
    all_goals fun_prop

/-- Normal likelihood times normal prior equals predictive density times
posterior density. Both sides retain their normalizing constants. -/
theorem gaussian_prior_likelihood (v w : ℝ≥0) (hv : 0 < v) (hw : 0 < w)
    (θ y : ℝ) :
    gaussianPDF 0 w θ * gaussianPDF θ v y =
      gaussianPDF 0 (v + w) y *
        gaussianPDF ((w : ℝ) / (v + w) * y) (v * w / (v + w)) θ := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hs : (v : ℝ) + w ≠ 0 := by positivity
  have he : -θ ^ 2 / (2 * w) + -(y - θ) ^ 2 / (2 * v) =
      -y ^ 2 / (2 * ((v : ℝ) + w)) +
        -(θ - (w : ℝ) / (v + w) * y) ^ 2 /
          (2 * ((v : ℝ) * w / (v + w))) := by
    field_simp
    ring
  have hc : (Real.sqrt (2 * Real.pi * (w : ℝ)))⁻¹ *
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ =
      (Real.sqrt (2 * Real.pi * ((v : ℝ) + w)))⁻¹ *
        (Real.sqrt (2 * Real.pi * ((v : ℝ) * w / (v + w))))⁻¹ := by
    rw [← mul_inv, ← mul_inv, ← Real.sqrt_mul (by positivity),
      ← Real.sqrt_mul (by positivity)]
    congr 2
    field_simp
  simp only [gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul, sub_zero]
  calc
    _ = ((Real.sqrt (2 * Real.pi * (w : ℝ)))⁻¹ *
        (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) *
          Real.exp (-θ ^ 2 / (2 * w) + -(y - θ) ^ 2 / (2 * v)) := by
      rw [Real.exp_add]; ring
    _ = _ := by rw [hc, he, Real.exp_add]; ring

/-- Tonelli disintegration for the finite-dimensional normal-normal experiment.
It applies to every nonnegative measurable loss, without finite-risk assumptions. -/
theorem normal_bayes_disintegration {p : ℕ} (v w : ℝ≥0) (hv : 0 < v) (hw : 0 < w)
    (L : (Fin p → ℝ) → (Fin p → ℝ) → ℝ≥0∞)
    (hL : Measurable (Function.uncurry L)) :
    (∫⁻ θ, ∫⁻ y, L θ y ∂Measure.pi (fun i => gaussianReal (θ i) v)
      ∂Measure.pi (fun _ => gaussianReal 0 w)) =
    ∫⁻ y, ∫⁻ θ, L θ y
      ∂Measure.pi (fun i => gaussianReal ((w : ℝ) / (v + w) * y i) (v * w / (v + w)))
      ∂Measure.pi (fun _ => gaussianReal 0 (v + w)) := by
  let d := fun (θ : Fin p → ℝ) (s : ℝ≥0) (y : Fin p → ℝ) =>
    ∏ i, gaussianPDF (θ i) s (y i)
  have hd (θ : Fin p → ℝ) (s : ℝ≥0) : Measurable (d θ s) := by dsimp [d]; fun_prop
  have hform (θ : Fin p → ℝ) (s : ℝ≥0) (hs : s ≠ 0)
      (f : (Fin p → ℝ) → ℝ≥0∞) (hf : Measurable f) :
      (∫⁻ z, f z ∂Measure.pi (fun i => gaussianReal (θ i) s)) =
        ∫⁻ z, d θ s z * f z := by
    rw [normal_pi_withDensity θ s hs, lintegral_withDensity_eq_lintegral_mul _ (hd θ s) hf]
    rfl
  have hleft (θ : Fin p → ℝ) :
      (∫⁻ y, L θ y ∂Measure.pi (fun i => gaussianReal (θ i) v)) =
        ∫⁻ y, d θ v y * L θ y := hform θ v hv.ne' _ (by fun_prop)
  have hright (y : Fin p → ℝ) :
      (∫⁻ θ, L θ y ∂Measure.pi
        (fun i => gaussianReal ((w : ℝ) / (v + w) * y i) (v * w / (v + w)))) =
        ∫⁻ θ, d (fun i => (w : ℝ) / (v + w) * y i) (v * w / (v + w)) θ * L θ y :=
    hform _ _ (by positivity) _ (by fun_prop)
  simp_rw [hleft, hright]
  rw [hform (fun _ => 0) w hw.ne' _ (by dsimp [d]; fun_prop),
    hform (fun _ => 0) (v + w) (by positivity) _ (by dsimp [d]; fun_prop)]
  have hpull (c : ℝ≥0∞) (f : (Fin p → ℝ) → ℝ≥0∞) (hf : Measurable f) :
      c * (∫⁻ x, f x) = ∫⁻ x, c * f x := (lintegral_const_mul'' c hf.aemeasurable).symm
  calc
    _ = ∫⁻ θ, ∫⁻ y, d (fun _ => 0) w θ * (d θ v y * L θ y) :=
      lintegral_congr (fun θ => hpull _ _ (by dsimp [d]; fun_prop))
    _ = ∫⁻ y, ∫⁻ θ, d (fun _ => 0) w θ * (d θ v y * L θ y) :=
      lintegral_lintegral_swap (by dsimp [d]; fun_prop)
    _ = ∫⁻ y, ∫⁻ θ, d (fun _ => 0) (v + w) y *
        (d (fun i => (w : ℝ) / (v + w) * y i) (v * w / (v + w)) θ * L θ y) := by
      apply lintegral_congr
      intro y
      apply lintegral_congr
      intro θ
      rw [← mul_assoc, ← mul_assoc]
      congr 1
      dsimp [d]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      exact gaussian_prior_likelihood v w hv hw (θ i) (y i)
    _ = _ := lintegral_congr (fun y => (hpull _ _ (by dsimp [d]; fun_prop)).symm)

/-- Exact posterior loss at a fixed action. -/
theorem normal_squared_loss_integral {p : ℕ} (μ a : Fin p → ℝ) (v : ℝ≥0) :
    (∫⁻ θ, ENNReal.ofReal (∑ i, (a i - θ i) ^ 2)
      ∂Measure.pi (fun i => gaussianReal (μ i) v)) =
      ENNReal.ofReal (p * (v : ℝ) + ∑ i, (a i - μ i) ^ 2) := by
  let P := Measure.pi (fun i => gaussianReal (μ i) v)
  have hY (i : Fin p) : HasLaw (fun θ : Fin p → ℝ => θ i) (gaussianReal (μ i) v) P :=
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  have h₂ (i : Fin p) : MemLp (fun θ : Fin p → ℝ => θ i) 2 P :=
    ((hY i).identDistrib HasLaw.id).memLp_iff.mpr (memLp_id_gaussianReal 2)
  have hi (i : Fin p) : Integrable (fun θ : Fin p → ℝ => (a i - θ i) ^ 2) P :=
    ((memLp_const (a i)).sub (h₂ i)).integrable_sq
  have he (i : Fin p) : (∫ θ, (a i - θ i) ^ 2 ∂P) = v + (a i - μ i) ^ 2 := by
    simp_rw [sub_sq_comm (a i)]
    change mse P (fun θ => θ i) (a i) = _
    rw [mse_bias_variance_decomposition P (h₂ i), bias]
    rw [(hY i).integral_eq, (hY i).variance_eq]
    simp
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_finsetSum _ (fun i _ => hi i))
    (ae_of_all _ (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
  congr 1
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [he]
  simp [Finset.sum_add_distrib]

/-- A normal prior supplies a lower bound on the integrated risk of every
measurable rule, even if its risk is infinite. -/
theorem normal_bayes_risk_lower_bound {p : ℕ} (v w : ℝ≥0) (hv : 0 < v) (hw : 0 < w)
    (δ : (Fin p → ℝ) → Fin p → ℝ) (hδ : Measurable δ) :
    ENNReal.ofReal (p * ((v : ℝ) * w / (v + w))) ≤
      ∫⁻ θ, normalMeansSquaredRisk v δ θ ∂Measure.pi (fun _ => gaussianReal 0 w) := by
  unfold normalMeansSquaredRisk risk
  rw [normal_bayes_disintegration v w hv hw _ (by fun_prop)]
  simp_rw [normal_squared_loss_integral]
  calc
    _ = ∫⁻ _y : Fin p → ℝ, ENNReal.ofReal (p * ((v : ℝ) * w / (v + w)))
        ∂Measure.pi (fun _ => gaussianReal 0 (v + w)) := by simp
    _ ≤ _ := lintegral_mono (fun y => ENNReal.ofReal_le_ofReal (by
      simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))

/-- The precision-weighted normal posterior mean attains the Bayes lower bound. -/
theorem normal_shrinkage_bayes_risk {p : ℕ} (v w : ℝ≥0) (hv : 0 < v) (hw : 0 < w) :
    (∫⁻ θ, normalMeansSquaredRisk v (fun y i => (w : ℝ) / (v + w) * y i) θ
      ∂Measure.pi (fun _ : Fin p => gaussianReal 0 w)) =
      ENNReal.ofReal (p * ((v : ℝ) * w / (v + w))) := by
  unfold normalMeansSquaredRisk risk
  rw [normal_bayes_disintegration v w hv hw _ (by fun_prop)]
  simp_rw [normal_squared_loss_integral]
  simp

/-- Normal posterior-mean shrinkage is Bayes among all measurable rules. -/
theorem normal_shrinkage_is_bayes {p : ℕ} (v w : ℝ≥0) (hv : 0 < v) (hw : 0 < w) :
    IsBayesRule
      (fun δ : {f : (Fin p → ℝ) → Fin p → ℝ // Measurable f} =>
        ∫⁻ θ, normalMeansSquaredRisk v δ.1 θ ∂Measure.pi (fun _ => gaussianReal 0 w))
      ⟨fun y i => (w : ℝ) / (v + w) * y i, by fun_prop⟩ := by
  intro δ
  dsimp only
  rw [normal_shrinkage_bayes_risk v w hv hw]
  exact normal_bayes_risk_lower_bound v w hv hw δ.1 δ.2

end LectureNotes
