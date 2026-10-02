import LectureNotes.VectorWald
import LectureNotes.WilksAnalytic
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

/-! Vector likelihood-ratio expansions from actual derivatives. The quadratic
remainder is controlled directly by a derivative envelope, without selecting
a random point on an estimation segment. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative of the half-quadratic form associated with a symmetric
operator is its linear gradient. -/
theorem hasFDerivAt_half_quadratic (H : E →L[ℝ] E)
    (hsym : ∀ x y, ⟪H x, y⟫_ℝ = ⟪x, H y⟫_ℝ) (t x : E) :
    HasFDerivAt (fun y => (1 / 2 : ℝ) * ⟪H (y - t), y - t⟫_ℝ)
      (innerSL ℝ (H (x - t))) x := by
  have h₁ := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const t
  have h₂ := H.hasFDerivAt.comp x h₁
  convert! (h₂.inner ℝ h₁).const_mul (1 / 2 : ℝ) using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply, smul_eq_mul, Function.comp_apply, id_eq]
  rw [hsym (x - t) v, real_inner_comm (H v) (x - t)]
  ring

/-- A stationary point and a Lipschitz derivative give a second-order
likelihood expansion with an explicit remainder in operator norm. -/
theorem vector_likelihood_quadratic_error
    {f : E → ℝ} {score : E → E} {L : E → E →L[ℝ] E} {D : Set E}
    (hD : Convex ℝ D) {θ t : E} {H : E →L[ℝ] E} {B : ℝ}
    (hsym : ∀ x y, ⟪H x, y⟫_ℝ = ⟪x, H y⟫_ℝ)
    (hθ : θ ∈ D) (ht : t ∈ D) (hB : 0 ≤ B)
    (hf : ∀ x ∈ D, HasFDerivWithinAt f (innerSL ℝ (score x)) D x)
    (hs : ∀ x ∈ D, HasFDerivWithinAt score (L x) D x)
    (hL : ∀ x ∈ D, ‖L x - L θ‖ ≤ B * ‖x - θ‖)
    (hroot : score t = 0) :
    |2 * (f t - f θ) - ⟪H (t - θ), t - θ⟫_ℝ| ≤
      2 * (B * ‖t - θ‖ + ‖L θ + H‖) * ‖t - θ‖ ^ 2 := by
  let K := B * ‖t - θ‖ + ‖L θ + H‖
  let g x := f x + (1 / 2 : ℝ) * ⟪H (x - t), x - t⟫_ℝ
  let g' x := score x + H (x - t)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsub : segment ℝ θ t ⊆ D := hD.segment_subset hθ ht
  have hg x (hx : x ∈ segment ℝ θ t) :
      HasFDerivWithinAt g (innerSL ℝ (g' x)) (segment ℝ θ t) x := by
    simpa only [g, g', map_add] using!
      ((hf x (hsub hx)).mono hsub).add
        (hasFDerivAt_half_quadratic H hsym t x).hasFDerivWithinAt
  have hg' x (hx : x ∈ segment ℝ θ t) :
      HasFDerivWithinAt g' (L x + H) (segment ℝ θ t) x := by
    simpa only [g', ContinuousLinearMap.comp_id] using!
      ((hs x (hsub hx)).mono hsub).add
        (H.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const t)).hasFDerivWithinAt
  have hcb x (hx : x ∈ segment ℝ θ t) : ‖L x + H‖ ≤ K := by
    calc
      ‖L x + H‖ = ‖(L x - L θ) + (L θ + H)‖ := by congr 1; abel
      _ ≤ ‖L x - L θ‖ + ‖L θ + H‖ := norm_add_le _ _
      _ ≤ K := by
        dsimp [K]
        gcongr
        exact (hL x (hsub hx)).trans
          (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hx) hB)
  have hgb x (hx : x ∈ segment ℝ θ t) : ‖innerSL ℝ (g' x)‖ ≤ K * ‖t - θ‖ := by
    have hm := (convex_segment θ t).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hg' hcb (right_mem_segment ℝ θ t) hx
    have hg't : g' t = 0 := by simp [g', hroot]
    rw [hg't, sub_zero] at hm
    rw [innerSL_apply_norm]
    apply hm.trans
    apply mul_le_mul_of_nonneg_left _ hK
    have hx' : x ∈ segment ℝ t θ := by simpa only [segment_symm ℝ t θ] using hx
    simpa only [norm_sub_rev] using norm_sub_le_of_mem_segment hx'
  have hm := (convex_segment θ t).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hg hgb (right_mem_segment ℝ θ t) (left_mem_segment ℝ θ t)
  have hneg : ⟪H (θ - t), θ - t⟫_ℝ = ⟪H (t - θ), t - θ⟫_ℝ := by
    rw [show θ - t = -(t - θ) by abel, map_neg, inner_neg_neg]
  have he : 2 * (f t - f θ) - ⟪H (t - θ), t - θ⟫_ℝ = -2 * (g θ - g t) := by
    simp only [g, sub_self, map_zero, inner_zero_left, mul_zero, add_zero, hneg]
    ring
  rw [he, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |g θ - g t| ≤ 2 * ((K * ‖t - θ‖) * ‖θ - t‖) := by
      exact mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = 2 * K * ‖t - θ‖ ^ 2 := by rw [norm_sub_rev θ t]; ring

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {d : ℕ}

/-- Vector Wilks for a point null, derived from actual likelihood derivatives.
The estimator limit can be supplied by the IID vector MLE theorem. -/
theorem vector_wilks_from_derivatives
    (f : ℕ → Ω → EuclideanSpace ℝ (Fin d) → ℝ)
    (score : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℕ → Ω → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (B : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (hD : Convex ℝ D)
    (θ : EuclideanSpace ℝ (Fin d)) (M : ℝ) (hθ : θ ∈ D)
    (V : Matrix (Fin d) (Fin d) ℝ) (hV : V.PosDef)
    (hTin : ∀ n ω, T n ω ∈ D) (hTm : ∀ n, Measurable (T n))
    (hfm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => f n p.1 p.2))
    (hBm : ∀ n, AEMeasurable (B n) P)
    (hLm : ∀ n, AEMeasurable (fun ω => L n ω θ) P)
    (hB0 : ∀ n ω, 0 ≤ B n ω)
    (hf : ∀ n ω x, x ∈ D → HasFDerivWithinAt (f n ω) (innerSL ℝ (score n ω x)) D x)
    (hs : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hL : ∀ n ω x, x ∈ D → ‖L n ω x - L n ω θ‖ ≤ B n ω * ‖x - θ‖)
    (hroot : ∀ n ω, score n ω (T n ω) = 0)
    (hT : TendstoInMeasure P T atTop (fun _ => θ))
    (hB : TendstoInMeasure P B atTop (fun _ => M))
    (hc : TendstoInMeasure P (fun n ω => L n ω θ) atTop
      (fun _ => -toEuclideanCLM (𝕜 := ℝ) V⁻¹))
    {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    (hE : TendstoInDistribution (fun n ω => rate n • (T n ω - θ)) atTop Z (fun _ => P) Q)
    (hZ : HasLaw Z (multivariateGaussian 0 V) Q) :
    ConvergesInDistribution P Q
      (fun n ω => 2 * rate n ^ 2 * (f n ω (T n ω) - f n ω θ))
      (fun ω => ⟪toEuclideanCLM (𝕜 := ℝ) V⁻¹ (Z ω), Z ω⟫_ℝ) ∧
    HasLaw (fun ω => ⟪toEuclideanCLM (𝕜 := ℝ) V⁻¹ (Z ω), Z ω⟫_ℝ) (chiSquared d) Q := by
  let H := toEuclideanCLM (𝕜 := ℝ) V⁻¹
  let err n ω := B n ω * ‖T n ω - θ‖ + ‖L n ω θ + H‖
  let W n ω := rate n • (T n ω - θ)
  let LR n ω := 2 * rate n ^ 2 * (f n ω (T n ω) - f n ω θ)
  have hHsym : ∀ x y, ⟪H x, y⟫_ℝ = ⟪x, H y⟫_ℝ := by
    have hself : H.adjoint = H := by
      exact (hV.inv.isHermitian.isSelfAdjoint.map (toEuclideanCLM (𝕜 := ℝ))).adjoint_eq
    intro x y
    simpa only [hself] using H.adjoint_inner_left y x
  have hp : TendstoInMeasure P (fun n ω => B n ω * ‖T n ω - θ‖) atTop (fun _ => 0) := by
    simpa using continuous_mapping_probability_const_metric
      (g := fun p : ℝ × EuclideanSpace ℝ (Fin d) => p.1 * ‖p.2 - θ‖)
      (by fun_prop) (probability_product_const hB hT)
  have hl : TendstoInMeasure P (fun n ω => ‖L n ω θ + H‖) atTop (fun _ => 0) := by
    simpa only [H, neg_add_cancel, norm_zero] using! continuous_mapping_probability_const_metric
      (g := fun A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) => ‖A + H‖)
      (by fun_prop) hc
  have herr : ConvergesInProbability P err (fun _ => 0) := by
    simpa only [ConvergesInProbability, err, add_zero] using! continuous_mapping_probability_const_metric
      (g := fun p : ℝ × ℝ => p.1 + p.2) (by fun_prop) (probability_product_const hp hl)
  have herrm n : AEMeasurable (err n) P :=
    ((hBm n).mul (((hTm n).aemeasurable.sub_const θ).norm)).add ((hLm n).add_const H).norm
  have hprod : ConvergesInProbability P (fun n ω => ‖W n ω‖ ^ 2 * err n ω) (fun _ => 0) :=
    quadratic_statistics_equivalent (hE.continuous_comp (g := fun x => ‖x‖) (by fun_prop)) herr herrm
  have htwo : ConvergesInProbability P (fun n ω => 2 * err n ω * ‖W n ω‖ ^ 2) (fun _ => 0) := by
    convert! continuous_mapping_probability_const (g := fun x => 2 * x) (by fun_prop) hprod using 1
    · funext n ω; ring
    · simp
  have herror : ConvergesInProbability P
      (fun n ω => LR n ω - ⟪H (W n ω), W n ω⟫_ℝ) (fun _ => 0) := by
    apply probability_zero_of_abs_le (V := fun n ω => 2 * err n ω * ‖W n ω‖ ^ 2) _ htwo
    intro n ω
    have hb := vector_likelihood_quadratic_error hD hHsym hθ (hTin n ω) (hB0 n ω)
      (hf n ω) (hs n ω) (hL n ω) (hroot n ω)
    have he : LR n ω - ⟪H (W n ω), W n ω⟫_ℝ =
        rate n ^ 2 * (2 * (f n ω (T n ω) - f n ω θ) - ⟪H (T n ω - θ), T n ω - θ⟫_ℝ) := by
      simp only [LR, W, map_smul, inner_smul_left, inner_smul_right, conj_trivial]
      ring
    rw [he, abs_mul, abs_of_nonneg (sq_nonneg (rate n))]
    have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg (rate n))
    convert! hb' using 1
    simp only [W, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, err]
    ring
  refine ⟨?_, ?_⟩
  · have hbase := hE.continuous_comp (g := fun x => ⟪H x, x⟫_ℝ) (by fun_prop)
    apply tendstoInDistribution_of_tendstoInMeasure_sub LR (fun ω => ⟪H (Z ω), Z ω⟫_ℝ)
      hbase herror
    intro n
    have ht := (hfm n).comp (measurable_id.prodMk (hTm n))
    have hθm : Measurable (fun ω => f n ω θ) :=
      (hfm n).comp (measurable_id.prodMk measurable_const)
    exact ((ht.sub hθm).const_mul (2 * rate n ^ 2)).aemeasurable
  · simpa only [sub_zero, real_inner_comm] using! normal_mahalanobis hV hZ

/-- Likelihood-ratio expansion against a random constrained estimate. Its
quadratic limit is proved from derivatives and the joint estimation error;
no likelihood expansion is assumed. -/
theorem vector_likelihood_ratio_limit
    (f : ℕ → Ω → EuclideanSpace ℝ (Fin d) → ℝ)
    (score : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℕ → Ω → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (T U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (B : ℕ → Ω → ℝ) (rate : ℕ → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (hD : Convex ℝ D)
    (M : ℝ) (H : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hHsym : ∀ x y, ⟪H x, y⟫_ℝ = ⟪x, H y⟫_ℝ)
    (hTin : ∀ n ω, T n ω ∈ D) (hUin : ∀ n ω, U n ω ∈ D)
    (hTm : ∀ n, Measurable (T n)) (hUm : ∀ n, Measurable (U n))
    (hfm : ∀ n, Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) => f n p.1 p.2))
    (hBm : ∀ n, AEMeasurable (B n) P)
    (hLm : ∀ n, AEMeasurable (fun ω => L n ω (U n ω)) P)
    (hB0 : ∀ n ω, 0 ≤ B n ω)
    (hf : ∀ n ω x, x ∈ D → HasFDerivWithinAt (f n ω) (innerSL ℝ (score n ω x)) D x)
    (hs : ∀ n ω x, x ∈ D → HasFDerivWithinAt (score n ω) (L n ω x) D x)
    (hL : ∀ n ω x, x ∈ D → ‖L n ω x - L n ω (U n ω)‖ ≤ B n ω * ‖x - U n ω‖)
    (hroot : ∀ n ω, score n ω (T n ω) = 0)
    (hTU : TendstoInMeasure P (fun n ω => T n ω - U n ω) atTop (fun _ => 0))
    (hB : TendstoInMeasure P B atTop (fun _ => M))
    (hc : TendstoInMeasure P (fun n ω => L n ω (U n ω)) atTop
      (fun _ => -H))
    {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    (hE : TendstoInDistribution (fun n ω => rate n • (T n ω - U n ω)) atTop Z (fun _ => P) Q) :
    ConvergesInDistribution P Q
      (fun n ω => 2 * rate n ^ 2 * (f n ω (T n ω) - f n ω (U n ω)))
      (fun ω => ⟪H (Z ω), Z ω⟫_ℝ) := by
  let err n ω := B n ω * ‖T n ω - U n ω‖ + ‖L n ω (U n ω) + H‖
  let W n ω := rate n • (T n ω - U n ω)
  let LR n ω := 2 * rate n ^ 2 * (f n ω (T n ω) - f n ω (U n ω))
  have hp : TendstoInMeasure P (fun n ω => B n ω * ‖T n ω - U n ω‖) atTop (fun _ => 0) := by
    simpa using continuous_mapping_probability_const_metric
      (g := fun p : ℝ × EuclideanSpace ℝ (Fin d) => p.1 * ‖p.2‖)
      (by fun_prop) (probability_product_const hB hTU)
  have hl : TendstoInMeasure P (fun n ω => ‖L n ω (U n ω) + H‖) atTop (fun _ => 0) := by
    simpa only [neg_add_cancel, norm_zero] using! continuous_mapping_probability_const_metric
      (g := fun A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) => ‖A + H‖)
      (by fun_prop) hc
  have herr : ConvergesInProbability P err (fun _ => 0) := by
    simpa only [ConvergesInProbability, err, add_zero] using! continuous_mapping_probability_const_metric
      (g := fun p : ℝ × ℝ => p.1 + p.2) (by fun_prop) (probability_product_const hp hl)
  have herrm n : AEMeasurable (err n) P :=
    ((hBm n).mul (((hTm n).aemeasurable.sub (hUm n).aemeasurable).norm)).add ((hLm n).add_const H).norm
  have hprod : ConvergesInProbability P (fun n ω => ‖W n ω‖ ^ 2 * err n ω) (fun _ => 0) :=
    quadratic_statistics_equivalent (hE.continuous_comp (g := fun x => ‖x‖) (by fun_prop)) herr herrm
  have htwo : ConvergesInProbability P (fun n ω => 2 * err n ω * ‖W n ω‖ ^ 2) (fun _ => 0) := by
    convert! continuous_mapping_probability_const (g := fun x => 2 * x) (by fun_prop) hprod using 1
    · funext n ω; ring
    · simp
  have herror : ConvergesInProbability P
      (fun n ω => LR n ω - ⟪H (W n ω), W n ω⟫_ℝ) (fun _ => 0) := by
    apply probability_zero_of_abs_le (V := fun n ω => 2 * err n ω * ‖W n ω‖ ^ 2) _ htwo
    intro n ω
    have hb := vector_likelihood_quadratic_error hD hHsym (hUin n ω) (hTin n ω) (hB0 n ω)
      (hf n ω) (hs n ω) (hL n ω) (hroot n ω)
    have he : LR n ω - ⟪H (W n ω), W n ω⟫_ℝ =
        rate n ^ 2 * (2 * (f n ω (T n ω) - f n ω (U n ω)) - ⟪H (T n ω - U n ω), T n ω - U n ω⟫_ℝ) := by
      simp only [LR, W, map_smul, inner_smul_left, inner_smul_right, conj_trivial]
      ring
    rw [he, abs_mul, abs_of_nonneg (sq_nonneg (rate n))]
    have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg (rate n))
    convert! hb' using 1
    simp only [W, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, err]
    ring
  have hbase := hE.continuous_comp (g := fun x => ⟪H x, x⟫_ℝ) (by fun_prop)
  apply tendstoInDistribution_of_tendstoInMeasure_sub LR (fun ω => ⟪H (Z ω), Z ω⟫_ℝ)
    hbase herror
  intro n
  have ht := (hfm n).comp (measurable_id.prodMk (hTm n))
  have hu := (hfm n).comp (measurable_id.prodMk (hUm n))
  exact ((ht.sub hu).const_mul (2 * rate n ^ 2)).aemeasurable

end LectureNotes
