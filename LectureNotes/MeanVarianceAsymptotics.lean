import LectureNotes.VectorDeltaMethod
import LectureNotes.VarianceAsymptotics
import LectureNotes.InstrumentalVariables

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- The two centered influence coordinates for the sample mean and variance. -/
def meanVarianceInfluenceVector (μ v x : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![x - μ, (x - μ) ^ 2 - v]

def meanVarianceCoordinates : EuclideanSpace ℝ (Fin 2) →L[ℝ] (ℝ × ℝ) :=
  (EuclideanSpace.proj 0).prod (EuclideanSpace.proj 1)

@[simp] theorem meanVarianceCoordinates_apply (x : EuclideanSpace ℝ (Fin 2)) :
    meanVarianceCoordinates x = (x 0, x 1) := rfl

@[simp] theorem meanVarianceCoordinates_influence (μ v x : ℝ) :
    meanVarianceCoordinates (meanVarianceInfluenceVector μ v x) =
      (x - μ, (x - μ) ^ 2 - v) := rfl

theorem meanVarianceInfluenceVector_measurable (μ v : ℝ) :
    Measurable (meanVarianceInfluenceVector μ v) := by
  unfold meanVarianceInfluenceVector
  fun_prop

theorem meanVarianceInfluenceVector_memLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : MemLp X 4 P) (μ v : ℝ) :
    MemLp (fun ω => meanVarianceInfluenceVector μ v (X ω)) 2 P := by
  have h2 : MemLp (fun ω => X ω - μ) 2 P :=
    (hX.mono_exponent (by norm_num)).sub (memLp_const μ)
  have hs : MemLp (fun ω => (X ω - μ) ^ 2) 2 P := by
    apply (memLp_two_iff_integrable_sq (h2.aestronglyMeasurable.pow 2)).mpr
    have h4 := (hX.sub (memLp_const μ)).integrable_norm_pow' (p := 4)
    simpa only [Pi.sub_apply, Pi.pow_apply, Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs] using! h4
  apply MemLp.of_eval_piLp
  intro i
  fin_cases i
  · exact h2
  · exact hs.sub (memLp_const v)

theorem meanVarianceInfluenceVector_mean {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hXm : Measurable X) (hX : MemLp X 4 P) :
    (∫ ω, meanVarianceInfluenceVector P[X] Var[X; P] (X ω) ∂P) = 0 := by
  have h2 : MemLp X 2 P := hX.mono_exponent (by norm_num)
  have hi := (meanVarianceInfluenceVector_memLp hX P[X] Var[X; P]).integrable (by norm_num)
  ext i
  rw [eval_integral_piLp (fun i => hi.eval_piLp i)]
  fin_cases i
  · change (∫ ω, X ω - P[X] ∂P) = 0
    rw [integral_sub (h2.integrable (by norm_num)) (integrable_const _)]
    simp
  · change (∫ ω, (X ω - P[X]) ^ 2 - Var[X; P] ∂P) = 0
    have hc : MemLp (fun ω => X ω - P[X]) 2 P := h2.sub (memLp_const _)
    rw [integral_sub hc.integrable_sq (integrable_const _),
      ← variance_eq_integral hXm.aemeasurable]
    simp

/-- The actual normalized averages of the two influence coordinates have a
joint Gaussian limit constructed from their covariance, even when singular. -/
theorem iid_mean_variance_influence_clt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n •
      (sampleMean (fun i : Fin n => X i ω - P[X 0]),
        sampleMean (fun i : Fin n => (X i ω - P[X 0]) ^ 2 - Var[X 0; P])))
      atTop meanVarianceCoordinates (fun _ => P)
      (multivariateGaussian 0 (vectorCovariance P
        (fun ω => meanVarianceInfluenceVector P[X 0] Var[X 0; P] (X 0 ω)))) := by
  let g := meanVarianceInfluenceVector P[X 0] Var[X 0; P]
  have h := iid_zero_mean_vector_score_clt X g (meanVarianceInfluenceVector_measurable _ _)
    hind hident (meanVarianceInfluenceVector_memLp hX _ _)
    (meanVarianceInfluenceVector_mean (hXm 0) hX) HasLaw.id
  have hh := h.continuous_comp meanVarianceCoordinates.continuous
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl)) hh
  intro n
  apply ae_of_all
  intro ω
  simp only [Function.comp_apply, map_smul, map_sum, meanVarianceCoordinates_influence,
    meanVarianceCoordinates_apply, g, smul_smul]
  ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_sum, Prod.snd_sum,
    smul_eq_mul, sampleMean, Fintype.card_fin]
  · simp only [meanVarianceInfluenceVector, PiLp.toLp_apply, Matrix.cons_val_zero]
    rw [Fin.sum_univ_eq_sum_range (fun i => X i ω - P[X 0]) n]
    ring
  · simp only [meanVarianceInfluenceVector, PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [Fin.sum_univ_eq_sum_range (fun i => (X i ω - P[X 0]) ^ 2 - Var[X 0; P]) n]
    ring

/-- Joint strong consistency of the actual mean and denominator-(n-1) variance. -/
theorem iid_mean_variance_strong_consistency {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n =>
      (sampleMean (fun i : Fin n => X i ω), sampleVariance (fun i : Fin n => X i ω)))
      atTop (𝓝 (P[X 0], Var[X 0; P])) := by
  have hmean := strong_law_of_large_numbers (hX.integrable (by norm_num))
    (fun _ _ hij => hind.indepFun hij) hident
  filter_upwards [hmean, sampleVariance_strong_consistency hXm hX hind hident] with ω hm hv
  have hh := hm.prodMk_nhds hv
  convert! hh using 1
  funext n
  simp only [sampleMean, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => X i ω) n]
  simp only [div_eq_mul_inv, mul_comm]

theorem sqrt_nat_div_pred_tendsto_zero :
    Tendsto (fun n : ℕ => Real.sqrt n / (n - 1)) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hr : Tendsto (fun n : ℕ => (n : ℝ) / (n - 1)) atTop (𝓝 1) := by
    simpa only [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)
  have hh := hi.mul hr
  simp only [zero_mul] at hh
  apply hh.congr
  intro n
  by_cases hn : n = 0
  · subst n; simp
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).ne'
  have he : (Real.sqrt n)⁻¹ * (n : ℝ) = Real.sqrt n := by
    calc
      _ = (Real.sqrt n)⁻¹ * (Real.sqrt n * Real.sqrt n) := by rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg n)]
      _ = _ := inv_mul_cancel_left₀ hs _
  rw [div_eq_mul_inv, ← mul_assoc, he, div_eq_mul_inv]

/-- The actual joint mean/variance CLT. The finite-sample centering and the
n−1 denominator are accounted for by vanishing remainders. -/
theorem iid_mean_variance_clt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n •
      ((sampleMean (fun i : Fin n => X i ω), sampleVariance (fun i : Fin n => X i ω)) -
        (P[X 0], Var[X 0; P]))) atTop meanVarianceCoordinates (fun _ => P)
      (multivariateGaussian 0 (vectorCovariance P
        (fun ω => meanVarianceInfluenceVector P[X 0] Var[X 0; P] (X 0 ω)))) := by
  let μ := P[X 0]
  let v := Var[X 0; P]
  let M (n : ℕ) (ω : Ω) := sampleMean (fun i : Fin n => X i ω - μ)
  let C (n : ℕ) (ω : Ω) := Real.sqrt n / (n - 1) * empiricalVariance (fun i : Fin n => X i ω)
  have h2 : MemLp (X 0) 2 P := hX.mono_exponent (by norm_num)
  have hMm n : Measurable (M n) := by unfold M sampleMean; fun_prop
  have hCm n : Measurable (C n) := by unfold C empiricalVariance sampleMean; fun_prop
  have hlin := iid_mean_variance_influence_clt hXm hX hind hident
  have hMroot := hlin.continuous_comp (g := Prod.fst) continuous_fst
  have hM : ConvergesInProbability P M (fun _ => 0) := by
    let g (x : ℝ) := x - μ
    have hg : Measurable g := by unfold g; fun_prop
    have hi : Integrable (fun ω => g (X 0 ω)) P :=
      (h2.sub (memLp_const μ)).integrable (by norm_num)
    have hm : (∫ ω, g (X 0 ω) ∂P) = 0 := by
      rw [show (fun ω => g (X 0 ω)) = fun ω => X 0 ω - μ from rfl,
        integral_sub (h2.integrable (by norm_num)) (integrable_const _)]
      simp [μ]
    have hh := iid_statistic_average_limit X g hXm hg hind hident hi
    rw [hm] at hh
    convert! hh using 1
    funext n ω
    simp only [M, sampleMean, Fintype.card_fin, g]
    rw [Fin.sum_univ_eq_sum_range (fun i => X i ω - μ) n]
    ring
  have hC : ConvergesInProbability P C (fun _ => 0) := by
    apply almost_sure_implies_probability (fun n => (hCm n).aemeasurable)
    filter_upwards [empiricalVariance_strong_consistency hXm h2 hind hident] with ω hω
    simpa only [zero_mul] using sqrt_nat_div_pred_tendsto_zero.mul hω
  have hprod : ConvergesInProbability P
      (fun n ω => (Real.sqrt n * M n ω) * M n ω) (fun _ => 0) := by
    exact slutsky_mul_zero hMroot hM (fun n => (hMm n).aemeasurable)
  have hR : TendstoInMeasure P
      (fun n ω => (0, C n ω - (Real.sqrt n * M n ω) * M n ω) : ℕ → Ω → ℝ × ℝ)
      atTop (fun _ => (0, 0)) := by
    have hh := continuous_mapping_probability_const_metric
      (g := fun z : ℝ × ℝ => ((0 : ℝ), z.1 - z.2)) (by fun_prop) (probability_product_const hC hprod)
    simpa only [sub_zero] using hh
  have hactualm (n : ℕ) : Measurable (fun ω => Real.sqrt n •
      ((sampleMean (fun i : Fin n => X i ω), sampleVariance (fun i : Fin n => X i ω)) - (μ, v))) := by
    unfold sampleVariance sampleMean
    fun_prop
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ _ hlin _ (fun n => (hactualm n).aemeasurable)
  apply TendstoInMeasure.congr' _ (ae_of_all _ (fun _ => rfl)) hR
  filter_upwards [eventually_gt_atTop 1] with n hn
  apply ae_of_all
  intro ω
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  have he := empiricalVariance_normalized_decomposition (fun i : Fin n => X i ω) μ v
  change (0, C n ω - (Real.sqrt n * M n ω) * M n ω) =
    Real.sqrt n • ((sampleMean (fun i : Fin n => X i ω), sampleVariance (fun i : Fin n => X i ω)) - (μ, v)) -
      Real.sqrt n • (sampleMean (fun i : Fin n => X i ω - μ),
        sampleMean (fun i : Fin n => (X i ω - μ) ^ 2 - v))
  rw [sampleVariance_eq_scaled_empiricalVariance hn]
  simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_sub_mk, sampleMean_sub_const hn0, M, C]
  ext
  · ring
  · have hd : (n : ℝ) - 1 ≠ 0 := (sub_pos.mpr (by exact_mod_cast hn : (1 : ℝ) < n)).ne'
    simp only [sampleMean_sub_const hn0] at he
    have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn0)).ne'
    have he' : empiricalVariance (fun i : Fin n => X i ω) =
        sampleMean (fun i : Fin n => (X i ω - μ) ^ 2) -
          (sampleMean (fun i : Fin n => X i ω) - μ) ^ 2 := by
      apply mul_left_cancel₀ hs
      nlinarith only [he]
    rw [he']
    field_simp
    ring

/-- L8's nonlinear delta limit for h(mean, sampleVariance). The limit variance
is the variance of the actual derivative influence function. It may be zero. -/
theorem iid_mean_variance_function_clt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {h : ℝ × ℝ → ℝ} (hh : Continuous h) (D : (ℝ × ℝ) →L[ℝ] ℝ)
    (hd : HasFDerivAt h D (P[X 0], Var[X 0; P])) :
    ConvergesInDistribution P
      (gaussianReal 0 Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P].toNNReal)
      (fun (n : ℕ) ω => Real.sqrt n *
        (h (sampleMean (fun i : Fin n => X i ω), sampleVariance (fun i : Fin n => X i ω)) -
          h (P[X 0], Var[X 0; P]))) id := by
  let E (n : ℕ) (ω : Ω) :=
    (sampleMean (fun i : Fin n => X i ω), sampleVariance (fun i : Fin n => X i ω))
  have hEm n : Measurable (E n) := by unfold E sampleVariance sampleMean; fun_prop
  have hE : TendstoInMeasure P E atTop (fun _ => (P[X 0], Var[X 0; P])) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hEm n).aestronglyMeasurable)
      (iid_mean_variance_strong_consistency hXm (hX.mono_exponent (by norm_num)) hind hident)
  have hc := normed_delta_method (fun n => (hEm n).aemeasurable) hE
    (iid_mean_variance_clt hXm hX hind hident) hh hd
  have hl := gaussian_vectorCovariance_projection
    (meanVarianceInfluenceVector_memLp hX P[X 0] Var[X 0; P]) (D.comp meanVarianceCoordinates)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, meanVarianceCoordinates_influence] at hl
  refine ⟨hc.forall_aemeasurable, measurable_id.aemeasurable, ?_⟩
  convert! hc.tendsto using 2
  congr 1
  apply Subtype.ext
  simpa only [Measure.map_id, Function.comp_def] using! hl.map_eq.symm

/-- Standardization needs a positive influence variance. A nonzero derivative
alone does not imply this when the joint mean/variance limit is singular. -/
theorem iid_mean_variance_function_standardized_clt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {h : ℝ × ℝ → ℝ} (hh : Continuous h) (D : (ℝ × ℝ) →L[ℝ] ℝ)
    (hd : HasFDerivAt h D (P[X 0], Var[X 0; P]))
    (τ : ℝ) (hτ : 0 < τ)
    (hvar : Var[fun ω => D (X 0 ω - P[X 0], (X 0 ω - P[X 0]) ^ 2 - Var[X 0; P]); P] = τ ^ 2) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => Real.sqrt ((n : ℝ) + 1) / τ *
        (h (sampleMean (fun i : Fin (n + 1) => X i ω), sampleVariance (fun i : Fin (n + 1) => X i ω)) -
          h (P[X 0], Var[X 0; P]))) id := by
  have hc := iid_mean_variance_function_clt hXm hX hind hident hh D hd
  rw [hvar] at hc
  have hs : ConvergesInDistribution P (gaussianReal 0 (τ ^ 2).toNNReal)
      (fun n ω => Real.sqrt (n + 1 : ℕ) *
        (h (sampleMean (fun i : Fin (n + 1) => X i ω), sampleVariance (fun i : Fin (n + 1) => X i ω)) -
          h (P[X 0], Var[X 0; P]))) id :=
    { forall_aemeasurable := fun n => hc.forall_aemeasurable (n + 1)
      tendsto := hc.tendsto.comp (tendsto_add_atTop_nat 1) }
  have hdlim := continuous_mapping_distribution (g := fun z => z / τ) (by fun_prop) hs
  have hl : HasLaw (fun z : ℝ => z / τ) (gaussianReal 0 1) (gaussianReal 0 (τ ^ 2).toNNReal) := by
    have hquot : (τ ^ 2).toNNReal / NNReal.mk (τ ^ 2) (sq_nonneg τ) = 1 := by
      apply NNReal.coe_injective
      simp only [NNReal.coe_div, Real.coe_toNNReal _ (sq_nonneg τ), NNReal.coe_mk, NNReal.coe_one]
      exact div_self (sq_pos_of_pos hτ).ne'
    simpa only [id_eq, zero_div, hquot] using
      gaussianReal_div_const (HasLaw.id : HasLaw id (gaussianReal 0 (τ ^ 2).toNNReal)
        (gaussianReal 0 (τ ^ 2).toNNReal)) τ
  have hhlim : ConvergesInDistribution P (gaussianReal 0 1)
      (fun n ω => (Real.sqrt (n + 1 : ℕ) *
        (h (sampleMean (fun i : Fin (n + 1) => X i ω), sampleVariance (fun i : Fin (n + 1) => X i ω)) -
          h (P[X 0], Var[X 0; P]))) / τ) id := by
    refine ⟨hdlim.forall_aemeasurable, measurable_id.aemeasurable, ?_⟩
    convert! hdlim.tendsto using 2
    congr 1
    apply Subtype.ext
    simpa only [Measure.map_id, id_eq] using hl.map_eq.symm
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl)) hhlim
  intro n
  apply ae_of_all
  intro ω
  simp only [Nat.cast_add, Nat.cast_one]
  ring

end LectureNotes
