import LectureNotes.BoundaryNormalMLE

set_option autoImplicit false

/-! L7 Example 5: independent normal pairs with a separate unknown mean for
 each pair. The joint maximum and the inconsistent variance limit are derived
 explicitly; the means may vary arbitrarily across pairs. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

def neymanScottMean (x : ℝ × ℝ) : ℝ := (x.1 + x.2) / 2

def neymanScottVariance {n : ℕ} (x : Fin n → ℝ × ℝ) : ℝ :=
  (∑ i, ((x i).1 - (x i).2) ^ 2) / (4 * n)

theorem neymanScott_pair_decomposition (x : ℝ × ℝ) (m : ℝ) :
    (x.1 - m) ^ 2 + (x.2 - m) ^ 2 =
      (x.1 - x.2) ^ 2 / 2 + 2 * (m - neymanScottMean x) ^ 2 := by
  unfold neymanScottMean
  ring

theorem neymanScott_residual_lower_bound {n : ℕ} (x : Fin n → ℝ × ℝ)
    (m : Fin n → ℝ) :
    (∑ i, ((x i).1 - (x i).2) ^ 2) / 2 ≤
      ∑ i, (((x i).1 - m i) ^ 2 + ((x i).2 - m i) ^ 2) := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  rw [neymanScott_pair_decomposition]
  nlinarith [sq_nonneg (m i - neymanScottMean (x i))]

theorem neymanScott_residual_at_mean {n : ℕ} (x : Fin n → ℝ × ℝ) :
    (∑ i, (((x i).1 - neymanScottMean (x i)) ^ 2 +
      ((x i).2 - neymanScottMean (x i)) ^ 2)) =
        (∑ i, ((x i).1 - (x i).2) ^ 2) / 2 := by
  simp_rw [neymanScott_pair_decomposition, sub_self, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero]
  exact (Finset.sum_div _ _ _).symm

theorem neymanScott_difference_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ} {m : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal m v) P) (hY : HasLaw Y (gaussianReal m v) P)
    (hind : IndepFun X Y P) :
    HasLaw (fun ω => X ω - Y ω) (gaussianReal 0 (v + v)) P := by
  refine ⟨hX.aemeasurable.sub hY.aemeasurable, ?_⟩
  simpa only [Pi.add_apply, neg_add_cancel, add_neg_cancel, sub_eq_add_neg,
    Pi.neg_apply, Function.comp_def, id_eq] using! gaussianReal_add_gaussianReal_of_indepFun
      (hind.comp measurable_id measurable_neg) hX.map_eq (gaussianReal_neg hY).map_eq

/-- The transformed observations are identically distributed even when the
 nuisance means vary with the pair index. -/
theorem neymanScott_variance_limit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ × ℝ}
    {m : ℕ → ℝ} {v : ℝ≥0} (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P)
    (h₁ : ∀ i, HasLaw (fun ω => (X i ω).1) (gaussianReal (m i) v) P)
    (h₂ : ∀ i, HasLaw (fun ω => (X i ω).2) (gaussianReal (m i) v) P)
    (hpair : ∀ i, IndepFun (fun ω => (X i ω).1) (fun ω => (X i ω).2) P) :
    ConvergesInProbability P
      (fun n ω => neymanScottVariance (fun i : Fin n => X i ω)) (fun _ => (v : ℝ) / 2) := by
  let D (i : ℕ) (ω : Ω) : ℝ := (X i ω).1 - (X i ω).2
  have hD (i) : HasLaw (D i) (gaussianReal 0 (v + v)) P :=
    neymanScott_difference_law (h₁ i) (h₂ i) (hpair i)
  have hDm (i) : Measurable (D i) := (hXm i).fst.sub (hXm i).snd
  have hi : iIndepFun D P := hind.comp (fun (_ : ℕ) (p : ℝ × ℝ) => p.1 - p.2) (by fun_prop)
  have hLp := (hD 0).hasGaussianLaw.memLp_two
  have hmean : (∫ ω, D 0 ω ∂P) = 0 := by simpa using (hD 0).integral_eq
  have hmoment : (∫ ω, (D 0 ω) ^ 2 ∂P) = 2 * (v : ℝ) := by
    have hv := (hD 0).variance_eq
    rw [variance_eq_sub hLp, hmean] at hv
    simpa [two_mul] using hv
  have hs := iid_statistic_average_limit D (fun z => z ^ 2) hDm (by fun_prop)
    hi (fun i => (hD i).identDistrib (hD 0))
    ((memLp_two_iff_integrable_sq hLp.aestronglyMeasurable).mp hLp)
  rw [hmoment] at hs
  have hc := continuous_mapping_probability_const (g := fun z : ℝ => z / 4) (by fun_prop) hs
  convert! hc using 1
  · funext n ω
    unfold neymanScottVariance
    rw [← Fin.sum_univ_eq_sum_range (fun i => (D i ω) ^ 2)]
    simp only [D]
    ring
  · funext ω
    ring

/-- Doubling the maximum-likelihood variance corrects its limiting bias. -/
theorem neymanScott_corrected_variance_consistent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ × ℝ}
    {m : ℕ → ℝ} {v : ℝ≥0} (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P)
    (h₁ : ∀ i, HasLaw (fun ω => (X i ω).1) (gaussianReal (m i) v) P)
    (h₂ : ∀ i, HasLaw (fun ω => (X i ω).2) (gaussianReal (m i) v) P)
    (hpair : ∀ i, IndepFun (fun ω => (X i ω).1) (fun ω => (X i ω).2) P) :
    ConvergesInProbability P
      (fun n ω => 2 * neymanScottVariance (fun i : Fin n => X i ω)) (fun _ => (v : ℝ)) := by
  have h := continuous_mapping_probability_const (g := fun z : ℝ => 2 * z) (by fun_prop)
    (neymanScott_variance_limit hXm hind h₁ h₂ hpair)
  simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h

/-- Positive population variance rules out consistency for the uncorrected
 estimator, by uniqueness of limits in probability. -/
theorem neymanScott_variance_inconsistent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ × ℝ}
    {m : ℕ → ℝ} {v : ℝ≥0} (hv : 0 < v) (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P)
    (h₁ : ∀ i, HasLaw (fun ω => (X i ω).1) (gaussianReal (m i) v) P)
    (h₂ : ∀ i, HasLaw (fun ω => (X i ω).2) (gaussianReal (m i) v) P)
    (hpair : ∀ i, IndepFun (fun ω => (X i ω).1) (fun ω => (X i ω).2) P) :
    ¬ ConvergesInProbability P
      (fun n ω => neymanScottVariance (fun i : Fin n => X i ω)) (fun _ => (v : ℝ)) := by
  intro h
  have he := tendstoInMeasure_ae_unique
    (neymanScott_variance_limit hXm hind h₁ h₂ hpair) h
  obtain ⟨ω, hω⟩ := he.exists
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  dsimp at hω
  linarith

/-- With at least one pair and positive population variance, the residual
 variance is positive almost surely, so the interior maximizer exists. -/
theorem neymanScott_variance_pos_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ × ℝ}
    {m : Fin n → ℝ} {v : ℝ≥0} (hv : 0 < v)
    (h₁ : ∀ i, HasLaw (fun ω => (X i ω).1) (gaussianReal (m i) v) P)
    (h₂ : ∀ i, HasLaw (fun ω => (X i ω).2) (gaussianReal (m i) v) P)
    (hpair : ∀ i, IndepFun (fun ω => (X i ω).1) (fun ω => (X i ω).2) P) :
    ∀ᵐ ω ∂P, 0 < neymanScottVariance (fun i => X i ω) := by
  let i₀ : Fin n := ⟨0, hn⟩
  have hd := neymanScott_difference_law (h₁ i₀) (h₂ i₀) (hpair i₀)
  have hpos : 0 < v + v := add_pos hv hv
  have : NullSingletonClass (gaussianReal 0 (v + v)) := nullSingletonClass_gaussianReal hpos.ne'
  have hne : ∀ᵐ z ∂gaussianReal 0 (v + v), z ≠ 0 := by
    rw [ae_iff]
    simp
  have hXne := (hd.ae_iff (show Measurable (fun z : ℝ => z ≠ 0) by measurability)).mpr hne
  filter_upwards [hXne] with ω hω
  apply div_pos _ (by positivity : 0 < 4 * (n : ℝ))
  apply Finset.sum_pos' (fun _ _ => sq_nonneg _)
  exact ⟨i₀, Finset.mem_univ _, sq_pos_of_ne_zero hω⟩

/-- The log of the actual product of the two Gaussian densities in each pair. -/
theorem neymanScott_log_density {n : ℕ} (x : Fin n → ℝ × ℝ)
    (m : Fin n → ℝ) {s : ℝ≥0} (hs : 0 < s) :
    Real.log (∏ i, gaussianPDFReal (m i) s (x i).1 * gaussianPDFReal (m i) s (x i).2) =
      -(n : ℝ) * Real.log (2 * Real.pi) - n * Real.log s -
        (∑ i, (((x i).1 - m i) ^ 2 + ((x i).2 - m i) ^ 2)) / (2 * s) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hc : (Real.sqrt (2 * Real.pi * s))⁻¹ ≠ 0 := by positivity
  have hp : 2 * Real.pi ≠ 0 := by positivity
  rw [Real.log_prod (fun i _ => (mul_pos (gaussianPDFReal_pos _ _ _ hs.ne')
    (gaussianPDFReal_pos _ _ _ hs.ne')).ne')]
  simp_rw [Real.log_mul (gaussianPDFReal_pos _ _ _ hs.ne').ne'
    (gaussianPDFReal_pos _ _ _ hs.ne').ne']
  simp only [gaussianPDFReal, Real.log_mul hc (Real.exp_ne_zero _), Real.log_exp,
    Real.log_inv, Real.log_sqrt (by positivity : 0 ≤ 2 * Real.pi * (s : ℝ)),
    Real.log_mul hp hsR.ne']
  calc
    _ = ∑ i, (-(Real.log (2 * Real.pi)) - Real.log s -
        (((x i).1 - m i) ^ 2 + ((x i).2 - m i) ^ 2) / (2 * s)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div]
      simp

/-- The profiled variance objective is globally maximized at its positive
 empirical variance, using `log t ≤ t - 1`. -/
theorem neymanScott_profile_maximum {n : ℕ} (_hn : 0 < n) {a s : ℝ}
    (ha : 0 < a) (hs : 0 < s) :
    -(n : ℝ) * Real.log s - n * a / s ≤ -(n : ℝ) * Real.log a - n := by
  have hb := Real.log_le_sub_one_of_pos (div_pos ha hs)
  rw [Real.log_div ha.ne' hs.ne'] at hb
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm := mul_le_mul_of_nonneg_left hb hnR
  rw [mul_sub, mul_sub, mul_one, ← mul_div_assoc] at hm
  linarith

/-- For a positive residual variance this is a joint global maximum over every
 nuisance mean and every positive common variance. -/
theorem neymanScott_maximizes_density {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ × ℝ)
    (ha : 0 < neymanScottVariance x) (m : Fin n → ℝ) {s : ℝ≥0} (hs : 0 < s) :
    (∏ i, gaussianPDFReal (m i) s (x i).1 * gaussianPDFReal (m i) s (x i).2) ≤
      ∏ i, gaussianPDFReal (neymanScottMean (x i)) ⟨neymanScottVariance x, ha.le⟩ (x i).1 *
        gaussianPDFReal (neymanScottMean (x i)) ⟨neymanScottVariance x, ha.le⟩ (x i).2 := by
  have haN : (0 : ℝ≥0) < ⟨neymanScottVariance x, ha.le⟩ := ha
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (∑ i, ((x i).1 - (x i).2) ^ 2) / 2 =
      2 * n * neymanScottVariance x := by
    unfold neymanScottVariance
    field_simp
    ring
  apply (Real.log_le_log_iff (Finset.prod_pos (fun i _ =>
      mul_pos (gaussianPDFReal_pos _ _ _ hs.ne') (gaussianPDFReal_pos _ _ _ hs.ne')))
    (Finset.prod_pos (fun i _ => mul_pos (gaussianPDFReal_pos _ _ _ haN.ne')
      (gaussianPDFReal_pos _ _ _ haN.ne')))).mp
  rw [neymanScott_log_density x m hs, neymanScott_log_density x _ haN,
    neymanScott_residual_at_mean, he]
  change -(n : ℝ) * Real.log (2 * Real.pi) - n * Real.log s - _ / (2 * s) ≤
    -(n : ℝ) * Real.log (2 * Real.pi) - n * Real.log (neymanScottVariance x) -
      (2 * n * neymanScottVariance x) / (2 * neymanScottVariance x)
  have hr := div_le_div_of_nonneg_right (neymanScott_residual_lower_bound x m)
    (by positivity : 0 ≤ 2 * (s : ℝ))
  rw [he] at hr
  have hmax := neymanScott_profile_maximum hn ha hsR
  have hcancel : (2 * (n : ℝ) * neymanScottVariance x) /
      (2 * neymanScottVariance x) = n := by field_simp
  have hdiv : (2 * (n : ℝ) * neymanScottVariance x) / (2 * s) =
      n * neymanScottVariance x / s := by ring
  rw [hcancel]
  rw [hdiv] at hr
  linarith

/-- If every within-pair residual vanishes, no positive common variance
 maximizes the likelihood: halving the variance at the fitted means improves it. -/
theorem neymanScott_zero_variance_no_maximum {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ × ℝ) (ha : neymanScottVariance x = 0)
    (m : Fin n → ℝ) {s : ℝ≥0} (hs : 0 < s) :
    (∏ i, gaussianPDFReal (m i) s (x i).1 * gaussianPDFReal (m i) s (x i).2) <
      ∏ i, gaussianPDFReal (neymanScottMean (x i)) (s / 2) (x i).1 *
        gaussianPDFReal (neymanScottMean (x i)) (s / 2) (x i).2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsN : (0 : ℝ≥0) < s / 2 := div_pos hs (by norm_num)
  have hz : (∑ i, ((x i).1 - (x i).2) ^ 2) = 0 := by
    unfold neymanScottVariance at ha
    exact (div_eq_zero_iff).mp ha |>.resolve_right (by positivity)
  apply (Real.log_lt_log_iff (Finset.prod_pos (fun i _ =>
      mul_pos (gaussianPDFReal_pos _ _ _ hs.ne') (gaussianPDFReal_pos _ _ _ hs.ne')))
    (Finset.prod_pos (fun i _ => mul_pos (gaussianPDFReal_pos _ _ _ hsN.ne')
      (gaussianPDFReal_pos _ _ _ hsN.ne')))).mp
  rw [neymanScott_log_density x m hs, neymanScott_log_density x _ hsN,
    neymanScott_residual_at_mean, hz]
  simp only [zero_div, sub_zero, NNReal.coe_div, NNReal.coe_ofNat]
  rw [Real.log_div hsR.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  have hres : 0 ≤ (∑ i, (((x i).1 - m i) ^ 2 + ((x i).2 - m i) ^ 2)) / (2 * s) :=
    div_nonneg (Finset.sum_nonneg (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (by positivity)
  have hp : 0 < (n : ℝ) * Real.log 2 := mul_pos hnR (Real.log_pos (by norm_num))
  nlinarith

end LectureNotes
