import LectureNotes.BootstrapMoments
import LectureNotes.IIDScoreAsymptotics
import LectureNotes.BoundaryNormalMLE

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- Finite-sample algebra behind the variance-estimator CLT, including the
empty-sample convention after multiplication by the square-root rate. -/
theorem empiricalVariance_normalized_decomposition {n : ℕ} (x : Fin n → ℝ) (μ v : ℝ) :
    Real.sqrt n * (empiricalVariance x - v) =
      Real.sqrt n * sampleMean (fun i => (x i - μ) ^ 2 - v) -
        (Real.sqrt n * sampleMean (fun i => x i - μ)) * sampleMean (fun i => x i - μ) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hs := sum_squared_error_decomposition (Nat.pos_of_ne_zero hn) x μ
  have hsum : sampleMean (fun i => x i - μ) = sampleMean x - μ := by
    simp only [sampleMean, Fintype.card_fin, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hvsum : sampleMean (fun i => (x i - μ) ^ 2 - v) =
      ((∑ i, (x i - μ) ^ 2) / n) - v := by
    simp only [sampleMean, Fintype.card_fin, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [hsum, hvsum, hs]
  unfold empiricalVariance
  field_simp
  ring

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- The empirical-variance CLT under a finite fourth central moment.
Its Gaussian variance is the variance of the squared centered observation. -/
theorem empiricalVariance_clt {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hfour : Integrable (fun ω => (X 0 ω - P[X 0]) ^ 4) P)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P].toNNReal) Q) :
    ConvergesInDistribution P Q
      (fun n ω => Real.sqrt n * (empiricalVariance (fun i : Fin n => X i ω) - Var[X 0; P])) Z := by
  let μ := P[X 0]
  let v := Var[X 0; P]
  let g (x : ℝ) := x - μ
  let h (x : ℝ) := (x - μ) ^ 2 - v
  have hgm : Measurable g := by dsimp [g]; fun_prop
  have hhm : Measurable h := by dsimp [h]; fun_prop
  have hgp : MemLp (fun ω => g (X 0 ω)) 2 P := hX.sub (memLp_const _)
  have hg0 : (∫ ω, g (X 0 ω) ∂P) = 0 := by
    rw [show (fun ω => g (X 0 ω)) = fun ω => X 0 ω - μ from rfl,
      integral_sub (hX.integrable (by norm_num)) (integrable_const _)]
    simp [μ]
  have hsquare : MemLp (fun ω => (X 0 ω - μ) ^ 2) 2 P := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    simpa only [μ, ← pow_mul] using hfour
  have hhp : MemLp (fun ω => h (X 0 ω)) 2 P := hsquare.sub (memLp_const _)
  have hh0 : (∫ ω, h (X 0 ω) ∂P) = 0 := by
    rw [show (fun ω => h (X 0 ω)) = fun ω => (X 0 ω - μ) ^ 2 - v from rfl,
      integral_sub (hgp.integrable_sq) (integrable_const _)]
    rw [← variance_eq_integral (hXm 0).aemeasurable]
    simp [v]
  have hgv : Var[fun ω => g (X 0 ω); P] = (Var[X 0; P].toNNReal : ℝ) := by
    rw [show (fun ω => g (X 0 ω)) = fun ω => X 0 ω - μ from rfl, variance_sub_const (hXm 0).aestronglyMeasurable]
    exact (Real.coe_toNNReal _ (variance_nonneg _ _)).symm
  have hhv : Var[fun ω => h (X 0 ω); P] =
      (Var[fun ω => (X 0 ω - μ) ^ 2; P].toNNReal : ℝ) := by
    rw [show (fun ω => h (X 0 ω)) = fun ω => (X 0 ω - μ) ^ 2 - v from rfl, variance_sub_const hsquare.aestronglyMeasurable]
    exact (Real.coe_toNNReal _ (variance_nonneg _ _)).symm
  have hG := iid_zero_mean_score_clt X g hgm hind hident hgp hg0 hgv
    (HasLaw.id : HasLaw id (gaussianReal 0 Var[X 0; P].toNNReal)
      (gaussianReal 0 Var[X 0; P].toNNReal))
  have hH := iid_zero_mean_score_clt X h hhm hind hident hhp hh0 hhv hZ
  have hB : ConvergesInProbability P
      (fun n ω => (∑ i ∈ Finset.range n, g (X i ω)) / n) (fun _ => 0) := by
    simpa only [hg0] using iid_statistic_average_limit X g hXm hgm hind hident
      (hgp.integrable (by norm_num))
  have hBm n : AEMeasurable (fun ω => (∑ i ∈ Finset.range n, g (X i ω)) / n) P :=
    ((Finset.measurable_sum _ (fun i _ => hgm.comp (hXm i))).div_const (n : ℝ)).aemeasurable
  have hprod := slutsky_mul_zero hG hB hBm
  have hneg : ConvergesInProbability P
      (fun n ω => -(Real.sqrt n * ((∑ i ∈ Finset.range n, g (X i ω)) / n) *
        ((∑ i ∈ Finset.range n, g (X i ω)) / n))) (fun _ => 0) := by
    simpa only [neg_zero] using continuous_mapping_probability_const
      (g := fun x : ℝ => -x) (by fun_prop) hprod
  have hlim := slutsky_add hH hneg (fun n => (((hBm n).const_mul (Real.sqrt n)).mul (hBm n)).neg)
  simp only [add_zero] at hlim
  convert! hlim using 1
  funext n ω
  rw [empiricalVariance_normalized_decomposition _ μ v]
  simp only [sampleMean, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => (X i ω - μ) ^ 2 - v) n,
    Fin.sum_univ_eq_sum_range (fun i => X i ω - μ) n]
  simp only [h, g]
  ring

/-- The limiting variance is fourth central moment minus squared variance. -/
theorem squared_centered_variance {X : Ω → ℝ} (hXm : Measurable X)
    (hX : MemLp X 2 P) (hfour : Integrable (fun ω => (X ω - P[X]) ^ 4) P) :
    Var[fun ω => (X ω - P[X]) ^ 2; P] = (∫ ω, (X ω - P[X]) ^ 4 ∂P) - Var[X; P] ^ 2 := by
  have hsq : MemLp (fun ω => (X ω - P[X]) ^ 2) 2 P := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    simpa only [← pow_mul] using hfour
  rw [variance_eq_second_moment_sub_mean_sq P hsq,
    ← variance_eq_integral hXm.aemeasurable]
  simp only [← pow_mul]

/-- The n-1 and n denominators differ by the usual deterministic factor. -/
theorem sampleVariance_eq_scaled_empiricalVariance {n : ℕ} (hn : 1 < n) (x : Fin n → ℝ) :
    sampleVariance x = (n : ℝ) / (n - 1) * empiricalVariance x := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  unfold sampleVariance empiricalVariance
  field_simp

/-- L5 Example 7 for the unbiased sample variance, with only second moments. -/
theorem sampleVariance_strong_consistency {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ConvergesAlmostSurely P (fun n ω => sampleVariance (fun i : Fin n => X i ω))
      (fun _ => Var[X 0; P]) := by
  have hr : Tendsto (fun n : ℕ => (n : ℝ) / (n - 1)) atTop (𝓝 1) := by
    simpa only [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)
  filter_upwards [empiricalVariance_strong_consistency hXm hX hind hident] with ω hω
  have hh := hr.mul hω
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  exact (sampleVariance_eq_scaled_empiricalVariance hn _).symm

/-- L5 Example 8: the unbiased sample variance has the same fourth-moment
Gaussian limit as the empirical central second moment. -/
theorem sampleVariance_clt {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hfour : Integrable (fun ω => (X 0 ω - P[X 0]) ^ 4) P)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 Var[fun ω => (X 0 ω - P[X 0]) ^ 2; P].toNNReal) Q) :
    ConvergesInDistribution P Q
      (fun n ω => Real.sqrt n * (sampleVariance (fun i : Fin n => X i ω) - Var[X 0; P])) Z := by
  let v := Var[X 0; P]
  have hr : Tendsto (fun n : ℕ => (n : ℝ) / (n - 1)) atTop (𝓝 1) := by
    simpa only [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)
  have hi : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hrem : Tendsto (fun n : ℕ => Real.sqrt n / (n - 1) * v) atTop (𝓝 0) := by
    have hh := (hi.mul hr).mul_const v
    simp only [zero_mul] at hh
    apply hh.congr
    intro n
    by_cases hn : n = 0
    · subst n; simp
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).ne'
    have hsq := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have he : (Real.sqrt n)⁻¹ * ((n : ℝ) / (n - 1)) = Real.sqrt n / (n - 1) := by
      have hc : (Real.sqrt n)⁻¹ * (n : ℝ) = Real.sqrt n := by
        calc
          _ = (Real.sqrt n)⁻¹ * (Real.sqrt n * Real.sqrt n) := by rw [← pow_two, hsq]
          _ = _ := inv_mul_cancel_left₀ hs _
      rw [div_eq_mul_inv, ← mul_assoc, hc, div_eq_mul_inv]
    rw [he]
  have hrp : ConvergesInProbability P (fun n _ => (n : ℝ) / (n - 1)) (fun _ => 1) :=
    almost_sure_implies_probability (fun _ => aemeasurable_const) (ae_of_all _ (fun _ => hr))
  have hremp : ConvergesInProbability P (fun n _ => Real.sqrt n / (n - 1) * v) (fun _ => 0) :=
    almost_sure_implies_probability (fun _ => aemeasurable_const) (ae_of_all _ (fun _ => hrem))
  have hh := slutsky_add (slutsky_mul (empiricalVariance_clt hXm hX hind hident hfour hZ)
    hrp (fun _ => aemeasurable_const)) hremp (fun _ => aemeasurable_const)
  simp only [mul_one, add_zero] at hh
  have hstat (n : ℕ) : AEMeasurable (fun ω => Real.sqrt n *
      (sampleVariance (fun i : Fin n => X i ω) - v)) P := by
    unfold sampleVariance sampleMean
    fun_prop
  refine ⟨hstat, hZ.aemeasurable, ?_⟩
  apply hh.tendsto.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  apply Subtype.ext
  apply Measure.map_congr
  apply ae_of_all
  intro ω
  dsimp only
  rw [sampleVariance_eq_scaled_empiricalVariance hn]
  dsimp only [v]
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hd : (n : ℝ) - 1 ≠ 0 := (sub_pos.mpr hnR).ne'
  field_simp
  ring

end LectureNotes
