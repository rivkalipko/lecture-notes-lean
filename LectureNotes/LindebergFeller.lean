import LectureNotes.LindebergBounds

set_option autoImplicit false

/-! The Lindeberg central limit theorem for finite, non-identically distributed
rows. Variables are centered and row second-moment sums tend to one. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

private theorem tendsto_zero_of_small_asymptotic_upper_bounds {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n)
    (h : ∀ ε > 0, ∃ (b : ℕ → ℝ) (l : ℝ),
      Tendsto b atTop (𝓝 l) ∧ l < ε ∧ ∀ᶠ n in atTop, a n ≤ b n) :
    Tendsto a atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨b, l, hb, hl, hab⟩ := h ε hε
  filter_upwards [hab, (tendsto_order.mp hb).2 ε hl] with n hn hn'
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (ha n)] using hn.trans_lt hn'

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {m : ℕ → ℕ} {X : (n : ℕ) → Fin (m n) → Ω → ℝ}

/-- Lindeberg's condition makes every row member negligible uniformly over
the row. For centered rows these second moments are the variances. -/
theorem lindeberg_asymptotic_negligibility
    (hXm : ∀ n i, Measurable (X n i)) (hX : ∀ n i, MemLp (X n i) 2 P)
    (hlin : ∀ δ > 0, Tendsto (fun n => ∑ i, truncSecondMoment P (X n i) δ)
      atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i, (∫ ω, X n i ω ^ 2 ∂P) < ε := by
  classical
  intro ε hε
  let δ := Real.sqrt (ε / 2)
  have hδ : 0 < δ := Real.sqrt_pos.mpr (half_pos hε)
  have hδsq : δ ^ 2 = ε / 2 := Real.sq_sqrt (half_pos hε).le
  filter_upwards [(tendsto_order.mp (hlin δ hδ)).2 (ε / 2) (half_pos hε)] with n hn
  intro i
  have hi : truncSecondMoment P (X n i) δ ≤ ∑ j, truncSecondMoment P (X n j) δ := by
    apply Finset.single_le_sum (s := Finset.univ) (a := i)
      (f := fun j : Fin (m n) => truncSecondMoment P (X n j) δ)
    · intro j _
      exact truncSecondMoment_nonneg _ _
    · exact Finset.mem_univ i
  have hh := secondMoment_le_truncation (hXm n i) (hX n i) hδ
  linarith

/-- The Lindeberg condition makes the sum of squared row variances vanish. -/
theorem lindeberg_sum_squared_secondMoments
    (hXm : ∀ n i, Measurable (X n i)) (hX : ∀ n i, MemLp (X n i) 2 P)
    (hvar : Tendsto (fun n => ∑ i, ∫ ω, X n i ω ^ 2 ∂P) atTop (𝓝 1))
    (hlin : ∀ δ > 0, Tendsto (fun n => ∑ i, truncSecondMoment P (X n i) δ)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∑ i, (∫ ω, X n i ω ^ 2 ∂P) ^ 2) atTop (𝓝 0) := by
  classical
  let v (n : ℕ) (i : Fin (m n)) := ∫ ω, X n i ω ^ 2 ∂P
  have hv n i : 0 ≤ v n i := integral_nonneg (fun _ => sq_nonneg _)
  apply tendsto_zero_of_small_asymptotic_upper_bounds
  · intro n
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  intro ε hε
  let δ := Real.sqrt (ε / 2)
  have hδ : 0 < δ := Real.sqrt_pos.mpr (half_pos hε)
  have hδsq : δ ^ 2 = ε / 2 := Real.sq_sqrt (half_pos hε).le
  refine ⟨fun n => (δ ^ 2 + ∑ i, truncSecondMoment P (X n i) δ) * ∑ i, v n i,
    δ ^ 2, ?_, by linarith, .of_forall (fun n => ?_)⟩
  · simpa only [add_zero, mul_one] using ((hlin δ hδ).const_add (δ ^ 2)).mul hvar
  · calc
      ∑ i, v n i ^ 2 ≤ ∑ i, (δ ^ 2 + ∑ j, truncSecondMoment P (X n j) δ) * v n i := by
        apply Finset.sum_le_sum
        intro i _
        have hi : truncSecondMoment P (X n i) δ ≤ ∑ j, truncSecondMoment P (X n j) δ := by
          apply Finset.single_le_sum (s := Finset.univ) (a := i)
            (f := fun j : Fin (m n) => truncSecondMoment P (X n j) δ)
          · intro j _
            exact truncSecondMoment_nonneg _ _
          · exact Finset.mem_univ i
        have hh := secondMoment_le_truncation (hXm n i) (hX n i) hδ
        have hbound : v n i ≤ δ ^ 2 + ∑ j, truncSecondMoment P (X n j) δ := by
          exact hh.trans (by linarith)
        simpa only [pow_two] using mul_le_mul_of_nonneg_right hbound (hv n i)
      _ = _ := (Finset.mul_sum ..).symm

/-- Pointwise convergence of row-sum characteristic functions, proved by
replacement with Gaussian factors and the Lindeberg truncation bound. -/
theorem lindeberg_charFun_tendsto
    (hXm : ∀ n i, Measurable (X n i)) (hX : ∀ n i, MemLp (X n i) 2 P)
    (hmean : ∀ n i, (∫ ω, X n i ω ∂P) = 0)
    (hind : ∀ n, iIndepFun (X n) P)
    (hvar : Tendsto (fun n => ∑ i, ∫ ω, X n i ω ^ 2 ∂P) atTop (𝓝 1))
    (hlin : ∀ δ > 0, Tendsto (fun n => ∑ i, truncSecondMoment P (X n i) δ)
      atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => charFun (P.map (fun ω => ∑ i, X n i ω)) t)
      atTop (𝓝 (charFun (gaussianReal 0 1) t)) := by
  classical
  let v (n : ℕ) (i : Fin (m n)) := ∫ ω, X n i ω ^ 2 ∂P
  let f (n : ℕ) (i : Fin (m n)) := charFun (P.map (X n i)) t
  let g (n : ℕ) (i : Fin (m n)) := Complex.exp (-(t : ℂ) ^ 2 * v n i / 2)
  have hv n i : 0 ≤ v n i := integral_nonneg (fun _ => sq_nonneg _)
  have hf n i : ‖f n i‖ ≤ 1 := by
    letI : IsProbabilityMeasure (P.map (X n i)) := Measure.isProbabilityMeasure_map (hXm n i).aemeasurable
    exact norm_charFun_le_one t
  have hg n i : ‖g n i‖ ≤ 1 := by
    have he : -(t : ℂ) ^ 2 * v n i / 2 = ((-(t ^ 2 * v n i / 2) : ℝ) : ℂ) := by
      push_cast
      ring
    dsimp only [g]
    rw [he, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (div_nonneg (mul_nonneg (sq_nonneg t) (hv n i)) (by norm_num))
  have herr : Tendsto (fun n => ∑ i, ‖f n i - g n i‖) atTop (𝓝 0) := by
    apply tendsto_zero_of_small_asymptotic_upper_bounds
    · intro n
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    intro ε hε
    let δ := ε / (2 * (|t| ^ 3 + 1))
    have ht : 0 ≤ |t| ^ 3 := pow_nonneg (abs_nonneg _) _
    have hden : 0 < 2 * (|t| ^ 3 + 1) := by positivity
    have hδ : 0 < δ := div_pos hε hden
    have hsmall : |t| ^ 3 * δ < ε := by
      dsimp [δ]
      rw [← mul_div_assoc, div_lt_iff₀ hden]
      nlinarith
    refine ⟨fun n => |t| ^ 3 * δ * (∑ i, v n i) +
      2 * t ^ 2 * (∑ i, truncSecondMoment P (X n i) δ) +
      t ^ 4 * (∑ i, v n i ^ 2), |t| ^ 3 * δ, ?_, hsmall, .of_forall (fun n => ?_)⟩
    · simpa only [mul_one, mul_zero, add_zero] using
        ((hvar.const_mul (|t| ^ 3 * δ)).add
          ((hlin δ hδ).const_mul (2 * t ^ 2))).add
          ((lindeberg_sum_squared_secondMoments hXm hX hvar hlin).const_mul (t ^ 4))
    · calc
        _ ≤ ∑ i, (|t| ^ 3 * δ * v n i + 2 * t ^ 2 * truncSecondMoment P (X n i) δ +
          t ^ 4 * v n i ^ 2) := Finset.sum_le_sum (fun i _ =>
            charFun_gaussian_error_bound (hXm n i) (hX n i) (hmean n i) t hδ)
        _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hdiff : Tendsto (fun n => (∏ i, f n i) - ∏ i, g n i) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ herr
    intro n
    exact norm_prod_sub_prod_le_sum Finset.univ (f n) (g n) (fun i _ => hf n i) (fun i _ => hg n i)
  have hgauss : Tendsto (fun n => ∏ i, g n i) atTop
      (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hvar
    have he := ((hc.const_mul (-(t : ℂ) ^ 2)).div_const (2 : ℂ)).cexp
    convert! he using 1
    · funext n
      simp only [g, v, Function.comp_apply, ← Complex.exp_sum, ← Finset.sum_div,
        ← Finset.mul_sum, Complex.ofReal_sum]
    · simp only [Complex.ofReal_one, mul_one]
  have htotal := hdiff.add hgauss
  simp only [sub_add_cancel, zero_add] at htotal
  convert! htotal using 1
  · funext n
    simpa only [f, Finset.prod_apply] using congrFun
      ((hind n).charFun_map_fun_sum_eq_prod (fun i => (hXm n i).aemeasurable)) t
  · simp [charFun_gaussianReal, neg_div]

/-- Lindeberg's central limit theorem for triangular arrays. No identical-law
assumption or convergence conclusion is included among the hypotheses. -/
theorem lindeberg_feller_triangular_array
    (hXm : ∀ n i, Measurable (X n i)) (hX : ∀ n i, MemLp (X n i) 2 P)
    (hmean : ∀ n i, (∫ ω, X n i ω ∂P) = 0)
    (hind : ∀ n, iIndepFun (X n) P)
    (hvar : Tendsto (fun n => ∑ i, ∫ ω, X n i ω ^ 2 ∂P) atTop (𝓝 1))
    (hlin : ∀ δ > 0, Tendsto (fun n => ∑ i, truncSecondMoment P (X n i) δ)
      atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω => ∑ i, X n i ω) atTop id (fun _ => P)
      (gaussianReal 0 1) where
  forall_aemeasurable n := (Finset.measurable_sum _ (fun i _ => hXm n i)).aemeasurable
  tendsto := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
    intro t
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using
      lindeberg_charFun_tendsto hXm hX hmean hind hvar hlin t

/-- L3 Theorem 13 in the sequence notation of the notes. The normalization
is explicitly eventually positive, as needed for the displayed quotient. -/
theorem lindeberg_feller_sequence {Z : ℕ → Ω → ℝ} (c : ℕ → ℝ)
    (hZm : ∀ i, Measurable (Z i)) (hZ : ∀ i, MemLp (Z i) 2 P)
    (hind : iIndepFun Z P)
    (hc : ∀ᶠ n in atTop, 0 < c n)
    (hcsq : ∀ n, c n ^ 2 = ∑ i ∈ Finset.range n, Var[Z i; P])
    (hlin : ∀ ε > 0,
      Tendsto (fun n => (c n ^ 2)⁻¹ * ∑ i ∈ Finset.range n,
        ∫ ω, if ε * c n < |Z i ω - P[Z i]| then (Z i ω - P[Z i]) ^ 2 else 0 ∂P)
        atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n ω => (∑ i ∈ Finset.range n, (Z i ω - P[Z i])) / c n)
      atTop id (fun _ => P) (gaussianReal 0 1) := by
  classical
  let Y (n : ℕ) (i : Fin n) (ω : Ω) := (Z i ω - P[Z i]) / c n
  have hYm n i : Measurable (Y n i) := ((hZm i).sub measurable_const).div_const _
  have hY n i : MemLp (Y n i) 2 P := by
    simpa only [Y, div_eq_mul_inv, Pi.sub_apply] using
      ((hZ i).sub (memLp_const _)).mul_const ((c n)⁻¹)
  have hmean n i : (∫ ω, Y n i ω ∂P) = 0 := by
    rw [show Y n i = fun ω => (Z i ω - P[Z i]) / c n from rfl,
      integral_div, integral_sub ((hZ i).integrable (by norm_num)) (integrable_const _)]
    simp
  have hYi n : iIndepFun (Y n) P := by
    exact (hind.precomp (g := fun i : Fin n => (i : ℕ)) Fin.val_injective).comp
      (fun i z => (z - P[Z i]) / c n) (fun _ => by fun_prop)
  have hvar : Tendsto (fun n => ∑ i, ∫ ω, Y n i ω ^ 2 ∂P) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hc] with n hn
    have he (i : Fin n) : (∫ ω, Y n i ω ^ 2 ∂P) = Var[Z i; P] / c n ^ 2 := by
      simp only [Y, div_pow, integral_div, ← variance_eq_integral (hZm i).aemeasurable]
    simp_rw [he]
    rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun i => Var[Z i; P]) n, ← hcsq n]
    exact (div_self (pow_ne_zero 2 hn.ne')).symm
  have hlinY : ∀ ε > 0, Tendsto (fun n => ∑ i, truncSecondMoment P (Y n i) ε)
      atTop (𝓝 0) := by
    intro ε hε
    apply (hlin ε hε).congr'
    filter_upwards [hc] with n hn
    have he (i : Fin n) : truncSecondMoment P (Y n i) ε =
        (∫ ω, if ε * c n < |Z i ω - P[Z i]| then (Z i ω - P[Z i]) ^ 2 else 0 ∂P) /
          c n ^ 2 := by
      rw [← integral_div]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      simp only [Y, abs_div, abs_of_pos hn, lt_div_iff₀ hn, div_pow]
      split_ifs <;> simp
    simp_rw [he]
    rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range
      (fun i => ∫ ω, if ε * c n < |Z i ω - P[Z i]| then (Z i ω - P[Z i]) ^ 2 else 0 ∂P) n]
    ring
  have h := lindeberg_feller_triangular_array hYm hY hmean hYi hvar hlinY
  apply h.congr _ (Filter.EventuallyEq.rfl)
  intro n
  exact Filter.Eventually.of_forall (fun ω => by
    simp only [Y, ← Finset.sum_div,
      Fin.sum_univ_eq_sum_range (fun i => Z i ω - P[Z i]) n])

end LectureNotes
