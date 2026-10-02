import LectureNotes.TwoSampleLindeberg

noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped Topology

/-- Centered summands for the two independent sample means. -/
def twoSampleSummand {Ω : Type*} (X Y : ℕ → Ω → ℝ) (m n : ℕ) (a b : ℝ) :
    Fin (m + n) → Ω → ℝ :=
  Fin.addCases (fun i ω => X i ω / a) (fun j ω => -(Y j ω / b))

theorem twoSampleSummand_independent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : ℕ → Ω → ℝ}
    (hind : iIndepFun (Sum.elim X Y) P) (m n : ℕ) (a b : ℝ) :
    iIndepFun (twoSampleSummand X Y m n a b) P := by
  let j : Fin (m + n) → ℕ ⊕ ℕ := fun i =>
    Sum.map Fin.val Fin.val (finSumFinEquiv.symm i)
  have hj : Function.Injective j :=
    (Fin.val_injective.sumMap Fin.val_injective).comp finSumFinEquiv.symm.injective
  let g : Fin (m + n) → ℝ → ℝ :=
    Fin.addCases (fun _ x => x / a) (fun _ x => -(x / b))
  have hgm (i : Fin (m + n)) : Measurable (g i) := by
    refine Fin.addCases ?_ ?_ i <;> intro k <;> simp only [g, Fin.addCases_left, Fin.addCases_right] <;> fun_prop
  have h := (iIndepFun.precomp hj hind).comp g hgm
  convert! h using 1
  funext i ω
  refine Fin.addCases ?_ ?_ i <;> intro k <;>
    simp [twoSampleSummand, g, j, Function.comp_def]

theorem truncSecondMoment_identDistrib {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    {X : Ω → ℝ} {Y : Ω' → ℝ} (h : IdentDistrib X Y P Q) (δ : ℝ) :
    truncSecondMoment P X δ = truncSecondMoment Q Y δ := by
  have hg : Measurable (fun x : ℝ => if δ < |x| then x ^ 2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_id.abs)
      (measurable_id.pow_const 2) measurable_const
  exact (h.comp hg).integral_eq

/-- The two-block row sum is the difference of the sample averages divided
by its theoretical standard error. -/
theorem twoSampleSummand_sum {Ω : Type*} (X Y : ℕ → Ω → ℝ)
    (m n : ℕ) (s : ℝ) (ω : Ω) :
    (∑ i, twoSampleSummand X Y m n (m * s) (n * s) i ω) =
      (sampleMean (fun i : Fin m => X i ω) - sampleMean (fun i : Fin n => Y i ω)) / s := by
  rw [Fin.sum_univ_add]
  simp only [twoSampleSummand, Fin.addCases_left, Fin.addCases_right,
    sum_neg_distrib, ← sum_div, sampleMean, Fintype.card_fin]
  ring

/-- L8's two-sample normal approximation, for centered observations and
arbitrary diverging sample sizes. The two variances may differ and no
sample-size ratio is assumed to converge. -/
theorem two_sample_centered_mean_clt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hX : MemLp (X 0) 2 P) (hY : MemLp (Y 0) 2 P)
    (hind : iIndepFun (Sum.elim X Y) P)
    (hidentX : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hmeanX : P[X 0] = 0) (hmeanY : P[Y 0] = 0)
    {vx vy : ℝ} (hvx : 0 < vx) (hvy : 0 < vy)
    (hvarX : (∫ ω, X 0 ω ^ 2 ∂P) = vx) (hvarY : (∫ ω, Y 0 ω ^ 2 ∂P) = vy)
    (m n : ℕ → ℕ) (hmpos : ∀ k, 0 < m k) (hnpos : ∀ k, 0 < n k)
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun k ω => (sampleMean (fun i : Fin (m k) => X i ω) -
        sampleMean (fun i : Fin (n k) => Y i ω)) / twoSampleStandardError (m k) (n k) vx vy) id := by
  let s (k : ℕ) := twoSampleStandardError (m k) (n k) vx vy
  let a (k : ℕ) := (m k : ℝ) * s k
  let b (k : ℕ) := (n k : ℝ) * s k
  let Z (k : ℕ) := twoSampleSummand X Y (m k) (n k) (a k) (b k)
  have hs k : 0 < s k := twoSampleStandardError_pos (hmpos k) (hnpos k) hvx hvy
  have ha k : 0 < a k := mul_pos (by exact_mod_cast hmpos k) (hs k)
  have hb k : 0 < b k := mul_pos (by exact_mod_cast hnpos k) (hs k)
  have hXall i : MemLp (X i) 2 P := (hidentX i).memLp_iff.mpr hX
  have hYall i : MemLp (Y i) 2 P := (hidentY i).memLp_iff.mpr hY
  have hzmeas k i : Measurable (Z k i) := by
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [Z, twoSampleSummand, Fin.addCases_left, Fin.addCases_right] <;> fun_prop
  have hzlp k i : MemLp (Z k i) 2 P := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [Z, twoSampleSummand, Fin.addCases_left]
      simpa only [div_eq_mul_inv] using (hXall j).mul_const (a k)⁻¹
    · intro j
      simp only [Z, twoSampleSummand, Fin.addCases_right]
      simpa only [div_eq_mul_inv, Pi.neg_apply] using! ((hYall j).mul_const (b k)⁻¹).neg
  have hzmean k i : P[Z k i] = 0 := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [Z, twoSampleSummand, Fin.addCases_left]
      rw [integral_div, (hidentX j).integral_eq, hmeanX, zero_div]
    · intro j
      simp only [Z, twoSampleSummand, Fin.addCases_right]
      rw [integral_neg, integral_div, (hidentY j).integral_eq, hmeanY, zero_div, neg_zero]
  have hxsq i : (∫ ω, X i ω ^ 2 ∂P) = vx := by
    have h := ((hidentX i).comp (measurable_id.pow_const 2)).integral_eq
    simpa only [Function.comp_def, id_eq, hvarX] using h
  have hysq i : (∫ ω, Y i ω ^ 2 ∂P) = vy := by
    have h := ((hidentY i).comp (measurable_id.pow_const 2)).integral_eq
    simpa only [Function.comp_def, id_eq, hvarY] using h
  have hzvar k : (∑ i, ∫ ω, Z k i ω ^ 2 ∂P) = 1 := by
    rw [Fin.sum_univ_add]
    simp only [Z, twoSampleSummand, Fin.addCases_left, Fin.addCases_right,
      neg_sq, div_pow, integral_div, hxsq, hysq, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    exact twoSample_variance_normalization (hmpos k) (hnpos k) hvx hvy
  have hza k : (m k : ℝ) * vx ≤ (a k) ^ 2 := by
    rw [(twoSample_scales_sq (hmpos k) (hnpos k) hvx hvy).1]
    exact le_add_of_nonneg_right (by positivity)
  have hzb k : (n k : ℝ) * vy ≤ (b k) ^ 2 := by
    rw [(twoSample_scales_sq (hmpos k) (hnpos k) hvx hvy).2]
    exact le_add_of_nonneg_right (by positivity)
  have hzlin : ∀ δ > 0, Tendsto (fun k => ∑ i, truncSecondMoment P (Z k i) δ)
      atTop (𝓝 0) := by
    intro δ hδ
    have hxlim := iid_group_lindeberg (hXm 0) hX hm ha hvx hza hδ
    have hylim := iid_group_lindeberg (hYm 0) hY hn hb hvy hzb hδ
    have hlim := hxlim.add hylim
    simp only [add_zero] at hlim
    have he k : (∑ i, truncSecondMoment P (Z k i) δ) =
        (m k : ℝ) * truncSecondMoment P (fun ω => X 0 ω / a k) δ +
        (n k : ℝ) * truncSecondMoment P (fun ω => Y 0 ω / b k) δ := by
      rw [Fin.sum_univ_add]
      simp only [Z, twoSampleSummand, Fin.addCases_left, Fin.addCases_right,
        truncSecondMoment_neg]
      have hx i : truncSecondMoment P (fun ω => X i ω / a k) δ =
          truncSecondMoment P (fun ω => X 0 ω / a k) δ :=
        truncSecondMoment_identDistrib ((hidentX i).comp (measurable_id.div_const _)) δ
      have hy i : truncSecondMoment P (fun ω => Y i ω / b k) δ =
          truncSecondMoment P (fun ω => Y 0 ω / b k) δ :=
        truncSecondMoment_identDistrib ((hidentY i).comp (measurable_id.div_const _)) δ
      simp only [hx, hy, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    simpa only [he] using hlim
  have hclt := lindeberg_feller_dependent_rows hzmeas hzlp hzmean
    (fun k => twoSampleSummand_independent hind (m k) (n k) (a k) (b k))
    (by simpa only [hzvar] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))) hzlin
  unfold ConvergesInDistribution
  convert! hclt using 1
  funext k ω
  exact (twoSampleSummand_sum X Y (m k) (n k) (s k) ω).symm

/-- The actual two-sample difference centered at the difference of population
means. Joint independence includes within-group and between-group independence. -/
theorem two_sample_mean_clt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hX : MemLp (X 0) 2 P) (hY : MemLp (Y 0) 2 P)
    (hind : iIndepFun (Sum.elim X Y) P)
    (hidentX : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hvx : 0 < Var[X 0; P]) (hvy : 0 < Var[Y 0; P])
    (m n : ℕ → ℕ) (hmpos : ∀ k, 0 < m k) (hnpos : ∀ k, 0 < n k)
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop) :
    ConvergesInDistribution P (gaussianReal 0 1)
      (fun k ω => (sampleMean (fun i : Fin (m k) => X i ω) -
        sampleMean (fun i : Fin (n k) => Y i ω) - (P[X 0] - P[Y 0])) /
          twoSampleStandardError (m k) (n k) Var[X 0; P] Var[Y 0; P]) id := by
  let Xc : ℕ → Ω → ℝ := fun i ω => X i ω - P[X 0]
  let Yc : ℕ → Ω → ℝ := fun i ω => Y i ω - P[Y 0]
  have hic : iIndepFun (Sum.elim Xc Yc) P := by
    have h := hind.comp (fun i z => z - Sum.elim (fun _ => P[X 0]) (fun _ => P[Y 0]) i)
      (fun _ => measurable_id.sub_const _)
    convert! h using 1
    funext i ω
    cases i <;> rfl
  have hxc : P[Xc 0] = 0 := by
    change (∫ ω, X 0 ω - P[X 0] ∂P) = 0
    rw [integral_sub (hX.integrable (by norm_num)) (integrable_const _)]
    simp
  have hyc : P[Yc 0] = 0 := by
    change (∫ ω, Y 0 ω - P[Y 0] ∂P) = 0
    rw [integral_sub (hY.integrable (by norm_num)) (integrable_const _)]
    simp
  have h := two_sample_centered_mean_clt (X := Xc) (Y := Yc)
    (fun i => (hXm i).sub_const _) (fun i => (hYm i).sub_const _)
    (hX.sub (memLp_const _)) (hY.sub (memLp_const _)) hic
    (fun i => (hidentX i).comp (measurable_id.sub_const _))
    (fun i => (hidentY i).comp (measurable_id.sub_const _)) hxc hyc hvx hvy
    (variance_eq_integral (hXm 0).aemeasurable).symm
    (variance_eq_integral (hYm 0).aemeasurable).symm m n hmpos hnpos hm hn
  have hcenter {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) (μ : ℝ) :
      sampleMean (fun i => x i - μ) = sampleMean x - μ := by
    have hr0 : (r : ℝ) ≠ 0 := by positivity
    simp only [sampleMean, Fintype.card_fin, sum_sub_distrib, sum_const,
      card_univ, nsmul_eq_mul]
    field_simp
  apply TendstoInDistribution.congr _ (ae_of_all _ (fun _ => rfl)) h
  intro k
  apply ae_of_all
  intro ω
  dsimp only [Xc, Yc]
  rw [hcenter (hmpos k), hcenter (hnpos k)]
  ring

end LectureNotes
