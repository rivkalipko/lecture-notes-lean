import LectureNotes.Convergence

/-! L3 stochastic order: addition, multiplication, and vanishing products. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem stochasticBigO_add {X Y : ℕ → Ω → ℝ} {a b : ℕ → ℝ}
    (hX : StochasticBigO (P := P) X a) (hY : StochasticBigO (P := P) Y b) :
    StochasticBigO (P := P) (fun n ω => X n ω + Y n ω)
      (fun n => max |a n| |b n|) := by
  refine ⟨fun n => ne_of_gt ((abs_pos.mpr (hX.1 n)).trans_le (le_max_left _ _)), ?_⟩
  intro ε hε
  obtain ⟨C, hC, hCX⟩ := hX.2 (ε / 2) (by positivity)
  obtain ⟨D, hD, hDY⟩ := hY.2 (ε / 2) (by positivity)
  refine ⟨C + D, by positivity, fun n => ?_⟩
  have hb : {ω | (C + D) * |max (|a n|) (|b n|)| < |X n ω + Y n ω|} ⊆
      {ω | C * |a n| < |X n ω|} ∪ {ω | D * |b n| < |Y n ω|} := by
    intro ω hω
    by_contra hbad
    have hx : |X n ω| ≤ C * |a n| := le_of_not_gt (fun h => hbad (Or.inl h))
    have hy : |Y n ω| ≤ D * |b n| := le_of_not_gt (fun h => hbad (Or.inr h))
    have h1 := mul_le_mul_of_nonneg_left (le_max_left |a n| |b n|) hC.le
    have h2 := mul_le_mul_of_nonneg_left (le_max_right |a n| |b n|) hD.le
    change (C + D) * |max (|a n|) (|b n|)| < |X n ω + Y n ω| at hω
    rw [abs_of_nonneg (le_trans (abs_nonneg _) (le_max_left _ _))] at hω
    linarith [abs_add_le (X n ω) (Y n ω)]
  have hm := measureReal_mono (μ := P) hb (measure_ne_top P _)
  have hu := measureReal_union_le (μ := P)
    {ω | C * |a n| < |X n ω|} {ω | D * |b n| < |Y n ω|}
  linarith [hCX n, hDY n]

theorem stochasticBigO_mul {X Y : ℕ → Ω → ℝ} {a b : ℕ → ℝ}
    (hX : StochasticBigO (P := P) X a) (hY : StochasticBigO (P := P) Y b) :
    StochasticBigO (P := P) (fun n ω => X n ω * Y n ω) (fun n => a n * b n) := by
  refine ⟨fun n => mul_ne_zero (hX.1 n) (hY.1 n), ?_⟩
  intro ε hε
  obtain ⟨C, hC, hCX⟩ := hX.2 (ε / 2) (by positivity)
  obtain ⟨D, hD, hDY⟩ := hY.2 (ε / 2) (by positivity)
  refine ⟨C * D, by positivity, fun n => ?_⟩
  have hb : {ω | C * D * |a n * b n| < |X n ω * Y n ω|} ⊆
      {ω | C * |a n| < |X n ω|} ∪ {ω | D * |b n| < |Y n ω|} := by
    intro ω hω
    by_contra hbad
    have hx : |X n ω| ≤ C * |a n| := le_of_not_gt (fun h => hbad (Or.inl h))
    have hy : |Y n ω| ≤ D * |b n| := le_of_not_gt (fun h => hbad (Or.inr h))
    have hm := mul_le_mul hx hy (abs_nonneg _) (mul_nonneg hC.le (abs_nonneg _))
    simp only [mem_setOf_eq, abs_mul] at hω
    nlinarith
  have hm := measureReal_mono (μ := P) hb (measure_ne_top P _)
  have hu := measureReal_union_le (μ := P)
    {ω | C * |a n| < |X n ω|} {ω | D * |b n| < |Y n ω|}
  linarith [hCX n, hDY n]

/-- A stochastically bounded factor times a vanishing factor vanishes. -/
theorem stochasticBigO_mul_littleO {X Y : ℕ → Ω → ℝ} {a b : ℕ → ℝ}
    (hX : StochasticBigO (P := P) X a) (hY : StochasticLittleO (P := P) Y b) :
    StochasticLittleO (P := P) (fun n ω => X n ω * Y n ω) (fun n => a n * b n) := by
  refine ⟨fun n => mul_ne_zero (hX.1 n) (hY.1 n), ?_⟩
  rw [ConvergesInProbability, tendstoInMeasure_iff_measureReal_norm]
  intro δ hδ
  apply tendsto_order.2
  constructor
  · intro l hl
    exact Eventually.of_forall (fun n => hl.trans_le ENNReal.toReal_nonneg)
  · intro ε hε
    obtain ⟨C, hC, hCX⟩ := hX.2 (ε / 2) (by positivity)
    have hy := (tendstoInMeasure_iff_measureReal_norm.mp hY.2 (δ / C) (by positivity)).eventually
      (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
    filter_upwards [hy] with n hn
    have hb : {ω | δ ≤ ‖X n ω * Y n ω / (a n * b n) - 0‖} ⊆
        {ω | C * |a n| < |X n ω|} ∪ {ω | δ / C ≤ ‖Y n ω / b n - 0‖} := by
      intro ω hω
      by_contra hbad
      have hx : |X n ω| ≤ C * |a n| := le_of_not_gt (fun h => hbad (Or.inl h))
      have hyn : ‖Y n ω / b n - 0‖ < δ / C :=
        lt_of_not_ge (fun h => hbad (Or.inr h))
      have hy : |Y n ω / b n| < δ / C := by
        simpa only [sub_zero, Real.norm_eq_abs] using hyn
      have hx' : |X n ω / a n| ≤ C := by
        rw [abs_div, div_le_iff₀ (abs_pos.mpr (hX.1 n))]
        exact hx
      have hp := mul_lt_mul_of_pos_left hy hC
      have hm := mul_le_mul_of_nonneg_right hx' (abs_nonneg (Y n ω / b n))
      simp only [mem_setOf_eq, sub_zero, Real.norm_eq_abs, mul_div_mul_comm, abs_mul] at hω
      have hcancel : C * (δ / C) = δ := by field_simp
      nlinarith
    have hm := measureReal_mono (μ := P) hb (measure_ne_top P _)
    have hu := measureReal_union_le (μ := P)
      {ω | C * |a n| < |X n ω|} {ω | δ / C ≤ ‖Y n ω / b n - 0‖}
    linarith [hCX n]

/-- Weak convergence implies the uniform-in-n stochastic boundedness used
in the lecture. Compactness of a convergent sequence makes its laws tight. -/
theorem distribution_implies_stochasticBigO {Ω' : Type*} [MeasurableSpace Ω']
    {Q : Measure Ω'} [IsProbabilityMeasure Q] {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : ConvergesInDistribution P Q X Z) :
    StochasticBigO (P := P) X (fun _ => 1) := by
  let laws : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨P.map (X n), Measure.isProbabilityMeasure_map (h.forall_aemeasurable n)⟩
  let limit : ProbabilityMeasure ℝ :=
    ⟨Q.map Z, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩
  have hc : IsCompact (closure (range laws)) :=
    h.tendsto.isCompact_insert_range.of_isClosed_subset isClosed_closure
      (closure_minimal (subset_insert limit (range laws)) h.tendsto.isCompact_insert_range.isClosed)
  have htight := isTightMeasureSet_of_isCompact_closure hc
  have hlim := tendsto_measure_norm_gt_of_isTightMeasureSet htight
  refine ⟨by simp, fun ε hε => ?_⟩
  have he : (0 : ENNReal) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hb := hlim.eventually (gt_mem_nhds he)
  obtain ⟨C, hC, hbound⟩ := ((eventually_gt_atTop (0 : ℝ)).and hb).exists
  refine ⟨C, hC, fun n => ?_⟩
  have hlt : (P.map (X n)) {x : ℝ | C < ‖x‖} < ENNReal.ofReal ε := by
    apply lt_of_le_of_lt _ hbound
    exact le_iSup_of_le (P.map (X n)) (le_iSup_of_le ⟨laws n, ⟨n, rfl⟩, rfl⟩ le_rfl)
  rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n)
    (measurableSet_lt measurable_const measurable_norm)] at hlt
  have hr := (ENNReal.toReal_lt_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top).mpr hlt
  simpa only [abs_one, mul_one, ENNReal.toReal_ofReal hε.le, measureReal_def,
    mem_preimage, mem_setOf_eq, preimage_setOf_eq, Real.norm_eq_abs] using hr

theorem stochasticLittleO_isBigO {X : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (hXm : ∀ n, AEMeasurable (X n) P)
    (hX : StochasticLittleO (P := P) X a) : StochasticBigO (P := P) X a := by
  have hb := distribution_implies_stochasticBigO
    (probability_implies_distribution (fun n => (hXm n).div_const (a n)) hX.2)
  refine ⟨hX.1, fun ε hε => ?_⟩
  obtain ⟨C, hC, htail⟩ := hb.2 ε hε
  refine ⟨C, hC, fun n => ?_⟩
  have he (ω) : C * |a n| < |X n ω| ↔ C < |X n ω / a n| := by
    rw [abs_div, lt_div_iff₀ (abs_pos.mpr (hX.1 n))]
  simpa only [he, abs_one, mul_one] using htail n

theorem stochasticBigO_normalize {X : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (hX : StochasticBigO (P := P) X a) :
    StochasticBigO (P := P) (fun n ω => X n ω / a n) (fun _ => 1) := by
  refine ⟨by simp, fun ε hε => ?_⟩
  obtain ⟨C, hC, htail⟩ := hX.2 ε hε
  refine ⟨C, hC, fun n => ?_⟩
  simpa only [abs_one, mul_one, abs_div, lt_div_iff₀ (abs_pos.mpr (hX.1 n))] using htail n

/-- In particular, Op(n^-δ) is op(1) when δ > 0, because its scale tends to zero. -/
theorem stochasticBigO_vanishing_scale {X : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (hX : StochasticBigO (P := P) X a) (ha : Tendsto a atTop (𝓝 0)) :
    StochasticLittleO (P := P) X (fun _ => 1) := by
  have ha' : StochasticLittleO (P := P) (fun n _ => a n) (fun _ => 1) := by
    refine ⟨by simp, ?_⟩
    simp only [div_one]
    exact almost_sure_implies_probability (fun _ => aemeasurable_const)
      (ae_of_all _ (fun _ => ha))
  have hp := stochasticBigO_mul_littleO (stochasticBigO_normalize hX) ha'
  simpa only [one_mul, div_mul_cancel₀ _ (hX.1 _)] using hp

theorem stochasticBigO_add_littleO {X Y : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (hX : StochasticBigO (P := P) X a) (hYm : ∀ n, AEMeasurable (Y n) P)
    (hY : StochasticLittleO (P := P) Y a) :
    StochasticBigO (P := P) (fun n ω => X n ω + Y n ω) a := by
  have hp := stochasticBigO_add hX (stochasticLittleO_isBigO hYm hY)
  exact ⟨hX.1, by simpa only [max_self, abs_abs] using hp.2⟩

theorem probability_difference_isLittleO {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (h : ConvergesInProbability P X Y) :
    StochasticLittleO (P := P) (fun n ω => X n ω - Y ω) (fun _ => 1) := by
  refine ⟨by simp, ?_⟩
  simpa only [ConvergesInProbability, tendstoInMeasure_iff_norm, div_one, sub_zero] using h
end LectureNotes
