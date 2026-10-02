import LectureNotes.Testing
import LectureNotes.QuantileMeasurability
import LectureNotes.PowerAnalysis

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- Upper-tail p-value relative to a continuous null distribution. -/
def upperTailPValue (μ : Measure ℝ) {Ω : Type*} (T : Ω → ℝ) (ω : Ω) : ℝ :=
  1 - cdf μ (T ω)

theorem upperTailPValue_measurable (μ : Measure ℝ) {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → ℝ} (hT : Measurable T) : Measurable (upperTailPValue μ T) :=
  measurable_const.sub ((monotone_cdf μ).measurable.comp hT)

theorem upperTailPValue_mem (μ : Measure ℝ) {Ω : Type*} (T : Ω → ℝ) (ω : Ω) :
    upperTailPValue μ T ω ∈ Icc (0 : ℝ) 1 := by
  dsimp [upperTailPValue]
  constructor <;> linarith [cdf_nonneg μ (T ω), cdf_le_one μ (T ω)]

/-- Exact interior calibration, allowing bounded supports and flat portions
of the continuous null CDF. -/
theorem upperTailPValue_exact {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure ℝ}
    [IsProbabilityMeasure μ] [NullSingletonClass μ] {T : Ω → ℝ}
    (hT : HasLaw T μ P) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    P.real {ω | upperTailPValue μ T ω ≤ α} = α := by
  have hq : 1-α ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have he : {ω | upperTailPValue μ T ω ≤ α} =
      {ω | T ω ∈ Ici (distributionQuantile μ (1-α))} := by
    ext ω
    simp only [mem_setOf_eq, mem_Ici, distributionQuantile_le_iff μ hq, upperTailPValue]
    constructor <;> intro h <;> linarith
  rw [he]
  change P.real {ω | distributionQuantile μ (1-α) ≤ T ω} = α
  rw [hT.measureReal_eq measurableSet_Ici]
  change μ.real (Ici (distributionQuantile μ (1-α))) = α
  rw [← measureReal_congr Ioi_ae_eq_Ici]
  have hec : Ioi (distributionQuantile μ (1-α)) = (Iic (distributionQuantile μ (1-α)))ᶜ := by
    ext t; simp
  rw [hec, measureReal_compl measurableSet_Iic, probReal_univ,
    distributionQuantile_exact μ _ hq]
  ring

/-- Exact continuous-null p-values satisfy the repository's validity
criterion, including the endpoint significance levels zero and one. -/
theorem upperTailPValue_valid {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure ℝ}
    [IsProbabilityMeasure μ] [NullSingletonClass μ] {T : Ω → ℝ}
    (hTm : Measurable T) (hT : HasLaw T μ P) :
    IsValidPValue (upperTailPValue μ T) (fun _ : Unit => P) univ := by
  refine ⟨upperTailPValue_measurable μ hTm, upperTailPValue_mem μ T, ?_⟩
  intro _ _ α hα
  by_cases hz : α = 0
  · subst α
    apply le_of_forall_pos_le_add
    intro ε hε
    let a := min (ε/2) (1/2 : ℝ)
    have ha : a ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact lt_min (by positivity) (by norm_num)
      · exact (min_le_right _ _).trans_lt (by norm_num)
    have hm := measureReal_mono (μ := P)
      (show {ω | upperTailPValue μ T ω ≤ 0} ⊆ {ω | upperTailPValue μ T ω ≤ a} from
        fun ω h => show upperTailPValue μ T ω ≤ a from h.trans ha.1.le)
      (measure_ne_top P _)
    rw [upperTailPValue_exact hT ha] at hm
    have ham : a ≤ ε := (min_le_left _ _).trans (by linarith)
    simpa only [zero_add] using hm.trans ham
  · by_cases ho : α = 1
    · subst α
      exact measureReal_le_one
    · exact (upperTailPValue_exact hT ⟨lt_of_le_of_ne hα.1 (Ne.symm hz),
        lt_of_le_of_ne hα.2 ho⟩).le


/-- Bonferroni combination of two valid p-values. No independence is needed. -/
theorem twoTailPValue_valid {Ω Θ : Type*} [MeasurableSpace Ω]
    {P : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (P θ)] {H : Set Θ}
    {p q : Ω → ℝ} (hp : IsValidPValue p P H) (hq : IsValidPValue q P H) :
    IsValidPValue (fun ω => min 1 (2 * min (p ω) (q ω))) P H := by
  refine ⟨measurable_const.min (measurable_const.mul (hp.1.min hq.1)), ?_, ?_⟩
  · intro ω
    exact ⟨le_min zero_le_one (mul_nonneg (by norm_num) (le_min (hp.2.1 ω).1 (hq.2.1 ω).1)),
      min_le_left _ _⟩
  · intro θ hθ α hα
    by_cases ha1 : α = 1
    · subst α
      exact measureReal_le_one
    have ha : α < 1 := lt_of_le_of_ne hα.2 ha1
    have hb : α/2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
    have he : {ω | min 1 (2 * min (p ω) (q ω)) ≤ α} =
        {ω | p ω ≤ α/2} ∪ {ω | q ω ≤ α/2} := by
      ext ω
      simp only [mem_setOf_eq, mem_union, min_le_iff]
      constructor
      · rintro (h | h)
        · exact (not_le_of_gt ha h).elim
        · have hm : min (p ω) (q ω) ≤ α/2 := by linarith
          exact min_le_iff.mp hm
      · intro h
        right
        have hm := min_le_iff.mpr h
        linarith
    rw [he]
    have hu := measureReal_union_le (μ := P θ) {ω | p ω ≤ α/2} {ω | q ω ≤ α/2}
    linarith [hp.2.2 θ hθ (α/2) hb, hq.2.2 θ hθ (α/2) hb]

/-- The two-sided normal p-value printed in L8. -/
def normalTwoSidedPValue {Ω : Type*} (T : Ω → ℝ) (ω : Ω) : ℝ :=
  2 * (1 - cdf (gaussianReal 0 1) |T ω|)

theorem normalTwoSidedPValue_eq_two_tails {Ω : Type*} (T : Ω → ℝ) (ω : Ω) :
    normalTwoSidedPValue T ω =
      min 1 (2 * min (upperTailPValue (gaussianReal 0 1) T ω)
        (upperTailPValue (gaussianReal 0 1) (fun ω => -T ω) ω)) := by
  have hhalf : cdf (gaussianReal 0 1) 0 = 1/2 := by
    have h := standardNormal_cdf_neg 0
    rw [neg_zero] at h
    linarith
  unfold normalTwoSidedPValue upperTailPValue
  rw [standardNormal_cdf_neg]
  by_cases ht : 0 ≤ T ω
  · rw [abs_of_nonneg ht]
    have h := (monotone_cdf (gaussianReal 0 1)) ht
    rw [hhalf] at h
    have he : min (1-cdf (gaussianReal 0 1) (T ω)) (1-(1-cdf (gaussianReal 0 1) (T ω))) =
        1-cdf (gaussianReal 0 1) (T ω) := min_eq_left (by linarith)
    rw [he, min_eq_right (by linarith)]
  · have ht' : T ω ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht', standardNormal_cdf_neg]
    have h := (monotone_cdf (gaussianReal 0 1)) ht'
    rw [hhalf] at h
    have he : min (1-cdf (gaussianReal 0 1) (T ω)) (1-(1-cdf (gaussianReal 0 1) (T ω))) =
        1-(1-cdf (gaussianReal 0 1) (T ω)) := min_eq_right (by linarith)
    rw [he, min_eq_right (by linarith)]

theorem normalTwoSidedPValue_valid {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → ℝ}
    (hTm : Measurable T) (hT : HasLaw T (gaussianReal 0 1) P) :
    IsValidPValue (normalTwoSidedPValue T) (fun _ : Unit => P) univ := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hn : HasLaw (fun ω => -T ω) (gaussianReal 0 1) P := by
    simpa only [Pi.neg_apply, neg_zero] using! gaussianReal_neg hT
  have hp := twoTailPValue_valid (upperTailPValue_valid hTm hT)
    (upperTailPValue_valid hTm.neg hn)
  have he : normalTwoSidedPValue T = fun ω =>
      min 1 (2 * min (upperTailPValue (gaussianReal 0 1) T ω)
        (upperTailPValue (gaussianReal 0 1) (fun ω => -T ω) ω)) :=
    funext (normalTwoSidedPValue_eq_two_tails T)
  rw [he]
  exact hp


/-- Exact calibration of the source's two-sided normal p-value. -/
theorem normalTwoSidedPValue_exact {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → ℝ}
    (hTm : Measurable T) (hT : HasLaw T (gaussianReal 0 1) P)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    P.real {ω | normalTwoSidedPValue T ω ≤ α} = α := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hn : HasLaw (fun ω => -T ω) (gaussianReal 0 1) P := by
    simpa only [Pi.neg_apply, neg_zero] using! gaussianReal_neg hT
  let p := upperTailPValue (gaussianReal 0 1) T
  let q := upperTailPValue (gaussianReal 0 1) (fun ω => -T ω)
  have hsum (ω) : p ω + q ω = 1 := by
    simp only [p, q, upperTailPValue, standardNormal_cdf_neg]
    ring
  have he : {ω | normalTwoSidedPValue T ω ≤ α} =
      {ω | p ω ≤ α/2} ∪ {ω | q ω ≤ α/2} := by
    ext ω
    rw [Set.mem_union]
    change normalTwoSidedPValue T ω ≤ α ↔ p ω ≤ α/2 ∨ q ω ≤ α/2
    rw [normalTwoSidedPValue_eq_two_tails]
    change min 1 (2*min (p ω) (q ω)) ≤ α ↔ _
    rw [min_le_iff]
    constructor
    · rintro (h | h)
      · exact (not_le_of_gt hα.2 h).elim
      · have hh : min (p ω) (q ω) ≤ α/2 := by linarith
        exact min_le_iff.mp hh
    · intro h
      right
      have hh := min_le_iff.mpr h
      linarith
  have hd : Disjoint {ω | p ω ≤ α/2} {ω | q ω ≤ α/2} := by
    apply Set.disjoint_left.mpr
    intro ω hp hq
    change p ω ≤ α/2 at hp
    change q ω ≤ α/2 at hq
    linarith [hsum ω, hα.2]
  have hqm : Measurable q := upperTailPValue_measurable _ hTm.neg
  rw [he, measureReal_union hd (measurableSet_le hqm measurable_const)]
  have ha : α/2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  rw [upperTailPValue_exact hT ha, upperTailPValue_exact hn ha]
  ring

/-- A statistic with a continuous asymptotic null law gives correctly
calibrated limiting upper-tail p-values, even if that CDF has flat portions. -/
theorem asymptotic_upperTailPValue_exact {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure ℝ}
    [IsProbabilityMeasure μ] [NullSingletonClass μ] {T : ℕ → Ω → ℝ}
    (hT : ConvergesInDistribution P μ T id)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => P.real {ω | upperTailPValue μ (T n) ω ≤ α}) atTop (𝓝 α) := by
  have hq : 1-α ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  let c := distributionQuantile μ (1-α)
  have he (n) : {ω | upperTailPValue μ (T n) ω ≤ α} = {ω | T n ω ∈ Ici c} := by
    ext ω
    simp only [mem_setOf_eq, mem_Ici, c, distributionQuantile_le_iff μ hq, upperTailPValue]
    constructor <;> intro h <;> linarith
  have hb : μ.map id (frontier (Ici c)) = 0 := by
    rw [Measure.map_id, frontier_Ici, measure_singleton]
  have h := asymptotic_rejection_probability hT (Ici c) measurableSet_Ici hb
  have hc : μ.real (Ici c) = α := by
    rw [← measureReal_congr Ioi_ae_eq_Ici]
    have hec : Ioi c = (Iic c)ᶜ := by ext x; simp
    rw [hec, measureReal_compl measurableSet_Iic, probReal_univ,
      distributionQuantile_exact μ _ hq]
    ring
  change Tendsto (fun n => P.real {ω | T n ω ∈ Ici c}) atTop (𝓝 (μ.real (Ici c))) at h
  rw [hc] at h
  simpa only [he] using h

end LectureNotes
