import LectureNotes.RowPerturbation
import Mathlib.Analysis.Calculus.FDeriv.Basic

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
  {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Convergence to zero in probability when each row has its own sample space. -/
def RowProbabilityZero (P : ∀ n, Measure (Ω n)) (Y : ∀ n, Ω n → E) : Prop :=
  ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ ‖Y n ω‖}) atTop (𝓝 0)

/-- Asymptotic tightness in norm for a sequence of row laws. -/
def RowTight (P : ∀ n, Measure (Ω n)) (Y : ∀ n, Ω n → E) : Prop :=
  ∀ ε > 0, ∃ M > 0, ∀ᶠ n in atTop, (P n).real {ω | M ≤ ‖Y n ω‖} < ε

theorem RowProbabilityZero.congr {Y Z : ∀ n, Ω n → E}
    (hY : RowProbabilityZero P Y) (hYZ : ∀ᶠ n in atTop, ∀ ω, Y n ω = Z n ω) :
    RowProbabilityZero P Z := by
  intro ε hε
  apply (hY ε hε).congr'
  filter_upwards [hYZ] with n hn
  congr 1
  ext ω
  simp only [mem_setOf_eq, hn ω]

theorem RowTight.congr {Y Z : ∀ n, Ω n → E}
    (hY : RowTight P Y) (hYZ : ∀ᶠ n in atTop, ∀ ω, Y n ω = Z n ω) :
    RowTight P Z := by
  intro ε hε
  obtain ⟨M, hM, he⟩ := hY ε hε
  refine ⟨M, hM, ?_⟩
  filter_upwards [he, hYZ] with n hn hn'
  convert hn using 1
  congr 1
  ext ω
  simp only [mem_setOf_eq, hn' ω]

theorem RowProbabilityZero.rowTight {Y : ∀ n, Ω n → E}
    (hY : RowProbabilityZero P Y) : RowTight P Y := by
  intro ε hε
  exact ⟨1, zero_lt_one, (hY 1 zero_lt_one).eventually (gt_mem_nhds hε)⟩

theorem RowProbabilityZero.add {Y Z : ∀ n, Ω n → E}
    (hY : RowProbabilityZero P Y) (hZ : RowProbabilityZero P Z) :
    RowProbabilityZero P (fun n ω => Y n ω + Z n ω) := by
  intro ε hε
  have hs n : {ω | ε ≤ ‖Y n ω + Z n ω‖} ⊆
      {ω | ε / 2 ≤ ‖Y n ω‖} ∪ {ω | ε / 2 ≤ ‖Z n ω‖} := by
    intro ω hω
    by_contra hb
    have hy : ‖Y n ω‖ < ε / 2 := lt_of_not_ge (fun h => hb (Or.inl h))
    have hz : ‖Z n ω‖ < ε / 2 := lt_of_not_ge (fun h => hb (Or.inr h))
    have ht := norm_add_le (Y n ω) (Z n ω)
    change ε ≤ ‖Y n ω + Z n ω‖ at hω
    linarith
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => (measureReal_mono (μ := P n) (hs n)).trans (measureReal_union_le _ _))
  simpa using (hY (ε / 2) (by positivity)).add (hZ (ε / 2) (by positivity))

theorem rowProbabilityZero_deterministic {a : ℕ → E}
    (ha : Tendsto a atTop (𝓝 0)) : RowProbabilityZero P (fun n _ => a n) := by
  intro ε hε
  have he := ha.norm.eventually (gt_mem_nhds (by simpa using hε : ‖(0 : E)‖ < ε))
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with n hn
  simp only [show {ω : Ω n | ε ≤ ‖a n‖} = ∅ by ext ω; simp [not_le.mpr hn],
    measureReal_empty]

theorem RowTight.add {Y Z : ∀ n, Ω n → E}
    (hY : RowTight P Y) (hZ : RowTight P Z) :
    RowTight P (fun n ω => Y n ω + Z n ω) := by
  intro ε hε
  obtain ⟨M, hM, hm⟩ := hY (ε / 2) (by positivity)
  obtain ⟨N, hN, hn⟩ := hZ (ε / 2) (by positivity)
  refine ⟨M + N, by positivity, ?_⟩
  filter_upwards [hm, hn] with n hym hzn
  have hs : {ω | M + N ≤ ‖Y n ω + Z n ω‖} ⊆
      {ω | M ≤ ‖Y n ω‖} ∪ {ω | N ≤ ‖Z n ω‖} := by
    intro ω hω
    by_contra hb
    have hy : ‖Y n ω‖ < M := lt_of_not_ge (fun h => hb (Or.inl h))
    have hz : ‖Z n ω‖ < N := lt_of_not_ge (fun h => hb (Or.inr h))
    have ht := norm_add_le (Y n ω) (Z n ω)
    change M + N ≤ ‖Y n ω + Z n ω‖ at hω
    linarith
  have hb := (measureReal_mono (μ := P n) hs).trans (measureReal_union_le _ _)
  linarith

theorem RowTight.prodMk {Y : ∀ n, Ω n → E} {Z : ∀ n, Ω n → F}
    (hY : RowTight P Y) (hZ : RowTight P Z) :
    RowTight P (fun n ω => (Y n ω, Z n ω)) := by
  intro ε hε
  obtain ⟨M, hM, hm⟩ := hY (ε / 2) (by positivity)
  obtain ⟨N, hN, hn⟩ := hZ (ε / 2) (by positivity)
  refine ⟨max M N, hM.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [hm, hn] with n hym hzn
  have hs : {ω | max M N ≤ ‖(Y n ω, Z n ω)‖} ⊆
      {ω | M ≤ ‖Y n ω‖} ∪ {ω | N ≤ ‖Z n ω‖} := by
    intro ω hω
    simp only [mem_setOf_eq, Prod.norm_def] at hω
    rcases le_max_iff.mp hω with h | h
    · exact Or.inl ((le_max_left _ _).trans h)
    · exact Or.inr ((le_max_right _ _).trans h)
  have hb := (measureReal_mono (μ := P n) hs).trans (measureReal_union_le _ _)
  linarith

theorem measureReal_norm_ge_le_secondMoment {Ω' : Type*} [MeasurableSpace Ω']
    {Q : Measure Ω'} [IsProbabilityMeasure Q] {Y : Ω' → E}
    (hY : MemLp Y 2 Q) {M : ℝ} (hM : 0 < M) :
    Q.real {ω | M ≤ ‖Y ω‖} ≤ (∫ ω, ‖Y ω‖ ^ 2 ∂Q) / M ^ 2 := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (fun ω => sq_nonneg ‖Y ω‖)) hY.norm.integrable_sq (M ^ 2)
  have hs : {ω | M ≤ ‖Y ω‖} ⊆ {ω | M ^ 2 ≤ ‖Y ω‖ ^ 2} := by
    intro ω hω
    change M ^ 2 ≤ ‖Y ω‖ ^ 2
    exact pow_le_pow_left₀ hM.le hω 2
  apply (le_div_iff₀ (sq_pos_of_pos hM)).mpr
  have hb := mul_le_mul_of_nonneg_left (measureReal_mono (μ := Q) hs) (sq_nonneg M)
  nlinarith

theorem rowTight_of_secondMoment_bound {Y : ∀ n, Ω n → E}
    (hY : ∀ n, MemLp (Y n) 2 (P n)) {K : ℝ}
    (hK : ∀ᶠ n in atTop, (∫ ω, ‖Y n ω‖ ^ 2 ∂P n) ≤ K) : RowTight P Y := by
  intro ε hε
  let M := Real.sqrt ((|K| + 1) / ε)
  have hM : 0 < M := Real.sqrt_pos.2 (by positivity)
  have hMsq : M ^ 2 = (|K| + 1) / ε := Real.sq_sqrt (by positivity)
  refine ⟨M, hM, ?_⟩
  filter_upwards [hK] with n hn
  apply (measureReal_norm_ge_le_secondMoment (hY n) hM).trans_lt
  apply (div_lt_iff₀ (sq_pos_of_pos hM)).mpr
  rw [hMsq, mul_div_cancel₀ _ (ne_of_gt hε)]
  exact hn.trans_lt (by linarith [le_abs_self K])

theorem rowTight_of_secondMoment_tendsto {Y : ∀ n, Ω n → E}
    (hY : ∀ n, MemLp (Y n) 2 (P n)) {K : ℝ}
    (hK : Tendsto (fun n => ∫ ω, ‖Y n ω‖ ^ 2 ∂P n) atTop (𝓝 K)) :
    RowTight P Y := by
  apply rowTight_of_secondMoment_bound hY
  exact (hK.eventually (gt_mem_nhds (show K < K + 1 by linarith))).mono fun _ h => h.le

section RealScalar
variable [NormedSpace ℝ E] [NormedSpace ℝ F]

theorem RowTight.smul_tendsto_zero {Y : ∀ n, Ω n → E}
    (hY : RowTight P Y) {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) :
    RowProbabilityZero P (fun n ω => a n • Y n ω) := by
  intro ε hε
  apply tendsto_order.2
  constructor
  · intro l hl
    exact Eventually.of_forall fun _ => hl.trans_le measureReal_nonneg
  · intro ζ hζ
    obtain ⟨M, hM, hm⟩ := hY ζ hζ
    have he := ha.norm.eventually (gt_mem_nhds (show ‖(0 : ℝ)‖ < ε / M by
      simpa using div_pos hε hM))
    filter_upwards [hm, he] with n hn han
    apply lt_of_le_of_lt (measureReal_mono (μ := P n) ?_) hn
    intro ω hω
    by_contra hb
    have hy : ‖Y n ω‖ < M := lt_of_not_ge hb
    have hh : ‖a n • Y n ω‖ < ε := by
      rw [norm_smul]
      calc
        ‖a n‖ * ‖Y n ω‖ ≤ ‖a n‖ * M := mul_le_mul_of_nonneg_left hy.le (norm_nonneg _)
        _ < ε := (lt_div_iff₀ hM).1 han
    exact (not_lt_of_ge hω) hh

theorem RowTight.continuousLinearMap {Y : ∀ n, Ω n → E}
    (hY : RowTight P Y) (A : E →L[ℝ] F) : RowTight P (fun n ω => A (Y n ω)) := by
  intro ε hε
  obtain ⟨M, hM, hm⟩ := hY ε hε
  refine ⟨(‖A‖ + 1) * M, by positivity, ?_⟩
  filter_upwards [hm] with n hn
  apply lt_of_le_of_lt (measureReal_mono (μ := P n) ?_) hn
  intro ω hω
  by_contra hb
  have hy : ‖Y n ω‖ < M := lt_of_not_ge hb
  have hh := A.le_opNorm (Y n ω)
  have hm' := mul_le_mul_of_nonneg_left hy.le (norm_nonneg A)
  change (‖A‖ + 1) * M ≤ ‖A (Y n ω)‖ at hω
  nlinarith

/-- Tight normalized deviations at a diverging scale force consistency. -/
theorem rowProbabilityZero_of_normalized_tight {T : ∀ n, Ω n → E}
    {x : ℕ → E} {θ : E} {r : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 θ)) (hr : Tendsto r atTop atTop)
    (hT : RowTight P (fun n ω => r n • (T n ω - x n))) :
    RowProbabilityZero P (fun n ω => T n ω - θ) := by
  have ha := hT.smul_tendsto_zero (tendsto_inv_atTop_zero.comp hr)
  have hd : RowProbabilityZero P (fun n ω => T n ω - x n) := by
    apply ha.congr
    filter_upwards [hr.eventually_gt_atTop 0] with n hn ω
    simp [smul_smul, ne_of_gt hn]
  have hc : RowProbabilityZero P (fun n _ => x n - θ) :=
    rowProbabilityZero_deterministic (by simpa using hx.sub (tendsto_const_nhds (x := θ)))
  exact (hd.add hc).congr (Eventually.of_forall fun n ω => by abel)

/-- A strict derivative controls the delta-method remainder for moving centers
and varying row laws. Consistency and tightness are probabilistic hypotheses;
the expansion itself is derived from the derivative. -/
theorem row_strict_delta_remainder {g : E → F} {A : E →L[ℝ] F} {θ : E}
    (hg : HasStrictFDerivAt g A θ) {T : ∀ n, Ω n → E} {x : ℕ → E} {r : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 θ))
    (hc : RowProbabilityZero P (fun n ω => T n ω - θ))
    (hT : RowTight P (fun n ω => r n • (T n ω - x n))) :
    RowProbabilityZero P (fun n ω =>
      r n • (g (T n ω) - g (x n) - A (T n ω - x n))) := by
  intro ε hε
  apply tendsto_order.2
  constructor
  · intro l hl
    exact Eventually.of_forall fun _ => hl.trans_le measureReal_nonneg
  · intro ζ hζ
    obtain ⟨M, hM, hm⟩ := hT (ζ / 2) (by positivity)
    have hη : 0 < ε / M := div_pos hε hM
    obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp (hg.isLittleO.bound hη)
    have hxn := (tendsto_iff_norm_sub_tendsto_zero.mp hx).eventually
      (gt_mem_nhds hδ)
    have hcn := (hc δ hδ).eventually (gt_mem_nhds (show (0 : ℝ) < ζ / 2 by positivity))
    filter_upwards [hm, hxn, hcn] with n hmn hxx hcc
    have hs : {ω | ε ≤ ‖r n • (g (T n ω) - g (x n) - A (T n ω - x n))‖} ⊆
        {ω | δ ≤ ‖T n ω - θ‖} ∪ {ω | M ≤ ‖r n • (T n ω - x n)‖} := by
      intro ω hω
      by_contra hbad
      have ht : ‖T n ω - θ‖ < δ := lt_of_not_ge (fun h => hbad (Or.inl h))
      have hi : ‖r n • (T n ω - x n)‖ < M :=
        lt_of_not_ge (fun h => hbad (Or.inr h))
      have hp : (T n ω, x n) ∈ Metric.ball (θ, θ) δ := by
        simpa only [Metric.mem_ball, dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, max_lt_iff] using And.intro ht hxx
      have hrem := hb hp
      have he : ‖r n • (g (T n ω) - g (x n) - A (T n ω - x n))‖ < ε := by
        calc
          _ = ‖r n‖ * ‖g (T n ω) - g (x n) - A (T n ω - x n)‖ := norm_smul _ _
          _ ≤ ‖r n‖ * (ε / M * ‖T n ω - x n‖) :=
            mul_le_mul_of_nonneg_left hrem (norm_nonneg _)
          _ = ε / M * ‖r n • (T n ω - x n)‖ := by rw [norm_smul]; ring
          _ < ε / M * M := mul_lt_mul_of_pos_left hi hη
          _ = ε := div_mul_cancel₀ _ (ne_of_gt hM)
      exact (not_lt_of_ge hω) he
    have hu := (measureReal_mono (μ := P n) hs).trans (measureReal_union_le _ _)
    linarith

/-- Delta remainder with consistency derived from normalized tightness. -/
theorem row_strict_delta_remainder_of_tight {g : E → F} {A : E →L[ℝ] F} {θ : E}
    (hg : HasStrictFDerivAt g A θ) {T : ∀ n, Ω n → E} {x : ℕ → E} {r : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 θ)) (hr : Tendsto r atTop atTop)
    (hT : RowTight P (fun n ω => r n • (T n ω - x n))) :
    RowProbabilityZero P (fun n ω =>
      r n • (g (T n ω) - g (x n) - A (T n ω - x n))) :=
  row_strict_delta_remainder hg hx (rowProbabilityZero_of_normalized_tight hx hr hT) hT

end RealScalar
end LectureNotes
