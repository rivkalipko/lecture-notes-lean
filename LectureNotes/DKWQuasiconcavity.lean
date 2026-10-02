import LectureNotes.DKWAnalytic

set_option autoImplicit false

/-! Shape of the exponential maximal-inequality bound used for the sharp
empirical-CDF inequality. -/
noncomputable section
namespace LectureNotes
open Set Filter
open scoped Topology

theorem log_one_add_lower_bound {x : ℝ} (hx : 0 ≤ x) :
    2 * x / (2 + x) ≤ Real.log (1 + x) := by
  let f (y : ℝ) := Real.log (1 + y) - 2 * y / (2 + y)
  have hd (y : ℝ) (hy : 0 ≤ y) : HasDerivAt f
      (y ^ 2 / ((1 + y) * (2 + y) ^ 2)) y := by
    have h1 : 1 + y ≠ 0 := by positivity
    have h2 : 2 + y ≠ 0 := by positivity
    have hlog := ((hasDerivAt_id y).const_add 1).log h1
    have hquot := ((hasDerivAt_id y).const_mul 2).div
      ((hasDerivAt_id y).const_add 2) h2
    convert! hlog.sub hquot using 1
    dsimp only [id_eq, f]
    field_simp
    ring
  have hm : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => by
        have hy0 : 0 ≤ y := interior_subset hy
        positivity)
  have h := hm (show (0 : ℝ) ∈ Ici 0 by simp) hx hx
  have h0 : f 0 = 0 := by simp [f]
  rw [h0] at h
  dsimp [f] at h
  linarith

/-- A concave initial segment followed by a decreasing tail is quasiconcave. -/
theorem quasiconcaveOn_Ioi_of_concave_antitone {f : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hc : ConcaveOn ℝ (Ioc 0 a) f) (hd : AntitoneOn f (Ici a)) :
    QuasiconcaveOn ℝ (Ioi 0) f := by
  intro c
  apply convex_iff_ordConnected.mpr
  constructor
  intro x hx y hy z hz
  refine ⟨hx.1.trans_le hz.1, ?_⟩
  by_cases hza : z ≤ a
  · by_cases hya : y ≤ a
    · exact ((hc.quasiconcaveOn c).ordConnected.out
        ⟨⟨hx.1, hz.1.trans hza⟩, hx.2⟩ ⟨⟨hy.1, hya⟩, hy.2⟩ hz).2
    · have hay : a ≤ y := le_of_not_ge hya
      have hca : c ≤ f a := hy.2.trans (hd (by simp) hay hay)
      exact ((hc.quasiconcaveOn c).ordConnected.out
        ⟨⟨hx.1, hz.1.trans hza⟩, hx.2⟩ ⟨⟨ha, le_rfl⟩, hca⟩ ⟨hz.1, hza⟩).2
  · have haz : a ≤ z := le_of_not_ge hza
    exact hy.2.trans (hd haz (haz.trans hz.2) hz.2)

def dkwShape (ε ℓ y : ℝ) : ℝ := (y + ε) * (Real.log y - Real.log (y + ℓ))

def dkwShapeDeriv (ε ℓ y : ℝ) : ℝ :=
  Real.log y - Real.log (y + ℓ) + ℓ * (y + ε) / (y * (y + ℓ))

theorem hasDerivAt_dkwShape (ε : ℝ) {ℓ y : ℝ} (hℓ : 0 ≤ ℓ) (hy : 0 < y) :
    HasDerivAt (dkwShape ε ℓ) (dkwShapeDeriv ε ℓ y) y := by
  have hyl : 0 < y + ℓ := add_pos_of_pos_of_nonneg hy hℓ
  have h := ((hasDerivAt_id y).add_const ε).mul
    (((hasDerivAt_id y).log hy.ne').sub (((hasDerivAt_id y).add_const ℓ).log hyl.ne'))
  convert! h using 1
  dsimp only [dkwShape, dkwShapeDeriv, id_eq, Pi.sub_apply, Pi.mul_apply]
  field_simp
  ring

theorem hasDerivAt_dkwShapeDeriv (ε : ℝ) {ℓ y : ℝ} (hℓ : 0 ≤ ℓ) (hy : 0 < y) :
    HasDerivAt (dkwShapeDeriv ε ℓ)
      (-ℓ * (y * (2 * ε - ℓ) + ε * ℓ) / (y ^ 2 * (y + ℓ) ^ 2)) y := by
  have hyl : 0 < y + ℓ := add_pos_of_pos_of_nonneg hy hℓ
  have hn := ((hasDerivAt_id y).add_const ε).const_mul ℓ
  have hd := (hasDerivAt_id y).mul ((hasDerivAt_id y).add_const ℓ)
  have hlog := ((hasDerivAt_id y).log hy.ne').sub
    (((hasDerivAt_id y).add_const ℓ).log hyl.ne')
  have h := hlog.add (hn.div hd (mul_pos hy hyl).ne')
  convert! h using 1
  dsimp only [dkwShapeDeriv, id_eq, Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.div_apply]
  field_simp
  ring

theorem dkwShape_concaveOn {ε ℓ : ℝ} (hℓ : 0 ≤ ℓ) {D : Set ℝ}
    (hD : Convex ℝ D) (hpos : D ⊆ Ioi 0)
    (hcurv : ∀ y ∈ D, 0 ≤ y * (2 * ε - ℓ) + ε * ℓ) :
    ConcaveOn ℝ D (dkwShape ε ℓ) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos hD
    (fun y hy => (hasDerivAt_dkwShape ε hℓ (hpos hy)).continuousAt.continuousWithinAt)
    (fun y hy => (hasDerivAt_dkwShape ε hℓ (hpos (interior_subset hy))).hasDerivWithinAt)
    (fun y hy => (hasDerivAt_dkwShapeDeriv ε hℓ (hpos (interior_subset hy))).hasDerivWithinAt)
  intro y hy
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hℓ) (hcurv y (interior_subset hy))
  · positivity

theorem dkwShapeDeriv_nonpos {ε ℓ y : ℝ} (hℓ : 0 ≤ ℓ) (hy : 0 < y)
    (hcut : ε * ℓ ≤ y * (ℓ - 2 * ε)) : dkwShapeDeriv ε ℓ y ≤ 0 := by
  have hyl : 0 < y + ℓ := add_pos_of_pos_of_nonneg hy hℓ
  have h2 : 0 < 2 * y + ℓ := by positivity
  have hr : 0 ≤ ℓ / y := div_nonneg hℓ hy.le
  have hl := log_one_add_lower_bound hr
  have he : (y + ℓ) / y = 1 + ℓ / y := by field_simp
  have hlog := Real.log_div hyl.ne' hy.ne'
  rw [he] at hlog
  have hdiff : 2 * (ℓ / y) / (2 + ℓ / y) - ℓ * (y + ε) / (y * (y + ℓ)) =
      ℓ * (y * (ℓ - 2 * ε) - ε * ℓ) / (y * (y + ℓ) * (2 * y + ℓ)) := by
    field_simp
    ring
  have hn : 0 ≤ 2 * (ℓ / y) / (2 + ℓ / y) - ℓ * (y + ε) / (y * (y + ℓ)) := by
    rw [hdiff]
    apply div_nonneg (mul_nonneg hℓ (sub_nonneg.mpr hcut))
    positivity
  dsimp only [dkwShapeDeriv]
  linarith

theorem dkwShape_quasiconcave {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 ≤ ℓ) :
    QuasiconcaveOn ℝ (Ioi 0) (dkwShape ε ℓ) := by
  by_cases hle : ℓ ≤ 2 * ε
  · apply (dkwShape_concaveOn hℓ (convex_Ioi 0) (fun _ h => h) ?_).quasiconcaveOn
    intro y hy
    exact add_nonneg (mul_nonneg hy.le (sub_nonneg.mpr hle)) (mul_nonneg hε.le hℓ)
  · have hlt : 0 < ℓ - 2 * ε := sub_pos.mpr (lt_of_not_ge hle)
    let a := ε * ℓ / (ℓ - 2 * ε)
    have ha : 0 < a := div_pos (mul_pos hε (by linarith)) hlt
    apply quasiconcaveOn_Ioi_of_concave_antitone ha
    · apply dkwShape_concaveOn hℓ (convex_Ioc 0 a) (fun _ h => h.1)
      intro y hy
      have hb : y * (ℓ - 2 * ε) ≤ ε * ℓ := (le_div_iff₀ hlt).mp hy.2
      nlinarith
    · apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
        (fun y hy => (hasDerivAt_dkwShape ε hℓ (ha.trans_le hy)).continuousAt.continuousWithinAt)
        (fun y hy => (hasDerivAt_dkwShape ε hℓ (ha.trans_le (interior_subset hy))).hasDerivWithinAt)
      intro y hy
      apply dkwShapeDeriv_nonpos hℓ (ha.trans_le (interior_subset hy))
      exact (div_le_iff₀ hlt).mp (interior_subset hy)

def dkwLogBound (ε p ℓ : ℝ) : ℝ :=
  Real.log (1 + ℓ) + p * (Real.log (p - ε) - Real.log (p - ε + ℓ))

theorem dkwLogBound_eq_shape (ε p ℓ : ℝ) :
    dkwLogBound ε p ℓ = Real.log (1 + ℓ) + dkwShape ε ℓ (p - ε) := by
  unfold dkwLogBound dkwShape
  ring

theorem dkwLogBound_quasiconcave {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 ≤ ℓ) :
    QuasiconcaveOn ℝ (Ioi ε) (fun p => dkwLogBound ε p ℓ) := by
  intro c
  apply convex_iff_ordConnected.mpr
  constructor
  intro x hx y hy z hz
  refine ⟨hx.1.trans_le hz.1, ?_⟩
  change ε < x ∧ c ≤ dkwLogBound ε x ℓ at hx
  change ε < y ∧ c ≤ dkwLogBound ε y ℓ at hy
  have hqc := (dkwShape_quasiconcave hε hℓ (c - Real.log (1 + ℓ))).ordConnected
  have hx' : x - ε ∈ Ioi 0 ∩ {t | c - Real.log (1 + ℓ) ≤ dkwShape ε ℓ t} := by
    refine ⟨show (0 : ℝ) < x - ε from sub_pos.mpr hx.1, ?_⟩
    change c - Real.log (1 + ℓ) ≤ dkwShape ε ℓ (x - ε)
    have hh := hx.2
    rw [dkwLogBound_eq_shape] at hh
    linarith
  have hy' : y - ε ∈ Ioi 0 ∩ {t | c - Real.log (1 + ℓ) ≤ dkwShape ε ℓ t} := by
    refine ⟨show (0 : ℝ) < y - ε from sub_pos.mpr hy.1, ?_⟩
    change c - Real.log (1 + ℓ) ≤ dkwShape ε ℓ (y - ε)
    have hh := hy.2
    rw [dkwLogBound_eq_shape] at hh
    linarith
  have h := hqc.out hx' hy' ⟨sub_le_sub_right hz.1 ε, sub_le_sub_right hz.2 ε⟩
  change c ≤ dkwLogBound ε z ℓ
  rw [dkwLogBound_eq_shape]
  linarith [h.2]

theorem quasiconvexOn_Ici_of_antitone_monotone {f : ℝ → ℝ} {a : ℝ}
    (hd : AntitoneOn f (Icc 0 a)) (hi : MonotoneOn f (Ici a)) :
    QuasiconvexOn ℝ (Ici 0) f := by
  intro c
  apply convex_iff_ordConnected.mpr
  constructor
  intro x hx y hy z hz
  refine ⟨hx.1.trans hz.1, ?_⟩
  by_cases hza : z ≤ a
  · exact (hd ⟨hx.1, hz.1.trans hza⟩ ⟨hx.1.trans hz.1, hza⟩ hz.1).trans hx.2
  · have haz : a ≤ z := le_of_not_ge hza
    exact (hi haz (haz.trans hz.2) hz.2).trans hy.2

theorem hasDerivAt_dkwLogBound {ε p ℓ : ℝ} (hp : ε < p) (hℓ : 0 ≤ ℓ) :
    HasDerivAt (dkwLogBound ε p)
      (((1 - p) * ℓ - ε) / ((1 + ℓ) * (p - ε + ℓ))) ℓ := by
  have h1 : 0 < 1 + ℓ := by positivity
  have hq : 0 < p - ε + ℓ := add_pos_of_pos_of_nonneg (sub_pos.mpr hp) hℓ
  have h := (((hasDerivAt_id ℓ).const_add 1).log h1.ne').add
    ((((hasDerivAt_const ℓ (Real.log (p - ε))).sub
      (((hasDerivAt_id ℓ).const_add (p - ε)).log hq.ne')).const_mul p))
  convert! h using 1
  dsimp only [dkwLogBound, id_eq, Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.div_apply]
  field_simp
  ring

theorem dkwLogBound_quasiconvex {ε p : ℝ} (hε : 0 < ε) (hp : ε < p) :
    QuasiconvexOn ℝ (Ici 0) (dkwLogBound ε p) := by
  by_cases hp1 : p < 1
  · let a := ε / (1 - p)
    have hden : 0 < 1 - p := sub_pos.mpr hp1
    apply quasiconvexOn_Ici_of_antitone_monotone (a := a)
    · apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 a)
        (fun ℓ hℓ => (hasDerivAt_dkwLogBound hp hℓ.1).continuousAt.continuousWithinAt)
        (fun ℓ hℓ => (hasDerivAt_dkwLogBound hp (interior_subset hℓ).1).hasDerivWithinAt)
      intro ℓ hℓ
      have hh := (interior_subset hℓ).2
      have hn : (1 - p) * ℓ ≤ ε := by
        have hb := (le_div_iff₀ hden).mp hh
        nlinarith
      apply div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hn)
      have h0 := (interior_subset hℓ).1
      have hq : 0 < p - ε := sub_pos.mpr hp
      positivity
    · apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
        (fun ℓ hℓ => (hasDerivAt_dkwLogBound hp ((div_pos hε hden).le.trans hℓ)).continuousAt.continuousWithinAt)
        (fun ℓ hℓ => (hasDerivAt_dkwLogBound hp
          ((div_pos hε hden).le.trans (interior_subset hℓ))).hasDerivWithinAt)
      intro ℓ hℓ
      have hh := (div_le_iff₀ hden).mp (interior_subset hℓ)
      have hn : ε ≤ (1 - p) * ℓ := by nlinarith
      apply div_nonneg (sub_nonneg.mpr hn)
      have h0 := (div_pos hε hden).le.trans (interior_subset hℓ)
      have hq : 0 < p - ε := sub_pos.mpr hp
      positivity
  · apply AntitoneOn.quasiconvexOn _ (convex_Ici 0)
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun ℓ hℓ => (hasDerivAt_dkwLogBound hp hℓ).continuousAt.continuousWithinAt)
      (fun ℓ hℓ => (hasDerivAt_dkwLogBound hp (interior_subset hℓ)).hasDerivWithinAt)
    intro ℓ hℓ
    have h0 : 0 ≤ ℓ := interior_subset hℓ
    have hn : (1 - p) * ℓ - ε ≤ 0 := by
      have hh := mul_nonpos_of_nonpos_of_nonneg (show 1 - p ≤ 0 by linarith) h0
      linarith
    apply div_nonpos_of_nonpos_of_nonneg hn
    have hq : 0 < p - ε := sub_pos.mpr hp
    positivity

theorem dkwLogBound_at_optimizer {ε p : ℝ} (hε : 0 < ε) (hp : p ∈ Ioo ε 1) :
    dkwLogBound ε p (ε / (1 - p)) = -bernoulliDivergence p (p - ε) := by
  have hp0 : 0 < p := hε.trans hp.1
  have hq : 0 < p - ε := sub_pos.mpr hp.1
  have h1p : 0 < 1 - p := sub_pos.mpr hp.2
  have h1q : 0 < 1 - (p - ε) := by linarith
  have he1 : 1 + ε / (1 - p) = (1 - (p - ε)) / (1 - p) := by field_simp; ring
  have he2 : p - ε + ε / (1 - p) = p * (1 - (p - ε)) / (1 - p) := by field_simp; ring
  unfold dkwLogBound bernoulliDivergence
  rw [he1, he2, Real.log_div h1q.ne' h1p.ne',
    Real.log_div (mul_pos hp0 h1q).ne' h1p.ne', Real.log_mul hp0.ne' h1q.ne']
  ring

theorem dkwLogBound_optimizer_le {ε p : ℝ} (hε : 0 < ε) (hp : p ∈ Ioo ε 1) :
    dkwLogBound ε p (ε / (1 - p)) ≤ -2 * ε ^ 2 := by
  rw [dkwLogBound_at_optimizer hε hp]
  have h := bernoulliDivergence_pinsker ⟨(hε.trans hp.1).le, hp.2.le⟩
    (show p - ε ∈ Ioo 0 1 by constructor <;> linarith [hp.1, hp.2])
  have he : p - (p - ε) = ε := by ring
  rw [he] at h
  linarith

theorem dkwLogBound_endpoint_tendsto {ε : ℝ} (hε : ε ∈ Ioo 0 1) :
    Tendsto (fun k : ℕ => dkwLogBound ε 1 k) atTop (𝓝 (Real.log (1 - ε))) := by
  have hq : 0 < 1 - ε := sub_pos.mpr hε.2
  have hd : Tendsto (fun k : ℕ => (1 - ε) + (k : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop (1 - ε) tendsto_natCast_atTop_atTop
  have hf := hd.const_div_atTop ε
  have hr : Tendsto (fun k : ℕ => (1 + (k : ℝ)) / ((1 - ε) + k)) atTop (𝓝 1) := by
    convert! hf.const_add 1 using 1
    · funext k
      have hk : 0 < 1 - ε + (k : ℝ) := by positivity
      field_simp
      ring
    · simp
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr
  have ht := hlog.add_const (Real.log (1 - ε))
  simp only [Real.log_one, zero_add] at ht
  convert! ht using 1
  funext k
  have h1 : 0 < 1 + (k : ℝ) := by positivity
  have hk : 0 < 1 - ε + (k : ℝ) := by positivity
  dsimp only [Function.comp_def]
  rw [Real.log_div h1.ne' hk.ne']
  unfold dkwLogBound
  ring

theorem dkwLogBound_exists_parameter {ε p η : ℝ} (hε : ε ∈ Ioo 0 1)
    (hp : p ∈ Ioc ε 1) (hη : 0 < η) :
    ∃ ℓ ∈ Ici 0, dkwLogBound ε p ℓ < -2 * ε ^ 2 + η := by
  rcases hp.2.eq_or_lt with hp1 | hp1
  · subst p
    have hkl := bernoulliDivergence_pinsker (p := 1) (q := 1 - ε)
      (by constructor <;> norm_num) (by constructor <;> linarith [hε.1, hε.2])
    have he : 1 - (1 - ε) = ε := by ring
    rw [he] at hkl
    simp only [bernoulliDivergence, Real.log_one, one_mul, sub_self, zero_mul, add_zero,
      zero_sub, sub_zero] at hkl
    have hbound : Real.log (1 - ε) < -2 * ε ^ 2 + η := by linarith
    obtain ⟨k, hk⟩ := ((tendsto_order.mp (dkwLogBound_endpoint_tendsto hε)).2
      (-2 * ε ^ 2 + η) hbound).exists
    exact ⟨k, show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k, hk⟩
  · refine ⟨ε / (1 - p), (div_pos hε.1 (sub_pos.mpr hp1)).le, ?_⟩
    exact (dkwLogBound_optimizer_le hε.1 ⟨hp.1, hp1⟩).trans_lt (by linarith)

theorem sion_exists_common_strict_bound {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (hX : X.Nonempty) (kX : IsCompact X) (cX : Convex ℝ X) (cY : Convex ℝ Y)
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x => f x y) X)
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X (fun x => f x y))
    (hfx : ∀ x ∈ X, UpperSemicontinuousOn (f x) Y)
    (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y (f x)) {c : ℝ}
    (hpoint : ∀ x ∈ X, ∃ y ∈ Y, c < f x y) :
    ∃ y ∈ Y, ∀ x ∈ X, c < f x y := by
  classical
  have hs : ∃ s : Finset Y, ∀ x ∈ X, ∃ y ∈ s, c < f x y := by
    rw [← LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset kX hfy]
    apply Set.eq_empty_of_forall_notMem
    rintro x ⟨hx, hx'⟩
    simp only [mem_iInter, mem_preimage, mem_Iic] at hx'
    obtain ⟨y, hy, hh⟩ := hpoint x hx
    exact hh.not_ge (hx' y hy)
  obtain ⟨s, hs⟩ := hs
  have ht : ∀ x ∈ X, ∃ y ∈ Subtype.val '' (s : Set Y), c < f x y := by
    intro x hx
    obtain ⟨y, hy, hh⟩ := hs x hx
    exact ⟨y, ⟨y, hy, rfl⟩, hh⟩
  exact Sion.exists_lt_iInf_of_lt_iInf_of_finite hX kX hfy hfy' cY hfx hfx' cX
    (s.finite_toSet.image Subtype.val) (by rintro _ ⟨y, _, rfl⟩; exact y.property) ht

theorem continuousAt_dkwLogBound_left {ε p ℓ : ℝ} (hp : ε < p) (hℓ : 0 ≤ ℓ) :
    ContinuousAt (fun q => dkwLogBound ε q ℓ) p := by
  simp_rw [dkwLogBound_eq_shape]
  have hg : ContinuousAt (fun q : ℝ => q - ε) p := continuousAt_id.sub continuousAt_const
  exact continuousAt_const.add ((hasDerivAt_dkwShape ε hℓ (sub_pos.mpr hp)).continuousAt.comp
    (f := fun q : ℝ => q - ε) (x := p) hg)

/-- A single nonnegative exponential parameter gives the sharp quadratic
rate simultaneously on every compact range of empirical proportions. -/
theorem dkwLogBound_uniform_parameter {ε a η : ℝ} (hε : ε ∈ Ioo 0 1)
    (ha : a ∈ Ioc ε 1) (hη : 0 < η) :
    ∃ ℓ ∈ Ici 0, ∀ p ∈ Icc a 1, dkwLogBound ε p ℓ < -2 * ε ^ 2 + η := by
  have hpoint : ∀ p ∈ Icc a 1, ∃ ℓ ∈ Ici 0,
      -(-2 * ε ^ 2 + η) < -dkwLogBound ε p ℓ := by
    intro p hp
    obtain ⟨ℓ, hℓ, hh⟩ := dkwLogBound_exists_parameter hε ⟨ha.1.trans_le hp.1, hp.2⟩ hη
    exact ⟨ℓ, hℓ, neg_lt_neg hh⟩
  have hfy (ℓ : ℝ) (hℓ : ℓ ∈ Ici 0) :
      LowerSemicontinuousOn (fun p => -dkwLogBound ε p ℓ) (Icc a 1) := by
    apply ContinuousOn.lowerSemicontinuousOn
    intro p hp
    exact (continuousAt_dkwLogBound_left (ha.1.trans_le hp.1) hℓ).neg.continuousWithinAt
  have hfy' (ℓ : ℝ) (hℓ : ℓ ∈ Ici 0) :
      QuasiconvexOn ℝ (Icc a 1) (fun p => -dkwLogBound ε p ℓ) := by
    have hq := (convex_Icc a 1).quasiconcaveOn_restrict
      (dkwLogBound_quasiconcave hε.1 hℓ) (fun p hp => ha.1.trans_le hp.1)
    simpa only [Function.comp_def] using hq.antitone_comp (fun x y hxy => neg_le_neg hxy)
  have hfx (p : ℝ) (hp : p ∈ Icc a 1) :
      UpperSemicontinuousOn (fun ℓ => -dkwLogBound ε p ℓ) (Ici 0) := by
    apply ContinuousOn.upperSemicontinuousOn
    intro ℓ hℓ
    exact (hasDerivAt_dkwLogBound (ha.1.trans_le hp.1) hℓ).continuousAt.neg.continuousWithinAt
  have hfx' (p : ℝ) (hp : p ∈ Icc a 1) :
      QuasiconcaveOn ℝ (Ici 0) (fun ℓ => -dkwLogBound ε p ℓ) := by
    simpa only [Function.comp_def] using
      (dkwLogBound_quasiconvex hε.1 (ha.1.trans_le hp.1)).antitone_comp
        (fun x y hxy => neg_le_neg hxy)
  obtain ⟨ℓ, hℓ, hh⟩ := sion_exists_common_strict_bound (nonempty_Icc.mpr ha.2)
    isCompact_Icc (convex_Icc a 1) (convex_Ici 0) hfy hfy' hfx hfx' hpoint
  refine ⟨ℓ, hℓ, fun p hp => ?_⟩
  have h := hh p hp
  linarith

end LectureNotes
