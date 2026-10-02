import LectureNotes.BetaConjugacy
import LectureNotes.Convergence
import LectureNotes.HighestDensity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Distributions.Uniform

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- The uniform probability law on `[0,θ]` when `θ > 0`. -/
def uniformEndpointLaw (θ : ℝ) : Measure ℝ :=
  (ENNReal.ofReal θ)⁻¹ • volume.restrict (Icc 0 θ)

def uniformEndpointDensity (θ x : ℝ) : ℝ := if x ∈ Icc 0 θ then 1 / θ else 0

def sampleMaximum {n : ℕ} (x : Fin n → ℝ) : ℝ := ⨆ i, x i

theorem sampleMaximum_le_iff {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (t : ℝ) :
    sampleMaximum x ≤ t ↔ ∀ i, x i ≤ t := by
  have : NeZero n := ⟨hn.ne'⟩
  exact ciSup_le_iff (Finite.bddAbove_range x)

theorem le_sampleMaximum {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    x i ≤ sampleMaximum x := le_ciSup (Finite.bddAbove_range x) i

theorem sampleMaximum_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) :
    Measurable (fun ω => sampleMaximum (fun i => X i ω)) := Measurable.iSup hX

theorem uniformEndpointLaw_probability {θ : ℝ} (hθ : 0 < θ) :
    IsProbabilityMeasure (uniformEndpointLaw θ) := by
  constructor
  simp [uniformEndpointLaw, Measure.smul_apply, Real.volume_Icc,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hθ).ne' ENNReal.ofReal_ne_top]

theorem uniformEndpointLaw_density {θ : ℝ} (hθ : 0 < θ) :
    volume.withDensity (fun x => ENNReal.ofReal (uniformEndpointDensity θ x)) =
      uniformEndpointLaw θ := by
  have he : (fun x => ENNReal.ofReal (uniformEndpointDensity θ x)) =
      (Icc 0 θ).indicator (fun _ => (ENNReal.ofReal θ)⁻¹) := by
    funext x
    by_cases hx : x ∈ Icc 0 θ
    · simp [uniformEndpointDensity, hx, ENNReal.ofReal_inv_of_pos hθ]
    · simp [uniformEndpointDensity, hx]
  rw [he, withDensity_indicator measurableSet_Icc, withDensity_const]
  rfl

theorem uniformEndpoint_cdf {θ : ℝ} (hθ : 0 < θ) (t : ℝ) :
    cdf (uniformEndpointLaw θ) t = max (min t θ) 0 / θ := by
  have := uniformEndpointLaw_probability hθ
  rw [cdf_eq_real, uniformEndpointLaw, measureReal_ennreal_smul_apply,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hθ.le,
    measureReal_restrict_apply measurableSet_Iic]
  have he : Iic t ∩ Icc (0 : ℝ) θ = Icc 0 (min t θ) := by ext x; simp; tauto
  rw [he, Real.volume_real_Icc, sub_zero]
  ring

/-- The sample maximum is a global likelihood maximizer whenever all sample
values are nonnegative and the maximum itself is positive. -/
theorem uniformEndpoint_maximizes_density {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hm : 0 < sampleMaximum x) {θ : ℝ} (hθ : 0 < θ) :
    (∏ i, uniformEndpointDensity θ (x i)) ≤
      ∏ i, uniformEndpointDensity (sampleMaximum x) (x i) := by
  have hfit (i) : x i ∈ Icc 0 (sampleMaximum x) := ⟨hx i, le_sampleMaximum x i⟩
  simp only [uniformEndpointDensity, if_pos (hfit _), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  by_cases hb : ∀ i, x i ≤ θ
  · have hc : sampleMaximum x ≤ θ := (sampleMaximum_le_iff hn x θ).mpr hb
    have hi : ∀ i, x i ∈ Icc 0 θ := fun i => ⟨hx i, hb i⟩
    simp only [if_pos (hi _), Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le hm hc) n
  · push Not at hb
    obtain ⟨i, hi⟩ := hb
    have hz : (∏ i, if x i ∈ Icc 0 θ then 1 / θ else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [show x i ∉ Icc 0 θ from fun h => (not_le_of_gt hi) h.2]
    rw [hz]
    positivity

/-- With an empty sample every positive endpoint has the same likelihood. -/
theorem uniformEndpoint_empty_likelihood (x : Fin 0 → ℝ) (θ : ℝ) :
    (∏ i, uniformEndpointDensity θ (x i)) = 1 := by simp

theorem beta_nat_succ_one (n : ℕ) : beta ((n : ℝ) + 1) 1 = 1 / (n + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  unfold beta
  rw [Real.Gamma_one, mul_one, Real.Gamma_add_one hn.ne']
  have hg := (Real.Gamma_pos_of_pos hn).ne'
  field_simp

theorem beta_nat_succ_one_density (n : ℕ) (x : ℝ) :
    betaPDFReal ((n : ℝ) + 1) 1 x =
      (Ioo (0 : ℝ) 1).indicator (fun x => (n + 1) * x ^ n) x := by
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · have hh : 0 < x ∧ x < 1 := hx
    simp [betaPDFReal, hh, hx, beta_nat_succ_one, Real.rpow_natCast]
  · have hh : ¬(0 < x ∧ x < 1) := hx
    simp [betaPDFReal, hh, hx]

theorem beta_nat_succ_one_cdf (n : ℕ) (t : ℝ) :
    cdf (betaMeasure ((n : ℝ) + 1) 1) t = max (min t 1) 0 ^ (n + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have : IsProbabilityMeasure (betaMeasure ((n : ℝ) + 1) 1) := isProbabilityMeasureBeta hn zero_lt_one
  have heq : betaPDFReal ((n : ℝ) + 1) 1 =ᵐ[volume]
      (Icc (0 : ℝ) 1).indicator (fun x => (n + 1) * x ^ n) := by
    filter_upwards [Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)] with x hx
    rw [beta_nat_succ_one_density]
    have hiff : x ∈ Ioo (0 : ℝ) 1 ↔ x ∈ Icc (0 : ℝ) 1 := Eq.to_iff hx
    by_cases hx' : x ∈ Ioo (0 : ℝ) 1
    · have hb : x ∈ Icc (0 : ℝ) 1 := hiff.mp hx'
      rw [indicator_of_mem hx', indicator_of_mem hb]
    · have hb : x ∉ Icc (0 : ℝ) 1 := fun h => hx' (hiff.mpr h)
      rw [indicator_of_notMem hx', indicator_of_notMem hb]
  rw [cdf_eq_real]
  change (volume.withDensity (fun x => ENNReal.ofReal (betaPDFReal ((n : ℝ) + 1) 1 x))).real (Iic t) = _
  rw [density_event_eq_integral (beta_density_integrable hn zero_lt_one)
    (beta_density_nonneg hn zero_lt_one) _ measurableSet_Iic]
  rw [setIntegral_congr_ae measurableSet_Iic (heq.mono (fun _ hx _ => hx)),
    integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  have hset : Icc (0 : ℝ) 1 ∩ Iic t = Icc 0 (min t 1) := by ext x; simp; tauto
  rw [hset]
  by_cases ht : 0 ≤ min t 1
  · rw [max_eq_left ht, integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero n), sub_zero]
    exact mul_div_cancel₀ _ hn.ne'
  · have he : Icc (0 : ℝ) (min t 1) = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge ht)
    simp [he, max_eq_right (le_of_not_ge ht)]

/-- Independence gives the exact CDF of the finite sample maximum. -/
theorem iid_uniform_maximum_cdf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) (hind : iIndepFun X P) (t : ℝ) :
    P.real {ω | sampleMaximum (fun i => X i ω) ≤ t} = (max (min t θ) 0 / θ) ^ n := by
  have := uniformEndpointLaw_probability hθ
  have hm := hind.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun _ => Iic t) (fun _ _ => measurableSet_Iic)
  have hs : {ω | sampleMaximum (fun i => X i ω) ≤ t} = ⋂ i, X i ⁻¹' Iic t := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_Iic]
    exact sampleMaximum_le_iff hn _ _
  simp only [Finset.mem_univ, iInter_true] at hm
  rw [hs, measureReal_def, hm, ENNReal.toReal_prod]
  have hp (i) : (P (X i ⁻¹' Iic t)).toReal = max (min t θ) 0 / θ := by
    rw [← measureReal_def]
    exact ((hX i).measureReal_eq (p := fun x => x ≤ t) measurableSet_Iic).trans
      ((cdf_eq_real (uniformEndpointLaw θ) t).symm.trans (uniformEndpoint_cdf hθ t))
  simp_rw [hp]
  simp [div_pow]

theorem uniformEndpoint_scaled_cdf {θ : ℝ} (hθ : 0 < θ) (t : ℝ) :
    cdf (uniformEndpointLaw θ) (θ * t) = max (min t 1) 0 := by
  rw [uniformEndpoint_cdf hθ]
  by_cases ht : t ≤ 0
  · have hp : θ * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ.le ht
    rw [max_eq_right ((min_le_left _ _).trans hp),
      max_eq_right ((min_le_left _ _).trans ht), zero_div]
  · have ht0 : 0 < t := lt_of_not_ge ht
    by_cases ht1 : 1 ≤ t
    · have hp : θ ≤ θ * t := by nlinarith
      rw [min_eq_right hp, max_eq_left hθ.le, div_self hθ.ne',
        min_eq_right ht1, max_eq_left zero_le_one]
    · have ht1' : t ≤ 1 := le_of_lt (lt_of_not_ge ht1)
      have hp : θ * t ≤ θ := by nlinarith
      rw [min_eq_left hp, max_eq_left (by positivity : 0 ≤ θ * t),
        min_eq_left ht1', max_eq_left ht0.le]
      exact mul_div_cancel_left₀ t hθ.ne'

/-- For `n+1` draws, the maximum divided by the endpoint has the exact
Beta(`n+1`,1) law, obtained from the independent sample CDF. -/
theorem iid_uniform_standardized_maximum_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (n : ℕ)
    {X : Fin (n + 1) → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) (hind : iIndepFun X P) :
    HasLaw (fun ω => sampleMaximum (fun i => X i ω) / θ)
      (betaMeasure ((n : ℝ) + 1) 1) P := by
  have hm : Measurable (fun ω => sampleMaximum (fun i => X i ω) / θ) :=
    (sampleMaximum_measurable X hXm).div_const θ
  refine ⟨hm.aemeasurable, ?_⟩
  have : IsProbabilityMeasure (P.map (fun ω => sampleMaximum (fun i => X i ω) / θ)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  have : IsProbabilityMeasure (betaMeasure ((n : ℝ) + 1) 1) :=
    isProbabilityMeasureBeta (by positivity) zero_lt_one
  apply Measure.eq_of_cdf
  ext t
  rw [cdf_eq_real, map_measureReal_apply hm measurableSet_Iic]
  have he : (fun ω => sampleMaximum (fun i => X i ω) / θ) ⁻¹' Iic t =
      {ω | sampleMaximum (fun i => X i ω) ≤ θ * t} := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_ofPred_eq, div_le_iff₀ hθ, mul_comm]
  rw [he, iid_uniform_maximum_cdf (Nat.succ_pos n) hθ hX hind,
    ← uniformEndpoint_cdf hθ, uniformEndpoint_scaled_cdf hθ, beta_nat_succ_one_cdf]

theorem iid_uniform_maximum_mean {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (n : ℕ)
    {X : Fin (n + 1) → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) (hind : iIndepFun X P) :
    (∫ ω, sampleMaximum (fun i => X i ω) ∂P) = θ * (n + 1) / (n + 2) := by
  have hβ := iid_uniform_standardized_maximum_law n hθ hXm hX hind
  have he : (fun ω => sampleMaximum (fun i => X i ω)) =
      fun ω => θ * (sampleMaximum (fun i => X i ω) / θ) := by
    funext ω
    field_simp
  rw [he, integral_const_mul, hβ.integral_eq, beta_mean _ _ (by positivity) zero_lt_one]
  ring

theorem iid_uniform_maximum_variance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (n : ℕ)
    {X : Fin (n + 1) → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) (hind : iIndepFun X P) :
    Var[fun ω => sampleMaximum (fun i => X i ω); P] =
      θ ^ 2 * (n + 1) / ((n + 2) ^ 2 * (n + 3)) := by
  have hβ := iid_uniform_standardized_maximum_law n hθ hXm hX hind
  have he : (fun ω => sampleMaximum (fun i => X i ω)) =
      fun ω => θ * (sampleMaximum (fun i => X i ω) / θ) := by
    funext ω
    field_simp
  rw [he, variance_const_mul, hβ.variance_eq, beta_variance _ _ (by positivity) zero_lt_one]
  ring

theorem iid_uniform_maximum_memLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (n : ℕ)
    {X : Fin (n + 1) → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) (hind : iIndepFun X P) :
    MemLp (fun ω => sampleMaximum (fun i => X i ω)) 2 P := by
  have hβ := iid_uniform_standardized_maximum_law n hθ hXm hX hind
  have hb : MemLp (id : ℝ → ℝ) 2 (betaMeasure ((n : ℝ) + 1) 1) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr
      (beta_power_integrable _ _ (by positivity) zero_lt_one 2)
  have hlp := ((hβ.identDistrib HasLaw.id).memLp_iff.mpr hb).const_mul θ
  convert! hlp using 1
  funext ω
  field_simp

/-- The exact mean-square error decreases at order `1/N²` for `N=n+1` draws. -/
theorem iid_uniform_maximum_mse {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (n : ℕ)
    {X : Fin (n + 1) → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) (hind : iIndepFun X P) :
    (∫ ω, (sampleMaximum (fun i => X i ω) - θ) ^ 2 ∂P) =
      2 * θ ^ 2 / ((n + 2) * (n + 3)) := by
  change mse P (fun ω => sampleMaximum (fun i => X i ω)) θ = _
  rw [mse_eq_variance_add_bias_sq P (iid_uniform_maximum_memLp n hθ hXm hX hind), bias,
    iid_uniform_maximum_mean n hθ hXm hX hind,
    iid_uniform_maximum_variance n hθ hXm hX hind]
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp
  ring

theorem iid_uniform_maximum_consistent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) (hind : iIndepFun X P) :
    ConvergesInProbability P
      (fun n ω => sampleMaximum (fun i : Fin (n + 1) => X i ω)) (fun _ => θ) := by
  apply mean_square_implies_probability
  have hi (n) : iIndepFun (fun i : Fin (n + 1) => X i) P :=
    iIndepFun.precomp Fin.val_injective hind
  refine ⟨fun n => (iid_uniform_maximum_memLp n hθ (fun i => hXm i)
    (fun i => hX i) (hi n)).sub (memLp_const θ), ?_⟩
  simp_rw [sq_abs, iid_uniform_maximum_mse _ hθ (fun i => hXm i) (fun i => hX i) (hi _)]
  have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
  have h3 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 3)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 3)
  convert! (h2.mul h3).const_mul (2 * θ ^ 2) using 1 <;> simp [div_eq_mul_inv, mul_comm]

/-- At the usual square-root sample-size scale the error collapses to zero;
there is no nondegenerate normal limit at this scale. -/
theorem iid_uniform_maximum_superconsistent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) (hind : iIndepFun X P) :
    ConvergesInProbability P
      (fun (n : ℕ) ω => Real.sqrt (n + 1) *
        (sampleMaximum (fun i : Fin (n + 1) => X i ω) - θ)) (fun _ => 0) := by
  apply mean_square_implies_probability
  have hi (n) : iIndepFun (fun i : Fin (n + 1) => X i) P :=
    iIndepFun.precomp Fin.val_injective hind
  refine ⟨fun n => ?_, ?_⟩
  · simpa only [sub_zero, Pi.sub_apply] using! ((iid_uniform_maximum_memLp n hθ (fun i => hXm i)
      (fun i => hX i) (hi n)).sub (memLp_const θ)).const_mul (Real.sqrt (n + 1))
  · have hsqrt (n : ℕ) : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
      Real.sq_sqrt (by positivity)
    simp_rw [sub_zero, sq_abs, mul_pow, hsqrt,
      integral_const_mul, iid_uniform_maximum_mse _ hθ (fun i => hXm i) (fun i => hX i) (hi _)]
    have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
    apply squeeze_zero (fun (n : ℕ) => by positivity)
      (fun (n : ℕ) => show ((n : ℝ) + 1) * (2 * θ ^ 2 / (((n : ℝ) + 2) * ((n : ℝ) + 3))) ≤
        2 * θ ^ 2 * (1 / ((n : ℝ) + 2)) from ?_)
      (by simpa using h2.const_mul (2 * θ ^ 2))
    have hr : ((n : ℝ) + 1) / ((n : ℝ) + 3) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    calc
      _ = (2 * θ ^ 2 / ((n : ℝ) + 2)) * (((n : ℝ) + 1) / ((n : ℝ) + 3)) := by
        field_simp
      _ ≤ (2 * θ ^ 2 / ((n : ℝ) + 2)) * 1 :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring

/-- For a nonempty all-zero sample, halving any positive endpoint improves
its likelihood. The excluded maximum-zero case has no positive MLE. -/
theorem uniformEndpoint_zero_sample_no_maximum {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : ∀ i, x i = 0) {θ : ℝ} (hθ : 0 < θ) :
    (∏ i, uniformEndpointDensity θ (x i)) <
      ∏ i, uniformEndpointDensity (θ / 2) (x i) := by
  have hhalf : 0 < θ / 2 := by positivity
  simp only [hx, uniformEndpointDensity, mem_Icc, le_refl, true_and,
    if_pos hθ.le, if_pos hhalf.le, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_lt_pow_left₀ (one_div_lt_one_div_of_lt hhalf (by linarith))
    (by positivity) hn.ne'

theorem uniformEndpoint_ae_support (θ : ℝ) :
    ∀ᵐ x ∂uniformEndpointLaw θ, x ∈ Ioc 0 θ := by
  have : NullSingletonClass (uniformEndpointLaw θ) := by
    refine ⟨fun x => ?_⟩
    simp only [uniformEndpointLaw, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply (measurableSet_singleton x)]
    have hz : volume ({x} ∩ Icc 0 θ) = 0 :=
      measure_mono_null inter_subset_left (measure_singleton x)
    rw [hz, mul_zero]
  have hs : ∀ᵐ x ∂uniformEndpointLaw θ, x ∈ Icc 0 θ := by
    rw [ae_iff]
    change uniformEndpointLaw θ (Icc 0 θ)ᶜ = 0
    simp [uniformEndpointLaw, Measure.smul_apply,
      Measure.restrict_apply measurableSet_Icc.compl]
  have hne : ∀ᵐ x ∂uniformEndpointLaw θ, x ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hs, hne] with x hx h0
  exact ⟨lt_of_le_of_ne hx.1 (Ne.symm h0), hx.2⟩

theorem uniform_maximum_pos_le_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {θ : ℝ}
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) :
    ∀ᵐ ω ∂P, 0 < sampleMaximum (fun i => X i ω) ∧ sampleMaximum (fun i => X i ω) ≤ θ := by
  have hs : ∀ᵐ ω ∂P, ∀ i, X i ω ∈ Ioc 0 θ := ae_all_iff.mpr (fun i =>
    ((hX i).ae_iff (show Measurable (fun x : ℝ => x ∈ Ioc 0 θ) by measurability)).mpr
      (uniformEndpoint_ae_support θ))
  filter_upwards [hs] with ω hω
  exact ⟨lt_of_lt_of_le (hω ⟨0, hn⟩).1 (le_sampleMaximum (fun i => X i ω) ⟨0, hn⟩),
    (sampleMaximum_le_iff hn _ θ).mpr (fun i => (hω i).2)⟩

/-- Under the uniform sampling model the density maximizer conditions hold
almost surely. Independence is unnecessary for this finite-sample assertion. -/
theorem uniformEndpoint_maximizes_density_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {θ : ℝ}
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) :
    ∀ᵐ ω ∂P, 0 < sampleMaximum (fun i => X i ω) ∧
      ∀ t : ℝ, 0 < t → (∏ i, uniformEndpointDensity t (X i ω)) ≤
        ∏ i, uniformEndpointDensity (sampleMaximum (fun i => X i ω)) (X i ω) := by
  have hs : ∀ᵐ ω ∂P, ∀ i, X i ω ∈ Ioc 0 θ := ae_all_iff.mpr (fun i =>
    ((hX i).ae_iff (show Measurable (fun x : ℝ => x ∈ Ioc 0 θ) by measurability)).mpr
      (uniformEndpoint_ae_support θ))
  filter_upwards [hs, uniform_maximum_pos_le_ae hn hX] with ω hω hmax
  exact ⟨hmax.1, fun t ht => uniformEndpoint_maximizes_density hn _
    (fun i => (hω i).1.le) hmax.1 ht⟩

end LectureNotes
