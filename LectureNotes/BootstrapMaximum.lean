import LectureNotes.Bootstrap
import LectureNotes.UniformEndpoint

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology Classical

instance bootstrapIndexLaw_probability (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (bootstrapIndexLaw n) := inferInstanceAs
      (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype (Fin n)).toMeasure)))

/-- A with-replacement bootstrap maximum never exceeds the observed maximum. -/
theorem bootstrapMaximum_le {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (b : Fin n → Fin n) : sampleMaximum (bootstrapSample x b) ≤ sampleMaximum x := by
  exact (sampleMaximum_le_iff hn _ _).mpr (fun i => le_sampleMaximum x (b i))

/-- Exact chance of selecting a specified original observation at least once. -/
theorem bootstrapIndex_hit_probability {n : ℕ} [NeZero n] (j : Fin n) :
    (bootstrapIndexLaw n).real {b | ∃ i, b i = j} = 1 - (1 - 1/(n : ℝ))^n := by
  let μ := (PMF.uniformOfFintype (Fin n)).toMeasure
  have hsingle : μ.real {j} = 1/(n : ℝ) := by
    simp [μ, measureReal_def, PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply]
  have havoid : {b : Fin n → Fin n | ∀ i, b i ≠ j} =
      Set.pi univ (fun _ : Fin n => ({j} : Set (Fin n))ᶜ) := by ext b; simp
  have ha : (bootstrapIndexLaw n).real {b | ∀ i, b i ≠ j} = (1-1/(n : ℝ))^n := by
    rw [havoid, measureReal_def, bootstrapIndexLaw, Measure.pi_pi, ENNReal.toReal_prod]
    change (∏ i : Fin n, μ.real ({j}ᶜ)) = _
    rw [measureReal_compl (measurableSet_singleton j), hsingle]
    simp
  have he : {b : Fin n → Fin n | ∃ i, b i = j} = {b | ∀ i, b i ≠ j}ᶜ := by
    ext b; simp
  rw [he, measureReal_compl (Set.to_countable _ |>.measurableSet), ha, probReal_univ]

/-- The no-hit probability stays at most one half, uniformly in sample size. -/
theorem bootstrapIndex_miss_le_half {n : ℕ} (hn : 0 < n) :
    (1 - 1/(n : ℝ))^n ≤ 1/2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ 1 - 1/(n : ℝ) := by rw [sub_nonneg, div_le_one hn']; exact hone
  have hx : 0 ≤ 1/(n : ℝ) := by positivity
  have hbase : (1 - 1/(n : ℝ)) * (1 + 1/(n : ℝ)) ≤ 1 := by nlinarith [sq_nonneg (1/(n : ℝ))]
  have hprod : (1 - 1/(n : ℝ))^n * (1 + 1/(n : ℝ))^n ≤ 1 := by
    rw [← mul_pow]
    simpa using pow_le_pow_left₀ (mul_nonneg hp (by positivity)) hbase n
  have hber : 2 ≤ (1 + 1/(n : ℝ))^n := by
    have h := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ 1/(n : ℝ)) n
    have hcancel : (n : ℝ) * (1/(n : ℝ)) = 1 := by field_simp
    rw [hcancel] at h
    norm_num only [one_add_one_eq_two] at h
    exact h
  nlinarith [pow_nonneg hp n]

/-- The conditional bootstrap maximum has a persistent atom at the observed
maximum, even when the original sampling law is continuous. Ties only increase it. -/
theorem bootstrapMaximum_atom_ge_half {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    1/2 ≤ (bootstrapIndexLaw n).real {b | sampleMaximum (bootstrapSample x b) = sampleMaximum x} := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨j, hj⟩ := Finite.exists_max x
  have he : sampleMaximum x = x j := le_antisymm
    ((sampleMaximum_le_iff hn _ _).mpr hj) (le_sampleMaximum x j)
  have hs : {b : Fin n → Fin n | ∃ i, b i = j} ⊆
      {b | sampleMaximum (bootstrapSample x b) = sampleMaximum x} := by
    rintro b ⟨i, hi⟩
    apply le_antisymm (bootstrapMaximum_le hn x b)
    rw [he, ← hi]
    exact le_sampleMaximum (bootstrapSample x b) i
  have hm := measureReal_mono (μ := bootstrapIndexLaw n) hs (measure_ne_top _ _)
  rw [bootstrapIndex_hit_probability] at hm
  linarith [bootstrapIndex_miss_le_half hn]


/-- The nonnegative root used for upper-endpoint inference. -/
def bootstrapMaximumGap {n : ℕ} (x : Fin n → ℝ) (b : Fin n → Fin n) : ℝ :=
  (n : ℝ) * (sampleMaximum x - sampleMaximum (bootstrapSample x b))

theorem bootstrapMaximumGap_cdf_zero_ge_half {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    1/2 ≤ cdf ((bootstrapIndexLaw n).map (bootstrapMaximumGap x)) 0 := by
  have : IsProbabilityMeasure ((bootstrapIndexLaw n).map (bootstrapMaximumGap x)) :=
    Measure.isProbabilityMeasure_map (Measurable.of_discrete : Measurable (bootstrapMaximumGap x)).aemeasurable
  rw [cdf_eq_real, measureReal_def,
    Measure.map_apply (show Measurable (bootstrapMaximumGap x) from Measurable.of_discrete)
      measurableSet_Iic]
  apply (bootstrapMaximum_atom_ge_half x).trans
  apply measureReal_mono (μ := bootstrapIndexLaw n) _ (measure_ne_top _ _)
  intro b hb
  change (n : ℝ) * (sampleMaximum x - sampleMaximum (bootstrapSample x b)) ≤ 0
  rw [hb, sub_self, mul_zero]

/-- A uniform variable is strictly below its positive endpoint almost surely. -/
theorem uniformEndpoint_ae_lt {θ : ℝ} (hθ : 0 < θ) :
    ∀ᵐ x ∂uniformEndpointLaw θ, x < θ := by
  have hs := uniformEndpoint_ae_support θ
  have hz : uniformEndpointLaw θ {θ} = 0 := by
    simp only [uniformEndpointLaw, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (measurableSet_singleton θ)]
    have he : volume ({θ} ∩ Icc 0 θ) = 0 :=
      measure_mono_null inter_subset_left (measure_singleton θ)
    rw [he, mul_zero]
  have hn : ∀ᵐ x ∂uniformEndpointLaw θ, x ≠ θ := by simpa [ae_iff] using hz
  filter_upwards [hs, hn] with x hx hne
  exact lt_of_le_of_ne hx.2 hne

theorem uniform_maximum_lt_endpoint_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) :
    ∀ᵐ ω ∂P, sampleMaximum (fun i => X i ω) < θ := by
  have hs : ∀ᵐ ω ∂P, ∀ i, X i ω < θ := ae_all_iff.mpr (fun i =>
    ((hX i).ae_iff (show Measurable (fun x : ℝ => x < θ) by measurability)).mpr
      (uniformEndpoint_ae_lt hθ))
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  filter_upwards [hs] with ω hω
  obtain ⟨j, hj⟩ := Finite.exists_max (fun i => X i ω)
  exact ((sampleMaximum_le_iff hn _ _).mpr hj).trans_lt (hω j)

/-- The true endpoint error has zero CDF at zero under continuous uniform
sampling, whereas the conditional bootstrap CDF is at least one half there.
Thus even the finite-sample CDF approximation error cannot vanish. -/
theorem uniform_bootstrapMaximum_cdf_gap {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} [NeZero n]
    {X : Fin n → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P)
    (x : Fin n → ℝ) :
    1/2 ≤ |cdf ((bootstrapIndexLaw n).map (bootstrapMaximumGap x)) 0 -
      cdf (P.map (fun ω => (n : ℝ) * (θ - sampleMaximum (fun i => X i ω)))) 0| := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hG : Measurable (fun ω => (n : ℝ) * (θ - sampleMaximum (fun i => X i ω))) :=
    measurable_const.mul (measurable_const.sub (sampleMaximum_measurable X hXm))
  have : IsProbabilityMeasure (P.map (fun ω => (n : ℝ) * (θ - sampleMaximum (fun i => X i ω)))) :=
    Measure.isProbabilityMeasure_map hG.aemeasurable
  have hpos : ∀ᵐ ω ∂P, 0 < (n : ℝ) * (θ - sampleMaximum (fun i => X i ω)) :=
    (uniform_maximum_lt_endpoint_ae hn hθ hX).mono (fun _ h => mul_pos (by positivity) (sub_pos.mpr h))
  have hz : cdf (P.map (fun ω => (n : ℝ) * (θ - sampleMaximum (fun i => X i ω)))) 0 = 0 := by
    rw [cdf_eq_real, measureReal_def, Measure.map_apply hG measurableSet_Iic]
    have he : P {ω | (n : ℝ) * (θ - sampleMaximum (fun i => X i ω)) ≤ 0} = 0 := by
      simpa only [ae_iff, not_lt] using hpos
    change (P {ω | (n : ℝ) * (θ - sampleMaximum (fun i => X i ω)) ≤ 0}).toReal = 0
    rw [he, ENNReal.toReal_zero]
  rw [hz, sub_zero, abs_of_nonneg (cdf_nonneg _ _)]
  exact bootstrapMaximumGap_cdf_zero_ge_half x

end LectureNotes
