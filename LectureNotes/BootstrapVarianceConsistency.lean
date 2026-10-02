import LectureNotes.BootstrapConditionalCLT
import LectureNotes.BootstrapVarianceMoments

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
attribute [local instance] bootstrapLaw_isProbabilityMeasure

/-- Markov's inequality applied to the squared absolute error, in real-valued
probability form. -/
theorem measureReal_abs_ge_le_secondMoment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : MemLp Y 2 P) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |Y ω|} ≤ (∫ ω, Y ω ^ 2 ∂P) / ε ^ 2 := by
  have hs : {ω | ε ≤ |Y ω|} = {ω | ε ^ 2 ≤ Y ω ^ 2} := by
    ext ω
    simp only [mem_setOf_eq, sq_le_sq, abs_of_pos hε]
  rw [hs]
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (fun ω => sq_nonneg (Y ω))) hY.integrable_sq (ε ^ 2)
  exact (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by nlinarith)

/-- Squaring the sample mean introduces only a local Lipschitz factor. -/
theorem empiricalVariance_deviation_bound {n : ℕ} (x b : Fin n → ℝ) :
    |empiricalVariance b - empiricalVariance x| ≤
      |sampleMean (fun i => b i ^ 2) - sampleMean (fun i => x i ^ 2)| +
      |sampleMean b - sampleMean x| * (|sampleMean b - sampleMean x| + 2 * |sampleMean x|) := by
  rw [empiricalVariance_eq_secondMoment_sub_sq, empiricalVariance_eq_secondMoment_sub_sq]
  have he : sampleMean (fun i => b i ^ 2) - sampleMean b ^ 2 -
      (sampleMean (fun i => x i ^ 2) - sampleMean x ^ 2) =
      (sampleMean (fun i => b i ^ 2) - sampleMean (fun i => x i ^ 2)) -
        (sampleMean b - sampleMean x) * (sampleMean b - sampleMean x + 2 * sampleMean x) := by ring
  rw [he]
  calc
    _ ≤ |sampleMean (fun i => b i ^ 2) - sampleMean (fun i => x i ^ 2)| +
        |(sampleMean b - sampleMean x) * (sampleMean b - sampleMean x + 2 * sampleMean x)| :=
      abs_sub _ _
    _ ≤ _ := by
      rw [abs_mul]
      gcongr
      calc
        _ ≤ |sampleMean b - sampleMean x| + |2 * sampleMean x| := abs_add_le _ _
        _ = _ := by rw [abs_mul]; norm_num

/-- On bounded observed centers, two small raw-moment errors give a small
empirical-variance error. -/
theorem empiricalVariance_deviation_small {n : ℕ} (x b : Fin n → ℝ)
    {M ε δ : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : δ * (1 + 2 * M) ≤ ε / 2)
    (hcenter : |sampleMean x| ≤ M)
    (hmean : |sampleMean b - sampleMean x| < δ)
    (hsecond : |sampleMean (fun i => b i ^ 2) - sampleMean (fun i => x i ^ 2)| < ε / 2) :
    |empiricalVariance b - empiricalVariance x| < ε := by
  have hbound := empiricalVariance_deviation_bound x b
  have hf : |sampleMean b - sampleMean x| + 2 * |sampleMean x| ≤ 1 + 2 * M := by linarith
  have hh : |sampleMean b - sampleMean x| *
      (|sampleMean b - sampleMean x| + 2 * |sampleMean x|) < ε / 2 := by
    calc
      _ ≤ |sampleMean b - sampleMean x| * (1 + 2 * M) :=
        mul_le_mul_of_nonneg_left hf (abs_nonneg _)
      _ < δ * (1 + 2 * M) := mul_lt_mul_of_pos_right hmean (by positivity)
      _ ≤ ε / 2 := hδe
  linarith

/-- Mean-square errors tending to zero imply rowwise convergence in probability,
even when the sample space and measure vary with the row. -/
theorem row_secondMoment_implies_probability {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {Y : ∀ n, Ω n → ℝ}
    (hY : ∀ n, MemLp (Y n) 2 (P n))
    (hM : Tendsto (fun n => ∫ ω, Y n ω ^ 2 ∂(P n)) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ |Y n ω|}) atTop (𝓝 0) := by
  intro ε hε
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => measureReal_abs_ge_le_secondMoment (hY n) hε)
    (by simpa only [zero_div] using hM.div_const (ε ^ 2))

/-- Continuity at a constant preserves rowwise convergence in probability.
This statement needs no relation between different row sample spaces. -/
theorem row_probability_continuous_mapping_const {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {Y : ∀ n, Ω n → ℝ} {c : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousAt g c)
    (hY : ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ |Y n ω - c|}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ |g (Y n ω) - g c|}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Metric.continuousAt_iff.mp hg ε hε
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (hY δ hδ)
  intro n
  refine measureReal_mono ?_ (measure_ne_top (P n) _)
  intro ω hω
  by_contra hsmall
  have hs : dist (Y n ω) c < δ := by simpa only [Real.dist_eq] using lt_of_not_ge hsmall
  have hh := hbound hs
  simp only [Real.dist_eq] at hh
  exact (not_lt_of_ge hω) hh

/-- Converging deterministic centers may be replaced by their limit in
rowwise convergence in probability. -/
theorem row_probability_center_limit {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {Y : ∀ n, Ω n → ℝ} {c : ℕ → ℝ} {a : ℝ}
    (hc : Tendsto c atTop (𝓝 a))
    (hY : ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ |Y n ω - c n|}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ |Y n ω - a|}) atTop (𝓝 0) := by
  intro ε hε
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ (hY (ε / 2) (by positivity))
  have he : ∀ᶠ n in atTop, |c n - a| < ε / 2 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hc (ε / 2) (by positivity))
  filter_upwards [he] with n hn
  refine measureReal_mono ?_ (measure_ne_top (P n) _)
  intro ω hω
  by_contra hh
  change ε ≤ |Y n ω - a| at hω
  have hsmall : |Y n ω - c n| < ε / 2 := lt_of_not_ge hh
  have hb : |Y n ω - a| ≤ |Y n ω - c n| + |c n - a| := by
    simpa only [sub_add_sub_cancel] using abs_add_le (Y n ω - c n) (c n - a)
  linarith

/-- Consistent bootstrap first and second raw moments give a consistent
bootstrap empirical variance, relative to the observed empirical variance. -/
theorem bootstrap_variance_rows_of_moments (x : ∀ n : ℕ, Fin (n + 1) → ℝ)
    {μ : ℝ} (hm : Tendsto (fun n => sampleMean (x n)) atTop (𝓝 μ))
    (hmean : ∀ ε > 0, Tendsto (fun n => (bootstrapLaw (x n)).real
      {b | ε ≤ |sampleMean b - sampleMean (x n)|}) atTop (𝓝 0))
    (hsecond : ∀ ε > 0, Tendsto (fun n => (bootstrapLaw (x n)).real
      {b | ε ≤ |sampleMean (fun i => b i ^ 2) - sampleMean (fun i => x n i ^ 2)|})
        atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (bootstrapLaw (x n)).real
      {b | ε ≤ |empiricalVariance b - empiricalVariance (x n)|}) atTop (𝓝 0) := by
  intro ε hε
  let M := |μ| + 1
  have hM : 0 ≤ M := by unfold M; positivity
  have hMp : 0 < 1 + 2 * M := by positivity
  let δ := min 1 (ε / (2 * (1 + 2 * M)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδe : δ * (1 + 2 * M) ≤ ε / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (1 + 2 * M))).mp
      (min_le_right 1 (ε / (2 * (1 + 2 * M))))
    dsimp only [δ]
    nlinarith
  have hbound : ∀ᶠ n in atTop, |sampleMean (x n)| ≤ M :=
    ((hm.abs).eventually (gt_mem_nhds (by dsimp only [M]; linarith))).mono (fun _ h => h.le)
  have hlim := (hsecond (ε / 2) (by positivity)).add (hmean δ hδ)
  simp only [zero_add] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  filter_upwards [hbound] with n hn
  have hs : {b : Fin (n + 1) → ℝ | ε ≤ |empiricalVariance b - empiricalVariance (x n)|} ⊆
      {b | ε / 2 ≤ |sampleMean (fun i => b i ^ 2) - sampleMean (fun i => x n i ^ 2)|} ∪
      {b | δ ≤ |sampleMean b - sampleMean (x n)|} := by
    intro b hb
    by_contra hh
    have hsecond' : |sampleMean (fun i => b i ^ 2) - sampleMean (fun i => x n i ^ 2)| < ε / 2 :=
      lt_of_not_ge (fun h => hh (Or.inl h))
    have hmean' : |sampleMean b - sampleMean (x n)| < δ :=
      lt_of_not_ge (fun h => hh (Or.inr h))
    exact (not_lt_of_ge hb) (empiricalVariance_deviation_small (x n) b hM hε hδ hδ1 hδe hn hmean' hsecond')
  exact (measureReal_mono hs).trans (measureReal_union_le _ _)

/-- Deterministic observed moment convergence implies conditional bootstrap
variance consistency. The fourth moment controls resampling fluctuations of
the second raw moment; no conditional limit theorem is assumed. -/
theorem bootstrap_variance_rows_consistent (x : ∀ n : ℕ, Fin (n + 1) → ℝ)
    {μ v κ : ℝ}
    (hm : Tendsto (fun n => sampleMean (x n)) atTop (𝓝 μ))
    (hv : Tendsto (fun n => empiricalVariance (x n)) atTop (𝓝 v))
    (hfour : Tendsto (fun n => sampleMean (fun i => x n i ^ 4)) atTop (𝓝 κ)) :
    ∀ ε > 0, Tendsto (fun n => (bootstrapLaw (x n)).real
      {b | ε ≤ |empiricalVariance b - v|}) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hmeanLp n : MemLp (fun b : Fin (n + 1) → ℝ => sampleMean b - sampleMean (x n))
      2 (bootstrapLaw (x n)) := by
    simpa only [id_eq, Pi.sub_apply] using!
      (bootstrap_transformed_sampleMean_memLp (x n) measurable_id).sub
        (memLp_const (sampleMean (x n)))
  have hsecondLp n : MemLp (fun b : Fin (n + 1) → ℝ => sampleMean (fun i => b i ^ 2) -
      sampleMean (fun i => x n i ^ 2)) 2 (bootstrapLaw (x n)) := by
    simpa only [Pi.sub_apply] using!
      (bootstrap_transformed_sampleMean_memLp (x n)
        (by fun_prop : Measurable (fun y : ℝ => y ^ 2))).sub
        (memLp_const (sampleMean (fun i => x n i ^ 2)))
  have hmse : Tendsto (fun n => ∫ b, (sampleMean b - sampleMean (x n)) ^ 2
      ∂bootstrapLaw (x n)) atTop (𝓝 0) := by
    simp_rw [bootstrap_sampleMean_mse]
    simpa only [div_eq_mul_inv, mul_zero] using hv.mul hn
  have hsse : Tendsto (fun n => ∫ b, (sampleMean (fun i => b i ^ 2) -
      sampleMean (fun i => x n i ^ 2)) ^ 2 ∂bootstrapLaw (x n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg (fun b => sq_nonneg _))
      (fun n => bootstrap_secondMoment_mse_le (x n))
    simpa only [div_eq_mul_inv, mul_zero] using hfour.mul hn
  exact row_probability_center_limit hv
    (bootstrap_variance_rows_of_moments x hm
      (row_secondMoment_implies_probability hmeanLp hmse)
      (row_secondMoment_implies_probability hsecondLp hsse))

/-- Conditional consistency of the bootstrap empirical variance, almost surely
under IID sampling with a finite fourth moment. -/
theorem iid_bootstrap_variance_consistent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, ∀ ε > 0, Tendsto
      (fun n => (bootstrapLaw (fun i : Fin (n + 1) => X i ω)).real
        {b | ε ≤ |empiricalVariance b - Var[X 0; P]|}) atTop (𝓝 0) := by
  have h₂ : MemLp (X 0) 2 P := hX.mono_exponent (by norm_num)
  have hfour : Integrable (fun ω => X 0 ω ^ 4) P := by
    have hh := hX.integrable_norm_pow' (p := 4)
    simpa only [Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs] using hh
  have hfourMean := iid_sampleMean_succ_ae (X := fun i ω => X i ω ^ 4)
    hfour (hind.comp (fun _ x => x ^ 4) (fun _ => by fun_prop))
    (fun i => (hident i).comp (by fun_prop : Measurable (fun x : ℝ => x ^ 4)))
  filter_upwards [iid_sampleMean_succ_ae (h₂.integrable (by norm_num)) hind hident,
    empiricalVariance_strong_consistency hXm h₂ hind hident, hfourMean] with ω hm hv hf
  have hv' := hv.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n => empiricalVariance (fun i : Fin (n + 1) => X i ω))
    atTop (𝓝 (Var[X 0; P])) at hv'
  exact bootstrap_variance_rows_consistent (fun n i => X i ω) hm hv' hf

/-- The resampling standard deviation divided by the population standard
deviation tends to one conditionally. Zero-variance finite resamples are
included: their probability vanishes, rather than being excluded by premise. -/
theorem iid_bootstrap_studentization_factor {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : MemLp (X 0) 4 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (σ : ℝ) (hσ : 0 < σ) (hvar : Var[X 0; P] = σ ^ 2) :
    ∀ᵐ ω ∂P, ∀ ε > 0, Tendsto
      (fun n => (bootstrapLaw (fun i : Fin (n + 1) => X i ω)).real
        {b | ε ≤ |Real.sqrt (empiricalVariance b) / σ - 1|}) atTop (𝓝 0) := by
  filter_upwards [iid_bootstrap_variance_consistent hXm hX hind hident] with ω hω
  rw [hvar] at hω
  have hh := row_probability_continuous_mapping_const
    (P := fun n => bootstrapLaw (fun i : Fin (n + 1) => X i ω))
    (Y := fun n (b : Fin (n + 1) → ℝ) => empiricalVariance b)
    (g := fun v => Real.sqrt v / σ) (by fun_prop) hω
  simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hσ, div_self hσ.ne'] using hh

end LectureNotes
