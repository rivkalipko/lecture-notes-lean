import LectureNotes.NormalConjugacy
import LectureNotes.Testing

set_option autoImplicit false

/-! L12 analytic posterior approximation. These results prove convergence of
normalized kernels from convergence and domination of unnormalized kernels.
Neither posterior convergence nor a normal approximation is assumed. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {Θ : Type*} [MeasurableSpace Θ] {ν : Measure Θ}

def normalizedKernel (ν : Measure Θ) (q : Θ → ℝ) (θ : Θ) : ℝ := q θ / evidence ν q

theorem normalizedKernel_integrable {q : Θ → ℝ} (hq : Integrable q ν) :
    Integrable (normalizedKernel ν q) ν := hq.div_const _

/-- L1 convergence of unnormalized integrable kernels and convergence of their
nonzero normalizers give L1 convergence after normalization. -/
theorem normalized_kernel_L1_of_L1 {q : ℕ → Θ → ℝ} {f : Θ → ℝ}
    (hq : ∀ n, Integrable (q n) ν) (hf : Integrable f ν)
    (he : evidence ν f ≠ 0)
    (hmass : Tendsto (fun n => evidence ν (q n)) atTop (𝓝 (evidence ν f)))
    (hL1 : Tendsto (fun n => ∫ θ, |q n θ - f θ| ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ θ, |normalizedKernel ν (q n) θ - normalizedKernel ν f θ| ∂ν)
      atTop (𝓝 0) := by
  have hb (n) :
      (∫ θ, |normalizedKernel ν (q n) θ - normalizedKernel ν f θ| ∂ν) ≤
        |(evidence ν (q n))⁻¹| * (∫ θ, |q n θ - f θ| ∂ν) +
          |(evidence ν (q n))⁻¹ - (evidence ν f)⁻¹| * (∫ θ, |f θ| ∂ν) := by
    have hpoint (θ) : |normalizedKernel ν (q n) θ - normalizedKernel ν f θ| ≤
        |(evidence ν (q n))⁻¹| * |q n θ - f θ| +
          |(evidence ν (q n))⁻¹ - (evidence ν f)⁻¹| * |f θ| := by
      have hrewrite : normalizedKernel ν (q n) θ - normalizedKernel ν f θ =
          (evidence ν (q n))⁻¹ * (q n θ - f θ) +
            ((evidence ν (q n))⁻¹ - (evidence ν f)⁻¹) * f θ := by
        unfold normalizedKernel
        simp only [div_eq_mul_inv]
        ring
      rw [hrewrite]
      simpa only [abs_mul] using abs_add_le
        ((evidence ν (q n))⁻¹ * (q n θ - f θ))
        (((evidence ν (q n))⁻¹ - (evidence ν f)⁻¹) * f θ)
    have hnorm : Integrable (fun θ => |normalizedKernel ν (q n) θ - normalizedKernel ν f θ|) ν :=
      ((normalizedKernel_integrable (hq n)).sub (normalizedKernel_integrable hf)).abs
    have h₁ : Integrable (fun θ => |(evidence ν (q n))⁻¹| * |q n θ - f θ|) ν :=
      ((hq n).sub hf).abs.const_mul |(evidence ν (q n))⁻¹|
    have h₂ : Integrable (fun θ => |(evidence ν (q n))⁻¹ - (evidence ν f)⁻¹| * |f θ|) ν :=
      hf.abs.const_mul |(evidence ν (q n))⁻¹ - (evidence ν f)⁻¹|
    have hi := integral_mono hnorm (h₁.add h₂) hpoint
    change (∫ θ, |normalizedKernel ν (q n) θ - normalizedKernel ν f θ| ∂ν) ≤
      ∫ θ, |(evidence ν (q n))⁻¹| * |q n θ - f θ| +
        |(evidence ν (q n))⁻¹ - (evidence ν f)⁻¹| * |f θ| ∂ν at hi
    rw [integral_add h₁ h₂, integral_const_mul, integral_const_mul] at hi
    exact hi
  have hinv := hmass.inv₀ he
  have hzero : Tendsto (fun n => |(evidence ν (q n))⁻¹| *
      (∫ θ, |q n θ - f θ| ∂ν) +
        |(evidence ν (q n))⁻¹ - (evidence ν f)⁻¹| * (∫ θ, |f θ| ∂ν)) atTop (𝓝 0) := by
    simpa using (hinv.abs.mul hL1).add
      ((hinv.sub_const (evidence ν f)⁻¹).abs.mul_const (∫ θ, |f θ| ∂ν))
  exact squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _)) hb hzero

/-- An integrable envelope and pointwise almost-everywhere kernel convergence
are sufficient for normalized L1 convergence. This is a genuine analytic
condition on unnormalized likelihood/prior products. -/
theorem normalized_kernel_L1_of_dominated {q : ℕ → Θ → ℝ} {f bound : Θ → ℝ}
    (hq : ∀ n, AEStronglyMeasurable (q n) ν) (hf : Integrable f ν)
    (hb : Integrable bound ν) (hbound : ∀ n, ∀ᵐ θ ∂ν, ‖q n θ‖ ≤ bound θ)
    (hlim : ∀ᵐ θ ∂ν, Tendsto (fun n => q n θ) atTop (𝓝 (f θ)))
    (he : evidence ν f ≠ 0) :
    Tendsto (fun n => ∫ θ, |normalizedKernel ν (q n) θ - normalizedKernel ν f θ| ∂ν)
      atTop (𝓝 0) := by
  have hqi (n) : Integrable (q n) ν := hb.mono' (hq n) (hbound n)
  have hm := tendsto_integral_of_dominated_convergence bound hq hb hbound hlim
  apply normalized_kernel_L1_of_L1 hqi hf he hm
  have hdom : ∀ n, ∀ᵐ θ ∂ν, ‖|q n θ - f θ|‖ ≤ bound θ + |f θ| := by
    intro n
    filter_upwards [hbound n] with θ hθ
    calc
      ‖|q n θ - f θ|‖ = ‖q n θ - f θ‖ := by simp [Real.norm_eq_abs]
      _ ≤ ‖q n θ‖ + ‖f θ‖ := norm_sub_le _ _
      _ ≤ bound θ + |f θ| := by simpa [Real.norm_eq_abs] using add_le_add_right hθ ‖f θ‖
  have hh := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun θ => bound θ + |f θ|)
    (fun n => by simpa only [Real.norm_eq_abs, Pi.sub_apply] using!
      ((hq n).sub hf.aestronglyMeasurable).norm) (hb.add hf.abs) hdom
    (hlim.mono (fun θ hθ => by simpa using (hθ.sub_const (f θ)).abs))
  simpa using hh

theorem bayesUpdate_event_eq_integral {q : Θ → ℝ} (hq : Integrable q ν)
    (hn : ∀ᵐ θ ∂ν, 0 ≤ q θ) (he : 0 < evidence ν q)
    (A : Set Θ) (hA : MeasurableSet A) :
    (bayesUpdate ν q).real A = ∫ θ in A, normalizedKernel ν q θ ∂ν := by
  letI := bayesUpdate_isProbabilityMeasure ν q hq hn he
  rw [measureReal_def, bayesUpdate, withDensity_apply _ hA]
  rw [← ofReal_integral_eq_lintegral_ofReal (hq.div_const _).integrableOn
    ((ae_restrict_of_ae hn).mono (fun θ hθ => div_nonneg hθ he.le)),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae
      ((ae_restrict_of_ae hn).mono (fun θ hθ => div_nonneg hθ he.le)))]
  rfl

/-- L1 approximation controls posterior probability errors for every measurable
event, uniformly over the event chosen. -/
theorem posterior_event_error_le_L1 {q f : Θ → ℝ}
    (hq : Integrable q ν) (hf : Integrable f ν)
    (hq0 : ∀ᵐ θ ∂ν, 0 ≤ q θ) (hf0 : ∀ᵐ θ ∂ν, 0 ≤ f θ)
    (heq : 0 < evidence ν q) (hef : 0 < evidence ν f)
    (A : Set Θ) (hA : MeasurableSet A) :
    |(bayesUpdate ν q).real A - (bayesUpdate ν f).real A| ≤
      ∫ θ, |normalizedKernel ν q θ - normalizedKernel ν f θ| ∂ν := by
  rw [bayesUpdate_event_eq_integral hq hq0 heq A hA,
    bayesUpdate_event_eq_integral hf hf0 hef A hA,
    ← integral_sub (normalizedKernel_integrable hq).integrableOn
      (normalizedKernel_integrable hf).integrableOn]
  apply abs_integral_le_integral_abs.trans
  exact setIntegral_le_integral
    (((normalizedKernel_integrable hq).sub (normalizedKernel_integrable hf)).abs)
    (ae_of_all _ (fun _ => abs_nonneg _))

/-- The unnormalized Gaussian kernel is integrable for positive variance. -/
theorem gaussian_kernel_integrable (μ : ℝ) (v : ℝ≥0) (hv : 0 < v) :
    Integrable (fun θ : ℝ => Real.exp (-(θ - μ) ^ 2 / (2 * v))) volume := by
  have hc : Real.sqrt (2 * Real.pi * v) ≠ 0 := by
    apply (Real.sqrt_pos.mpr _).ne'
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (by exact_mod_cast hv)
  have h := (integrable_gaussianPDFReal μ v).const_mul (Real.sqrt (2 * Real.pi * v))
  convert h using 1
  ext θ
  unfold gaussianPDFReal
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- An explicit error bound tending to zero controls *every* measurable
posterior event. The bound is independent of the event, so this is uniform
probability approximation, not just weak convergence at fixed intervals. -/
theorem posterior_gaussian_approximation {q : ℕ → ℝ → ℝ} {bound : ℝ → ℝ}
    {c : ℝ} (hc : 0 < c) (v : ℝ≥0) (hv : 0 < v)
    (hq : ∀ n, AEStronglyMeasurable (q n) volume)
    (hq0 : ∀ n, ∀ᵐ z ∂volume, 0 ≤ q n z)
    (hb : Integrable bound volume) (hbound : ∀ n, ∀ᵐ z ∂volume, ‖q n z‖ ≤ bound z)
    (he : ∀ n, 0 < evidence volume (q n))
    (hlim : ∀ᵐ z ∂volume, Tendsto (fun n => q n z) atTop
      (𝓝 (c * Real.exp (-z ^ 2 / (2 * v))))) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (𝓝 0) ∧
      ∀ n A, MeasurableSet A →
        |(bayesUpdate volume (q n)).real A - (gaussianReal 0 v).real A| ≤ error n := by
  let f : ℝ → ℝ := fun z => c * Real.exp (-z ^ 2 / (2 * v))
  have hkernel : Integrable (fun z : ℝ => Real.exp (-z ^ 2 / (2 * v))) volume := by
    simpa using gaussian_kernel_integrable 0 v hv
  have hf : Integrable f volume := hkernel.const_mul c
  have hf0 : ∀ᵐ z ∂volume, 0 ≤ f z := ae_of_all _ (fun z => mul_nonneg hc.le (Real.exp_pos _).le)
  have hef : 0 < evidence volume f := by
    change 0 < ∫ z : ℝ, c * Real.exp (-z ^ 2 / (2 * v))
    rw [integral_const_mul]
    exact mul_pos hc (integral_exp_pos hkernel)
  have hqi (n) : Integrable (q n) volume := hb.mono' (hq n) (hbound n)
  have hnorm : bayesUpdate volume f = gaussianReal 0 v := by
    rw [show f = fun z => c * Real.exp (-z ^ 2 / (2 * v)) from rfl,
      bayesUpdate_scale _ _ hc.ne']
    simpa using normalized_gaussian_kernel 0 v hv
  refine ⟨fun n => ∫ z, |normalizedKernel volume (q n) z - normalizedKernel volume f z|,
    fun _ => integral_nonneg (fun _ => abs_nonneg _),
    normalized_kernel_L1_of_dominated hq hf hb hbound hlim hef.ne', ?_⟩
  intro n A hA
  rw [← hnorm]
  exact posterior_event_error_le_L1 (hqi n) hf (hq0 n) hf0 (he n) hef A hA

/-- The posterior kernel in coordinates z = rₙ(θ−tₙ), with the value of the
log-likelihood at the center removed. Its constant Jacobian cancels on normalization. -/
def localPosteriorKernel (logL : ℕ → ℝ → ℝ) (prior : ℝ → ℝ)
    (center rate : ℕ → ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  prior (center n + z / rate n) *
    Real.exp (logL n (center n + z / rate n) - logL n (center n))

/-- Scalar posterior Gaussian approximation under explicit local asymptotic
quadraticity and an integrable envelope. Continuity and positivity of the prior
at the true parameter are sufficient; it need not be flat elsewhere. -/
theorem local_posterior_gaussian_approximation
    (logL : ℕ → ℝ → ℝ) (prior : ℝ → ℝ) (center rate : ℕ → ℝ)
    (θ₀ : ℝ) (v : ℝ≥0) (hv : 0 < v)
    (hprior : Measurable prior) (hprior0 : ∀ θ, 0 ≤ prior θ)
    (hpriorCont : ContinuousAt prior θ₀) (hpriorPos : 0 < prior θ₀)
    (hlogL : ∀ n, Measurable (logL n))
    (hcenter : Tendsto center atTop (𝓝 θ₀))
    (hrate : Tendsto (fun n => (rate n)⁻¹) atTop (𝓝 0))
    (hquadratic : ∀ z, Tendsto
      (fun n => logL n (center n + z / rate n) - logL n (center n)) atTop
      (𝓝 (-z ^ 2 / (2 * v))))
    (bound : ℝ → ℝ) (hb : Integrable bound volume)
    (hbound : ∀ n, ∀ᵐ z ∂volume, ‖localPosteriorKernel logL prior center rate n z‖ ≤ bound z)
    (he : ∀ n, 0 < evidence volume (localPosteriorKernel logL prior center rate n)) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (𝓝 0) ∧
      ∀ n A, MeasurableSet A →
        |(bayesUpdate volume (localPosteriorKernel logL prior center rate n)).real A -
          (gaussianReal 0 v).real A| ≤ error n := by
  apply posterior_gaussian_approximation hpriorPos v hv
  · intro n
    apply Measurable.aestronglyMeasurable
    unfold localPosteriorKernel
    fun_prop
  · intro n
    exact ae_of_all _ (fun z => mul_nonneg (hprior0 _) (Real.exp_pos _).le)
  · exact hb
  · exact hbound
  · exact he
  · apply ae_of_all
    intro z
    have ht : Tendsto (fun n => center n + z / rate n) atTop (𝓝 θ₀) := by
      simpa [div_eq_mul_inv] using hcenter.add (hrate.const_mul z)
    exact (hpriorCont.tendsto.comp ht).mul (Real.continuous_exp.tendsto _ |>.comp (hquadratic z))

/-- Translation and rescaling multiply the unnormalized evidence by the
absolute scale. This factor cancels in a posterior density. -/
theorem evidence_affine (q : ℝ → ℝ) (t r : ℝ) :
    evidence volume (fun z => q (t + z / r)) = |r| * evidence volume q := by
  unfold evidence
  change (∫ z : ℝ, (fun x => q (t + x)) (z / r)) = _
  rw [Measure.integral_comp_div (fun x => q (t + x)) r,
    integral_add_left_eq_self]
  rfl

/-- The exact distribution of the centered, rescaled posterior. The Jacobian
is proved by change of variables and is not a modeling assumption. -/
theorem bayesUpdate_map_affine {q : ℝ → ℝ} (hq : Integrable q volume)
    (hq0 : ∀ θ, 0 ≤ q θ) (he : 0 < evidence volume q)
    (t r : ℝ) (hr : r ≠ 0) :
    (bayesUpdate volume q).map (fun θ => r * (θ - t)) =
      bayesUpdate volume (fun z => q (t + z / r)) := by
  let e : ℝ ≃ᵐ ℝ :=
    { toFun := fun z => t + z / r
      invFun := fun θ => r * (θ - t)
      left_inv := by intro z; field_simp; ring
      right_inv := by intro θ; field_simp; ring
      measurable_toFun := by change Measurable (fun z : ℝ => t + z / r); fun_prop
      measurable_invFun := by change Measurable (fun θ : ℝ => r * (θ - t)); fun_prop }
  have he' : ∀ z, HasDerivAt e ((fun _ => r⁻¹) z) z := by
    intro z
    simpa [e, one_div] using ((hasDerivAt_id z).div_const r).const_add t
  have hi : Integrable (fun z => q (t + z / r)) volume :=
    (hq.comp_add_left t).comp_div hr
  have hem : 0 < evidence volume (fun z => q (t + z / r)) := by
    rw [evidence_affine]
    exact mul_pos (abs_pos.mpr hr) he
  change (bayesUpdate volume q).map e.symm = _
  ext A hA
  rw [bayesUpdate, e.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul'
    hA he' (ae_of_all _ (fun θ => div_nonneg (hq0 θ) he.le)) (hq.div_const _)]
  rw [bayesUpdate, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _).integrableOn
      (ae_of_all _ (fun z => div_nonneg (hq0 _) hem.le))]
  congr 1
  apply setIntegral_congr_fun hA
  intro z _
  change |r⁻¹| * (q (t + z / r) / evidence volume q) =
    q (t + z / r) / evidence volume (fun z => q (t + z / r))
  rw [evidence_affine, abs_inv]
  field_simp

/-- The local likelihood kernel is exactly the original posterior in local
coordinates, even before taking any limit. -/
theorem localPosteriorKernel_eq_map
    (logL : ℕ → ℝ → ℝ) (prior : ℝ → ℝ) (center rate : ℕ → ℝ)
    (hprior0 : ∀ θ, 0 ≤ prior θ) (n : ℕ) (hr : rate n ≠ 0)
    (hi : Integrable (fun θ => prior θ * Real.exp (logL n θ)) volume)
    (he : 0 < evidence volume (fun θ => prior θ * Real.exp (logL n θ))) :
    bayesUpdate volume (localPosteriorKernel logL prior center rate n) =
      (bayesUpdate volume (fun θ => prior θ * Real.exp (logL n θ))).map
        (fun θ => rate n * (θ - center n)) := by
  rw [bayesUpdate_map_affine hi
    (fun θ => mul_nonneg (hprior0 θ) (Real.exp_pos _).le) he _ _ hr]
  have hk : localPosteriorKernel logL prior center rate n =
      fun z => Real.exp (-logL n (center n)) *
        (prior (center n + z / rate n) * Real.exp (logL n (center n + z / rate n))) := by
    funext z
    simp only [localPosteriorKernel, sub_eq_add_neg, Real.exp_add]
    ring
  rw [hk, bayesUpdate_scale _ _ (Real.exp_pos _).ne']

/-- Evidence of the local kernel, including the Jacobian and the removed
likelihood value. Both multipliers are strictly positive for nonzero scale. -/
theorem localPosteriorKernel_evidence
    (logL : ℕ → ℝ → ℝ) (prior : ℝ → ℝ) (center rate : ℕ → ℝ) (n : ℕ) :
    evidence volume (localPosteriorKernel logL prior center rate n) =
      Real.exp (-logL n (center n)) * |rate n| *
        evidence volume (fun θ => prior θ * Real.exp (logL n θ)) := by
  have hk : localPosteriorKernel logL prior center rate n =
      fun z => Real.exp (-logL n (center n)) *
        (prior (center n + z / rate n) * Real.exp (logL n (center n + z / rate n))) := by
    funext z
    simp only [localPosteriorKernel, sub_eq_add_neg, Real.exp_add]
    ring
  rw [hk]
  change (∫ z, Real.exp (-logL n (center n)) *
    (prior (center n + z / rate n) * Real.exp (logL n (center n + z / rate n)))) = _
  rw [integral_const_mul]
  change Real.exp (-logL n (center n)) * evidence volume
    (fun z => (fun θ => prior θ * Real.exp (logL n θ)) (center n + z / rate n)) = _
  rw [evidence_affine (fun θ => prior θ * Real.exp (logL n θ)) (center n) (rate n)]
  ring

/-- L12 T1 with explicit sufficient hypotheses. The conclusion concerns the
actual posterior of θ, pushed forward by θ ↦ rₙ(θ−tₙ), uniformly over all
measurable events. Local quadraticity and a global integrable envelope are
stronger, precise replacements for the source's unspecified regularity. -/
theorem centered_posterior_gaussian_limit
    (logL : ℕ → ℝ → ℝ) (prior : ℝ → ℝ) (center rate : ℕ → ℝ)
    (θ₀ : ℝ) (v : ℝ≥0) (hv : 0 < v)
    (hprior : Measurable prior) (hprior0 : ∀ θ, 0 ≤ prior θ)
    (hpriorCont : ContinuousAt prior θ₀) (hpriorPos : 0 < prior θ₀)
    (hlogL : ∀ n, Measurable (logL n))
    (hcenter : Tendsto center atTop (𝓝 θ₀))
    (hrate : Tendsto (fun n => (rate n)⁻¹) atTop (𝓝 0))
    (hr : ∀ n, rate n ≠ 0)
    (hquadratic : ∀ z, Tendsto
      (fun n => logL n (center n + z / rate n) - logL n (center n)) atTop
      (𝓝 (-z ^ 2 / (2 * v))))
    (bound : ℝ → ℝ) (hb : Integrable bound volume)
    (hbound : ∀ n, ∀ᵐ z ∂volume, ‖localPosteriorKernel logL prior center rate n z‖ ≤ bound z)
    (hi : ∀ n, Integrable (fun θ => prior θ * Real.exp (logL n θ)) volume)
    (he : ∀ n, 0 < evidence volume (fun θ => prior θ * Real.exp (logL n θ))) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (𝓝 0) ∧
      ∀ n A, MeasurableSet A →
        |((bayesUpdate volume (fun θ => prior θ * Real.exp (logL n θ))).map
          (fun θ => rate n * (θ - center n))).real A -
            (gaussianReal 0 v).real A| ≤ error n := by
  have helocal n : 0 < evidence volume (localPosteriorKernel logL prior center rate n) := by
    rw [localPosteriorKernel_evidence]
    exact mul_pos (mul_pos (Real.exp_pos _) (abs_pos.mpr (hr n))) (he n)
  obtain ⟨err, herr, hlim, hA⟩ := local_posterior_gaussian_approximation
    logL prior center rate θ₀ v hv hprior hprior0 hpriorCont hpriorPos hlogL
    hcenter hrate hquadratic bound hb hbound helocal
  refine ⟨err, herr, hlim, fun n A hAm => ?_⟩
  rw [← localPosteriorKernel_eq_map logL prior center rate hprior0 n (hr n) (hi n) (he n)]
  exact hA n A hAm

/-- Any fixed Gaussian-calibrated event becomes an asymptotic posterior
credible set in the original parameter coordinates. -/
theorem posterior_credible_limit_of_uniform_error
    (post : ℕ → Measure ℝ) (center rate error : ℕ → ℝ) (v : ℝ≥0)
    (herror : Tendsto error atTop (𝓝 0))
    (hbound : ∀ n A, MeasurableSet A →
      |((post n).map (fun θ => rate n * (θ - center n))).real A -
        (gaussianReal 0 v).real A| ≤ error n)
    (A : Set ℝ) (hA : MeasurableSet A) (level : ℝ)
    (hlevel : (gaussianReal 0 v).real A = level) :
    Tendsto (fun n => (post n).real {θ | rate n * (θ - center n) ∈ A})
      atTop (𝓝 level) := by
  have hh n : |(post n).real {θ | rate n * (θ - center n) ∈ A} - level| ≤ error n := by
    have h := hbound n A hA
    rw [hlevel, measureReal_def, Measure.map_apply (by fun_prop) hA] at h
    exact h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) (fun n => by simpa [Real.norm_eq_abs] using hh n) herror)

/-- A symmetric local-coordinate interval corresponds to the usual interval
center ± critical-value/scale when the scale is positive. -/
theorem local_symmetric_interval (t r c : ℝ) (hr : 0 < r) :
    {θ : ℝ | r * (θ - t) ∈ Icc (-c) c} = Icc (t - c / r) (t + c / r) := by
  ext θ
  simp only [mem_setOf_eq, mem_Icc]
  constructor <;> intro h
  · constructor
    · have := (div_le_iff₀ hr).mpr (show -c ≤ (θ - t) * r by nlinarith [h.1])
      rw [neg_div] at this
      linarith
    · have := (le_div_iff₀ hr).mpr (show (θ - t) * r ≤ c by nlinarith [h.2])
      linarith
  · constructor
    · have : -c / r ≤ θ - t := by rw [neg_div]; linarith [h.1]
      have := (div_le_iff₀ hr).mp this
      nlinarith
    · have : θ - t ≤ c / r := by linarith [h.2]
      have := (le_div_iff₀ hr).mp this
      nlinarith

/-- A sampling-mode version of the posterior theorem: the explicit local
quadraticity, consistency, and domination hypotheses hold on a set of sample
paths of full probability. The resulting uniform event approximation holds
almost surely in the sampling experiment. The envelope may depend on the path. -/
theorem centered_posterior_gaussian_limit_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (logL : Ω → ℕ → ℝ → ℝ) (prior : ℝ → ℝ) (center rate : Ω → ℕ → ℝ)
    (θ₀ : ℝ) (v : ℝ≥0) (hv : 0 < v)
    (hprior : Measurable prior) (hprior0 : ∀ θ, 0 ≤ prior θ)
    (hpriorCont : ContinuousAt prior θ₀) (hpriorPos : 0 < prior θ₀)
    (hregular : ∀ᵐ ω ∂P,
      (∀ n, Measurable (logL ω n)) ∧
      Tendsto (center ω) atTop (𝓝 θ₀) ∧
      Tendsto (fun n => (rate ω n)⁻¹) atTop (𝓝 0) ∧
      (∀ n, rate ω n ≠ 0) ∧
      (∀ z, Tendsto
        (fun n => logL ω n (center ω n + z / rate ω n) - logL ω n (center ω n)) atTop
        (𝓝 (-z ^ 2 / (2 * v)))) ∧
      (∀ n, Integrable (fun θ => prior θ * Real.exp (logL ω n θ)) volume) ∧
      (∀ n, 0 < evidence volume (fun θ => prior θ * Real.exp (logL ω n θ))) ∧
      ∃ bound : ℝ → ℝ, Integrable bound volume ∧
        ∀ n, ∀ᵐ z ∂volume,
          ‖localPosteriorKernel (logL ω) prior (center ω) (rate ω) n z‖ ≤ bound z) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ A : Set ℝ, MeasurableSet A →
        |((bayesUpdate volume (fun θ => prior θ * Real.exp (logL ω n θ))).map
          (fun θ => rate ω n * (θ - center ω n))).real A -
            (gaussianReal 0 v).real A| < ε := by
  filter_upwards [hregular] with ω hω
  obtain ⟨hl, hc, hr, hr0, hquad, hi, he, bound, hb, hbound⟩ := hω
  obtain ⟨err, _, hlim, hA⟩ := centered_posterior_gaussian_limit
    (logL ω) prior (center ω) (rate ω) θ₀ v hv hprior hprior0 hpriorCont hpriorPos
    hl hc hr hr0 hquad bound hb hbound hi he
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  exact fun A hAm => (hA n A hAm).trans_lt hn

end LectureNotes
