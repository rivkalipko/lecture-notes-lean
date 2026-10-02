import LectureNotes.PosteriorAsymptotics
import LectureNotes.NormalHighestDensity
import LectureNotes.NormalPosteriorLimit

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

/-- A uniform Gaussian approximation transfers to events that change with
the sample size. The limiting Gaussian probability must itself converge. -/
theorem posterior_moving_event_limit_of_uniform_error
    (post : ℕ → Measure ℝ) (center rate error : ℕ → ℝ) (v : ℝ≥0)
    (herror : Tendsto error atTop (𝓝 0))
    (hbound : ∀ n A, MeasurableSet A →
      |((post n).map (fun θ => rate n * (θ - center n))).real A -
        (gaussianReal 0 v).real A| ≤ error n)
    (A : ℕ → Set ℝ) (hA : ∀ n, MeasurableSet (A n)) (level : ℝ)
    (hlevel : Tendsto (fun n => (gaussianReal 0 v).real (A n)) atTop (𝓝 level)) :
    Tendsto (fun n => (post n).real {θ | rate n * (θ - center n) ∈ A n})
      atTop (𝓝 level) := by
  have hh n : |(post n).real {θ | rate n * (θ - center n) ∈ A n} - level| ≤
      error n + |(gaussianReal 0 v).real (A n) - level| := by
    have he := hbound n (A n) (hA n)
    rw [map_measureReal_apply (by fun_prop) (hA n)] at he
    have ht := abs_add_le
      ((post n).real {θ | rate n * (θ - center n) ∈ A n} - (gaussianReal 0 v).real (A n))
      ((gaussianReal 0 v).real (A n) - level)
    rw [sub_add_sub_cancel] at ht
    exact ht.trans (add_le_add he le_rfl)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun n => error n + |(gaussianReal 0 v).real (A n) - level|)
      atTop (𝓝 0) := by simpa using herror.add ((hlevel.sub_const level).abs)
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => by simpa only [Real.norm_eq_abs] using hh n) hlim

/-- The limiting Gaussian measure calibrates the variable-width local event
when the positive information estimates converge to the true information. -/
theorem gaussian_estimated_information_event_limit (J : ℕ → ℝ) {I : ℝ≥0}
    (hI : 0 < I) (hJ : Tendsto J atTop (𝓝 (I : ℝ)))
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun n => (gaussianReal 0 I⁻¹).real
      {z | z / Real.sqrt ((J n)⁻¹) ∈ Icc
        (distributionQuantile (gaussianReal 0 1) a)
        (distributionQuantile (gaussianReal 0 1) b)}) atTop (𝓝 (b - a)) := by
  have hIR : (0 : ℝ) < I := by exact_mod_cast hI
  have hscale : Tendsto (fun n => Real.sqrt ((J n)⁻¹))
      atTop (𝓝 (Real.sqrt ((I : ℝ)⁻¹))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp (hJ.inv₀ hIR.ne')
  have hs : Real.sqrt ((I : ℝ)⁻¹) ≠ 0 := (Real.sqrt_pos.mpr (inv_pos.mpr hIR)).ne'
  have hprob : ConvergesInProbability (gaussianReal 0 I⁻¹)
      (fun n z => z / Real.sqrt ((J n)⁻¹)) (fun z => z / Real.sqrt ((I : ℝ)⁻¹)) := by
    apply almost_sure_implies_probability (fun n => (measurable_id.div_const _).aemeasurable)
    exact ae_of_all _ (fun z => tendsto_const_nhds.div hscale hs)
  have hdist := probability_implies_distribution
    (fun n => (measurable_id.div_const (Real.sqrt ((J n)⁻¹))).aemeasurable) hprob
  have hz := normal_standardize (inv_pos.mpr hI)
    (show HasLaw id (gaussianReal 0 I⁻¹) (gaussianReal 0 I⁻¹) from HasLaw.id)
  simp only [id_eq, sub_zero, NNReal.coe_inv] at hz
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  exact asymptotic_quantile_coverage hdist hz ha hb hab

/-- The estimated-information interval has asymptotic posterior content
`1−α` under an explicit uniform local Gaussian approximation. Index `n`
represents sample size `n+1`; the interval width uses the estimated information.
This is a conditional transfer result, not a general posterior limit theorem. -/
theorem posterior_estimated_information_interval_content
    (post : ℕ → Measure ℝ) (center J error : ℕ → ℝ) {I : ℝ≥0} (hI : 0 < I)
    (hJpos : ∀ n, 0 < J n) (hJ : Tendsto J atTop (𝓝 (I : ℝ)))
    (herror : Tendsto error atTop (𝓝 0))
    (hbound : ∀ n A, MeasurableSet A →
      |((post n).map (fun θ => Real.sqrt ((n : ℝ) + 1) * (θ - center n))).real A -
        (gaussianReal 0 I⁻¹).real A| ≤ error n)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => (post n).real (Icc
      (center n - distributionQuantile (gaussianReal 0 1) (1 - α / 2) *
        Real.sqrt (1 / (((n : ℝ) + 1) * J n)))
      (center n + distributionQuantile (gaussianReal 0 1) (1 - α / 2) *
        Real.sqrt (1 / (((n : ℝ) + 1) * J n))))) atTop (𝓝 (1 - α)) := by
  have ha : α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hb : 1 - α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  let z := distributionQuantile (gaussianReal 0 1) (1 - α / 2)
  have hsym : distributionQuantile (gaussianReal 0 1) (α / 2) = -z := by
    have h := standardNormal_quantile_symmetry ha
    dsimp only [z]
    linarith
  let A (n : ℕ) := {x : ℝ | x / Real.sqrt ((J n)⁻¹) ∈ Icc (-z) z}
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_Icc.preimage (by fun_prop)
  have hG : Tendsto (fun n => (gaussianReal 0 I⁻¹).real (A n)) atTop (𝓝 (1 - α)) := by
    have h := gaussian_estimated_information_event_limit J hI hJ ha hb (by linarith [hα.2])
    rw [hsym] at h
    simpa only [A, z, show 1 - α / 2 - α / 2 = 1 - α by ring] using h
  have ht := posterior_moving_event_limit_of_uniform_error post center
    (fun n => Real.sqrt ((n : ℝ) + 1)) error I⁻¹ herror hbound A hA (1 - α) hG
  convert ht using 1
  funext n
  congr 1
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hs : 0 < Real.sqrt ((J n)⁻¹) := Real.sqrt_pos.mpr (inv_pos.mpr (hJpos n))
  have he : Real.sqrt (1 / (((n : ℝ) + 1) * J n)) =
      Real.sqrt ((J n)⁻¹) / Real.sqrt ((n : ℝ) + 1) := by
    rw [← Real.sqrt_div (inv_nonneg.mpr (hJpos n).le)]
    congr 1
    simp only [mul_inv_rev, div_eq_mul_inv, one_mul]
  have hid : ∀ θ, Real.sqrt ((n : ℝ) + 1) * (θ - center n) / Real.sqrt ((J n)⁻¹) =
      (Real.sqrt ((n : ℝ) + 1) / Real.sqrt ((J n)⁻¹)) * (θ - center n) := by intro θ; ring
  change Icc (center n - z * _) (center n + z * _) =
    {θ | Real.sqrt ((n : ℝ) + 1) * (θ - center n) / Real.sqrt ((J n)⁻¹) ∈ Icc (-z) z}
  simp_rw [hid]
  rw [local_symmetric_interval _ _ _ (div_pos (Real.sqrt_pos.mpr hn) hs), he]
  congr 1 <;> rw [div_div_eq_mul_div] <;> ring

/-- If the explicit approximation and information convergence hold almost
surely along sampling paths, the posterior contents converge almost surely. -/
theorem posterior_estimated_information_interval_content_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (post : Ω → ℕ → Measure ℝ) (center J error : Ω → ℕ → ℝ)
    {I : ℝ≥0} (hI : 0 < I)
    (hregular : ∀ᵐ ω ∂P, (∀ n, 0 < J ω n) ∧
      Tendsto (J ω) atTop (𝓝 (I : ℝ)) ∧ Tendsto (error ω) atTop (𝓝 0) ∧
      ∀ n A, MeasurableSet A →
        |((post ω n).map (fun θ => Real.sqrt ((n : ℝ) + 1) * (θ - center ω n))).real A -
          (gaussianReal 0 I⁻¹).real A| ≤ error ω n)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, Tendsto (fun n => (post ω n).real (Icc
      (center ω n - distributionQuantile (gaussianReal 0 1) (1 - α / 2) *
        Real.sqrt (1 / (((n : ℝ) + 1) * J ω n)))
      (center ω n + distributionQuantile (gaussianReal 0 1) (1 - α / 2) *
        Real.sqrt (1 / (((n : ℝ) + 1) * J ω n))))) atTop (𝓝 (1 - α)) := by
  filter_upwards [hregular] with ω hω
  exact posterior_estimated_information_interval_content (post ω) (center ω) (J ω) (error ω)
    hI hω.1 hω.2.1 hω.2.2.1 hω.2.2.2 hα

/-- In the normal-mean model, a bounded continuous integrable prior positive
at the true parameter supplies the uniform posterior approximation. Thus the
estimated-information credible interval follows from prior conditions and
consistency; a posterior convergence claim is not assumed. -/
theorem normal_mean_estimated_information_posterior_content
    (prior : ℝ → ℝ) (center J : ℕ → ℝ) (θ₀ : ℝ) {I : ℝ≥0} (hI : 0 < I)
    (hprior : Continuous prior) (hprior0 : ∀ θ, 0 ≤ prior θ)
    (hpriorInt : Integrable prior volume) (hpriorPos : 0 < prior θ₀)
    (K : ℝ) (hK : ∀ θ, prior θ ≤ K)
    (hcenter : Tendsto center atTop (𝓝 θ₀))
    (hJpos : ∀ n, 0 < J n) (hJ : Tendsto J atTop (𝓝 (I : ℝ)))
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => (bayesUpdate volume (fun θ => prior θ *
      Real.exp (normalMeanLogKernel center (fun n => Real.sqrt ((n : ℝ) + 1)) I⁻¹ n θ))).real
        (Icc
          (center n - distributionQuantile (gaussianReal 0 1) (1 - α / 2) *
            Real.sqrt (1 / (((n : ℝ) + 1) * J n)))
          (center n + distributionQuantile (gaussianReal 0 1) (1 - α / 2) *
            Real.sqrt (1 / (((n : ℝ) + 1) * J n))))) atTop (𝓝 (1 - α)) := by
  have hr : Tendsto (fun n : ℕ => (Real.sqrt ((n : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    apply Real.tendsto_sqrt_atTop.comp
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  obtain ⟨error, _, he, hbound⟩ := normal_mean_posterior_gaussian_limit prior center
    (fun n => Real.sqrt ((n : ℝ) + 1)) θ₀ I⁻¹ (inv_pos.mpr hI)
    hprior hprior0 hpriorInt hpriorPos K hK hcenter hr
    (fun n => (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < (n : ℝ) + 1)).ne')
  exact posterior_estimated_information_interval_content _ center J error hI hJpos hJ he hbound hα

end LectureNotes
