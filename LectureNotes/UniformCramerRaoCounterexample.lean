import LectureNotes.UniformEndpoint
import LectureNotes.BootstrapMaximum
import LectureNotes.Information

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- The derivative of the actual uniform endpoint log density in its parameter. -/
def uniformEndpointScore (θ x : ℝ) : ℝ :=
  deriv (fun t => Real.log (uniformEndpointDensity t x)) θ

def uniformEndpointLogSecond (θ x : ℝ) : ℝ :=
  deriv (fun t => uniformEndpointScore t x) θ

/-- Away from the moving support boundary, the actual log density has the
constant-in-the-observation score printed in L6 Example 9. -/
theorem uniformEndpoint_log_hasDerivAt {θ x : ℝ} (hθ : 0 < θ)
    (hx : 0 ≤ x) (hxt : x < θ) :
    HasDerivAt (fun t => Real.log (uniformEndpointDensity t x)) (-1 / θ) θ := by
  have hd : HasDerivAt (fun t : ℝ => -Real.log t) (-1 / θ) θ := by
    simpa only [neg_div, one_div] using! (Real.hasDerivAt_log hθ.ne').neg
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hxt] with t ht
  simp [uniformEndpointDensity, show x ∈ Icc 0 t from ⟨hx, ht.le⟩]

theorem uniformEndpoint_score_eq {θ x : ℝ} (hθ : 0 < θ)
    (hx : 0 ≤ x) (hxt : x < θ) : uniformEndpointScore θ x = -1 / θ :=
  (uniformEndpoint_log_hasDerivAt hθ hx hxt).deriv

theorem uniformEndpoint_score_hasDerivAt {θ x : ℝ} (hθ : 0 < θ)
    (hx : 0 ≤ x) (hxt : x < θ) :
    HasDerivAt (fun t => uniformEndpointScore t x) (1 / θ ^ 2) θ := by
  have hd : HasDerivAt (fun t : ℝ => -1 / t) (1 / θ ^ 2) θ := by
    simpa only [neg_div, one_div, neg_neg] using! (hasDerivAt_inv hθ.ne').neg
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hxt] with t ht
  exact uniformEndpoint_score_eq (lt_of_le_of_lt hx ht) hx ht

theorem uniformEndpoint_score_ae {θ : ℝ} (hθ : 0 < θ) :
    uniformEndpointScore θ =ᵐ[uniformEndpointLaw θ] (fun _ => -1 / θ) := by
  filter_upwards [uniformEndpoint_ae_support θ, uniformEndpoint_ae_lt hθ] with x hx hxt
  exact uniformEndpoint_score_eq hθ hx.1.le hxt

theorem uniformEndpoint_log_second_ae {θ : ℝ} (hθ : 0 < θ) :
    uniformEndpointLogSecond θ =ᵐ[uniformEndpointLaw θ] (fun _ => 1 / θ ^ 2) := by
  filter_upwards [uniformEndpoint_ae_support θ, uniformEndpoint_ae_lt hθ] with x hx hxt
  exact (uniformEndpoint_score_hasDerivAt hθ hx.1.le hxt).deriv

theorem uniformEndpoint_score_memLp_two {θ : ℝ} (hθ : 0 < θ) :
    MemLp (uniformEndpointScore θ) 2 (uniformEndpointLaw θ) := by
  have := uniformEndpointLaw_probability hθ
  have hc : MemLp (fun _ : ℝ => -1 / θ) 2 (uniformEndpointLaw θ) := memLp_const _
  exact (memLp_congr_ae (uniformEndpoint_score_ae hθ)).mpr hc

theorem uniformEndpoint_log_second_integrable {θ : ℝ} (hθ : 0 < θ) :
    Integrable (uniformEndpointLogSecond θ) (uniformEndpointLaw θ) := by
  have := uniformEndpointLaw_probability hθ
  exact (integrable_const (1 / θ ^ 2)).congr (uniformEndpoint_log_second_ae hθ).symm

/-- The first regular information identity fails: the genuine score has
nonzero expectation under the actual sampling measure. -/
theorem uniformEndpoint_expected_score {θ : ℝ} (hθ : 0 < θ) :
    (∫ x, uniformEndpointScore θ x ∂uniformEndpointLaw θ) = -1 / θ ∧ -1 / θ ≠ 0 := by
  have := uniformEndpointLaw_probability hθ
  constructor
  · rw [integral_congr_ae (uniformEndpoint_score_ae hθ)]
    simp
  · exact div_ne_zero (by norm_num) hθ.ne'

theorem uniformEndpoint_fisherInformation {θ : ℝ} (hθ : 0 < θ) :
    FisherInformation (uniformEndpointLaw θ) (uniformEndpointScore θ) = 1 / θ ^ 2 := by
  have := uniformEndpointLaw_probability hθ
  unfold FisherInformation
  rw [integral_congr_ae ((uniformEndpoint_score_ae hθ).mono (fun x hx => congrArg (· ^ 2) hx))]
  simp [div_pow]

theorem uniformEndpoint_expected_log_second {θ : ℝ} (hθ : 0 < θ) :
    (∫ x, uniformEndpointLogSecond θ x ∂uniformEndpointLaw θ) = 1 / θ ^ 2 := by
  have := uniformEndpointLaw_probability hθ
  rw [integral_congr_ae (uniformEndpoint_log_second_ae hθ)]
  simp

/-- Squared score expectation and negative expected second log derivative
have opposite signs, so the second regular information identity fails too. -/
theorem uniformEndpoint_second_information_failure {θ : ℝ} (hθ : 0 < θ) :
    FisherInformation (uniformEndpointLaw θ) (uniformEndpointScore θ) ≠
      -(∫ x, uniformEndpointLogSecond θ x ∂uniformEndpointLaw θ) := by
  rw [uniformEndpoint_fisherInformation hθ, uniformEndpoint_expected_log_second hθ]
  have hp : 0 < 1 / θ ^ 2 := by positivity
  linarith

/-- Bias-corrected maximum of n+1 observations, with the source's factor
(N+1)/N and N=n+1. -/
def uniformCorrectedMaximum {n : ℕ} (x : Fin (n + 1) → ℝ) : ℝ :=
  ((n : ℝ) + 2) / ((n : ℝ) + 1) * sampleMaximum x

/-- Score of the actual product density, rather than a sum declared to have
zero mean. -/
def uniformEndpointSampleScore {n : ℕ} (θ : ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun t => Real.log (∏ i, uniformEndpointDensity t (x i))) θ

theorem uniformEndpoint_sample_log_hasDerivAt (n : ℕ) {θ : ℝ} (hθ : 0 < θ)
    (x : Fin (n + 1) → ℝ) (hx : ∀ i, 0 ≤ x i) (hmax : sampleMaximum x < θ) :
    HasDerivAt (fun t => Real.log (∏ i, uniformEndpointDensity t (x i)))
      (-((n : ℝ) + 1) / θ) θ := by
  have hd : HasDerivAt (fun t => -((n : ℝ) + 1) * Real.log t)
      (-((n : ℝ) + 1) / θ) θ := by
    simpa only [div_eq_mul_inv] using! (Real.hasDerivAt_log hθ.ne').const_mul (-((n : ℝ) + 1))
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hmax] with t ht
  have hi i : x i ∈ Icc 0 t := ⟨hx i, (le_sampleMaximum x i).trans ht.le⟩
  simp only [uniformEndpointDensity, if_pos (hi _), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Real.log_pow, one_div, Real.log_inv, Nat.cast_add, Nat.cast_one]
  ring

theorem uniformEndpoint_sample_score_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (n : ℕ) {X : Fin (n + 1) → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) :
    (fun ω => uniformEndpointSampleScore θ (fun i => X i ω)) =ᵐ[P]
      (fun _ => -((n : ℝ) + 1) / θ) := by
  have hs : ∀ᵐ ω ∂P, ∀ i, X i ω ∈ Ioc 0 θ := ae_all_iff.mpr (fun i =>
    ((hX i).ae_iff (show Measurable (fun x : ℝ => x ∈ Ioc 0 θ) by measurability)).mpr
      (uniformEndpoint_ae_support θ))
  filter_upwards [hs, uniform_maximum_lt_endpoint_ae (Nat.succ_pos n) hθ hX] with ω hω hmax
  exact (uniformEndpoint_sample_log_hasDerivAt n hθ _ (fun i => (hω i).1.le) hmax).deriv

/-- The actual sample squared-score expectation is N²/θ². The familiar
additive expression N/θ² fails because these scores are not centered. -/
theorem uniformEndpoint_sample_fisherInformation {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (n : ℕ)
    {X : Fin (n + 1) → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) :
    FisherInformation P (fun ω => uniformEndpointSampleScore θ (fun i => X i ω)) =
      ((n : ℝ) + 1) ^ 2 / θ ^ 2 := by
  unfold FisherInformation
  rw [integral_congr_ae ((uniformEndpoint_sample_score_ae n hθ hX).mono
    (fun ω hω => congrArg (· ^ 2) hω))]
  simp [div_pow]
  ring

theorem uniformEndpoint_sample_information_not_additive {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin (n + 1) → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) :
    FisherInformation P (fun ω => uniformEndpointSampleScore θ (fun i => X i ω)) ≠
      ((n : ℝ) + 1) * FisherInformation (uniformEndpointLaw θ) (uniformEndpointScore θ) := by
  rw [uniformEndpoint_sample_fisherInformation n hθ hX, uniformEndpoint_fisherInformation hθ]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  intro he
  have ht : θ ^ 2 ≠ 0 := pow_ne_zero _ hθ.ne'
  field_simp at he
  nlinarith

section IID
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (n : ℕ) {X : Fin (n + 1) → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
  (hXm : ∀ i, Measurable (X i))
  (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) (hind : iIndepFun X P)

include hθ hXm hX hind

theorem uniformCorrectedMaximum_unbiased :
    Unbiased P (fun ω => uniformCorrectedMaximum (fun i => X i ω)) θ := by
  constructor
  · exact ((iid_uniform_maximum_memLp n hθ hXm hX hind).const_mul _).integrable (by norm_num)
  · rw [show (fun ω => uniformCorrectedMaximum (fun i => X i ω)) =
        (fun ω => (((n : ℝ) + 2) / ((n : ℝ) + 1)) * sampleMaximum (fun i => X i ω)) from rfl,
      integral_const_mul, iid_uniform_maximum_mean n hθ hXm hX hind]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn' : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp

theorem uniformCorrectedMaximum_variance :
    Var[fun ω => uniformCorrectedMaximum (fun i => X i ω); P] =
      θ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 3)) := by
  unfold uniformCorrectedMaximum
  rw [variance_const_mul, iid_uniform_maximum_variance n hθ hXm hX hind]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn' : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp

theorem uniformCorrectedMaximum_below_formal_bound :
    Var[fun ω => uniformCorrectedMaximum (fun i => X i ω); P] < θ ^ 2 / ((n : ℝ) + 1) := by
  rw [uniformCorrectedMaximum_variance n hθ hXm hX hind]
  apply div_lt_div_of_pos_left (sq_pos_of_pos hθ) (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- The explicit unbiased estimator violates the expression obtained by
applying the regular Cramer–Rao formula to this moving-support model. This
is a counterexample to dropping regularity, not to the regular theorem. -/
theorem uniformEndpoint_cramerRao_counterexample :
    Unbiased P (fun ω => uniformCorrectedMaximum (fun i => X i ω)) θ ∧
      Var[fun ω => uniformCorrectedMaximum (fun i => X i ω); P] <
        1 / (((n : ℝ) + 1) * FisherInformation (uniformEndpointLaw θ) (uniformEndpointScore θ)) := by
  refine ⟨uniformCorrectedMaximum_unbiased n hθ hXm hX hind, ?_⟩
  rw [uniformEndpoint_fisherInformation hθ]
  have he : 1 / (((n : ℝ) + 1) * (1 / θ ^ 2)) = θ ^ 2 / ((n : ℝ) + 1) := by
    field_simp
  rw [he]
  exact uniformCorrectedMaximum_below_formal_bound n hθ hXm hX hind

end IID
end LectureNotes
