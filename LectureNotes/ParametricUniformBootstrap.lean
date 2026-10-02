import LectureNotes.UniformEndpoint
import LectureNotes.BootstrapMaximum

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped Topology

/-- Parametric resampling from the fitted uniform endpoint model. Positivity
of the observed maximum is proved almost surely in the sampling theorem. -/
def uniformParametricBootstrapLaw {n : ℕ} (x : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => uniformEndpointLaw (sampleMaximum x))

theorem uniformParametricBootstrapLaw_probability {n : ℕ} (x : Fin n → ℝ)
    (hx : 0 < sampleMaximum x) : IsProbabilityMeasure (uniformParametricBootstrapLaw x) := by
  have := uniformEndpointLaw_probability hx
  unfold uniformParametricBootstrapLaw
  infer_instance

theorem uniform_parametricBootstrap_eval_law {n : ℕ} (x : Fin n → ℝ)
    (hx : 0 < sampleMaximum x) (i : Fin n) :
    HasLaw (fun b : Fin n → ℝ => b i) (uniformEndpointLaw (sampleMaximum x))
      (uniformParametricBootstrapLaw x) := by
  have := uniformEndpointLaw_probability hx
  exact ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩

/-- Refitting the endpoint to the parametric sample gives the exact same
Beta law for the ratio of estimated to fitted endpoint. -/
theorem uniform_parametricBootstrap_maximum_ratio_law (n : ℕ) (x : Fin (n + 1) → ℝ)
    (hx : 0 < sampleMaximum x) :
    HasLaw (fun b => sampleMaximum b / sampleMaximum x)
      (betaMeasure ((n : ℝ) + 1) 1) (uniformParametricBootstrapLaw x) := by
  have := uniformEndpointLaw_probability hx
  have := uniformParametricBootstrapLaw_probability x hx
  exact iid_uniform_standardized_maximum_law n hx (fun i => measurable_pi_apply i)
    (uniform_parametricBootstrap_eval_law x hx)
    (iIndepFun_pi (fun _ : Fin (n + 1) => measurable_id.aemeasurable))

/-- The common, parameter-free finite-sample law of the normalized endpoint gap. -/
def uniformMaximumGapReference (n : ℕ) : Measure ℝ :=
  (betaMeasure ((n : ℝ) + 1) 1).map (fun y : ℝ => ((n : ℝ) + 1) * (1 - y))

instance uniformMaximumGapReference_probability (n : ℕ) :
    IsProbabilityMeasure (uniformMaximumGapReference n) := by
  have : IsProbabilityMeasure (betaMeasure ((n : ℝ) + 1) 1) :=
    isProbabilityMeasureBeta (by positivity) zero_lt_one
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem uniform_parametricBootstrap_normalized_gap_law (n : ℕ) (x : Fin (n + 1) → ℝ)
    (hx : 0 < sampleMaximum x) :
    HasLaw (fun b => ((n : ℝ) + 1) * (sampleMaximum x - sampleMaximum b) / sampleMaximum x)
      (uniformMaximumGapReference n) (uniformParametricBootstrapLaw x) := by
  have hg : HasLaw (fun y : ℝ => ((n : ℝ) + 1) * (1 - y))
      (uniformMaximumGapReference n) (betaMeasure ((n : ℝ) + 1) 1) := ⟨by fun_prop, rfl⟩
  have hh := hg.comp (uniform_parametricBootstrap_maximum_ratio_law n x hx)
  convert! hh using 1
  funext b
  dsimp only [Function.comp_apply]
  field_simp

/-- The actual original normalized endpoint gap has that same exact law. -/
theorem iid_uniform_normalized_gap_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (n : ℕ)
    {X : Fin (n + 1) → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) (hind : iIndepFun X P) :
    HasLaw (fun ω => ((n : ℝ) + 1) * (θ - sampleMaximum (fun i => X i ω)) / θ)
      (uniformMaximumGapReference n) P := by
  have hg : HasLaw (fun y : ℝ => ((n : ℝ) + 1) * (1 - y))
      (uniformMaximumGapReference n) (betaMeasure ((n : ℝ) + 1) 1) := ⟨by fun_prop, rfl⟩
  have hh := hg.comp (iid_uniform_standardized_maximum_law n hθ hXm hX hind)
  convert! hh using 1
  funext ω
  dsimp only [Function.comp_apply]
  field_simp

/-- A precise qualification to L7's blanket failure remark: correctly
specified parametric uniform resampling reproduces the normalized endpoint
pivot exactly, at every sample size. This differs from empirical resampling. -/
theorem iid_uniform_parametricBootstrap_exact_pivot {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (n : ℕ)
    {X : Fin (n + 1) → Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (uniformEndpointLaw θ) P) (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P,
      (uniformParametricBootstrapLaw (fun i => X i ω)).map
        (fun b => ((n : ℝ) + 1) *
          (sampleMaximum (fun i => X i ω) - sampleMaximum b) / sampleMaximum (fun i => X i ω)) =
      P.map (fun w => ((n : ℝ) + 1) * (θ - sampleMaximum (fun i => X i w)) / θ) := by
  filter_upwards [uniform_maximum_pos_le_ae (Nat.succ_pos n) hX] with ω hω
  exact (uniform_parametricBootstrap_normalized_gap_law n _ hω.1).map_eq.trans
    (iid_uniform_normalized_gap_law n hθ hXm hX hind).map_eq.symm

/-- The fitted experiment refits an actual likelihood maximizer almost surely,
not merely a statistic bearing the MLE name. -/
theorem uniform_parametricBootstrap_refit_maximizes (n : ℕ) (x : Fin (n + 1) → ℝ)
    (hx : 0 < sampleMaximum x) :
    ∀ᵐ b ∂uniformParametricBootstrapLaw x, 0 < sampleMaximum b ∧
      ∀ t : ℝ, 0 < t → (∏ i, uniformEndpointDensity t (b i)) ≤
        ∏ i, uniformEndpointDensity (sampleMaximum b) (b i) :=
  uniformEndpoint_maximizes_density_ae (Nat.succ_pos n) (uniform_parametricBootstrap_eval_law x hx)

end LectureNotes
