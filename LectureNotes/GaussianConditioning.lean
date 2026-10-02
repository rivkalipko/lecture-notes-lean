import LectureNotes.Correlation

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- A measurable family of pushforwards of one fixed probability law. -/
def familyMapKernel {E F G : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSpace G] (μ : Measure F) [SFinite μ]
    (f : E × F → G) (hf : Measurable f) : Kernel E G where
  toFun x := μ.map (fun y => f (x, y))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have heq : (fun x => μ.map (fun y => f (x, y)) s) =
        fun x => μ (Prod.mk x ⁻¹' (f ⁻¹' s)) := by
      funext x
      have hfx : Measurable (fun y => f (x, y)) := hf.comp measurable_prodMk_left
      rw [Measure.map_apply hfx hs]
      rfl
    rw [heq]
    exact measurable_measure_prodMk_left (hs.preimage hf)

instance familyMapKernel_isMarkov {E F G : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSpace G] (μ : Measure F) [IsProbabilityMeasure μ]
    (f : E × F → G) (hf : Measurable f) : IsMarkovKernel (familyMapKernel μ f hf) where
  isProbabilityMeasure x := Measure.isProbabilityMeasure_map (hf.comp measurable_prodMk_left).aemeasurable

/-- Independent noise gives a conditional law even when the transformation
also depends on the variable being conditioned on. -/
theorem condDistrib_independent_noise {Ω E F G : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G]
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → E} {R : Ω → F}
    (hY : Measurable Y) (hR : Measurable R) (hind : IndepFun Y R P)
    (f : E × F → G) (hf : Measurable f) :
    condDistrib (fun ω => f (Y ω, R ω)) Y P =ᵐ[P.map Y]
      familyMapKernel (P.map R) f hf := by
  haveI : IsProbabilityMeasure (P.map R) := Measure.isProbabilityMeasure_map hR.aemeasurable
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hY
    (hf.comp (hY.prodMk hR))
  have hj := hind.map_prod_eq_prod_map_map hY.aemeasurable hR.aemeasurable
  have hm : Measurable (fun z : E × F => (z.1, f z)) := measurable_fst.prodMk hf
  have hmap : P.map (fun ω => (Y ω, f (Y ω, R ω))) =
      ((P.map Y).prod (P.map R)).map (fun z => (z.1, f z)) := by
    rw [← hj, Measure.map_map hm (hY.prodMk hR)]
    rfl
  change P.map (fun ω => (Y ω, f (Y ω, R ω))) = _
  rw [hmap]
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hs.preimage hm),
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro y
  change (P.map R) (Prod.mk y ⁻¹' ((fun z : E × F => (z.1, f z)) ⁻¹' s)) =
    ((P.map R).map (fun r => f (y, r))) (Prod.mk y ⁻¹' s)
  have hfy : Measurable (fun r => f (y, r)) := hf.comp measurable_prodMk_left
  rw [Measure.map_apply hfy (hs.preimage measurable_prodMk_left)]
  rfl

/-- The regression residual of a jointly Gaussian pair is independent of the
regressor when that regressor has positive variance. -/
theorem gaussian_regression_residual_independent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) (hv : 0 < Var[Y; P]) :
    IndepFun (fun ω => X ω - (cov[X, Y; P] / Var[Y; P]) * Y ω) Y P := by
  let c := cov[X, Y; P] / Var[Y; P]
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ) - c • (ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hg : HasGaussianLaw (fun ω => (X ω - c * Y ω, Y ω)) P := by
    exact hXY.map_fun L
  apply hg.indepFun_of_covariance_eq_zero
  rw [covariance_fun_sub_left hXY.fst.memLp_two (hXY.snd.memLp_two.const_mul c)
      hXY.snd.memLp_two, covariance_const_mul_left, covariance_self hXY.snd.aemeasurable]
  dsimp [c]
  rw [div_mul_cancel₀ _ hv.ne', sub_self]

/-- The Gaussian residual has the Schur-complement variance. -/
theorem gaussian_regression_residual_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) (hv : 0 < Var[Y; P]) :
    P.map (fun ω => X ω - (cov[X, Y; P] / Var[Y; P]) * Y ω) =
      gaussianReal ((∫ ω, X ω ∂P) - (cov[X, Y; P] / Var[Y; P]) * (∫ ω, Y ω ∂P))
        (Var[X; P] - cov[X, Y; P] ^ 2 / Var[Y; P]).toNNReal := by
  let c := cov[X, Y; P] / Var[Y; P]
  have hg : HasGaussianLaw (fun ω => X ω - c * Y ω) P :=
    hXY.map_fun ((ContinuousLinearMap.fst ℝ ℝ ℝ) - c • (ContinuousLinearMap.snd ℝ ℝ ℝ))
  rw [hg.map_eq_gaussianReal]
  congr 1
  · rw [integral_sub hXY.fst.integrable (hXY.snd.integrable.const_mul c), integral_const_mul]
  · congr 1
    rw [variance_fun_sub hXY.fst.memLp_two (hXY.snd.memLp_two.const_mul c),
      variance_const_mul, covariance_const_mul_right]
    dsimp [c]
    field_simp
    <;> ring

/-- L1: the conditional law of one coordinate of a bivariate Gaussian. The
identity is for almost every conditioning value, as required for conditional laws. -/
theorem gaussian_conditional_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) (hv : 0 < Var[Y; P]) :
    condDistrib X Y P =ᵐ[P.map Y] fun y =>
      gaussianReal ((∫ ω, X ω ∂P) + cov[X, Y; P] / Var[Y; P] *
        (y - ∫ ω, Y ω ∂P)) (Var[X; P] - cov[X, Y; P] ^ 2 / Var[Y; P]).toNNReal := by
  let c := cov[X, Y; P] / Var[Y; P]
  let R : Ω → ℝ := fun ω => X ω - c * Y ω
  have hR : Measurable R := hX.sub (measurable_const.mul hY)
  have hind : IndepFun Y R P := (gaussian_regression_residual_independent P hXY hv).symm
  have hh := condDistrib_independent_noise P hY hR hind
    (fun z : ℝ × ℝ => z.2 + c * z.1) (by fun_prop)
  have heq : (fun ω => R ω + c * Y ω) = X := by funext ω; dsimp [R]; ring
  change condDistrib (fun ω => R ω + c * Y ω) Y P =ᵐ[P.map Y] _ at hh
  rw [heq] at hh
  filter_upwards [hh] with y hy
  rw [hy]
  change (P.map R).map (fun r => r + c * y) = _
  rw [gaussian_regression_residual_law P hXY hv, gaussianReal_map_add_const]
  congr 1
  dsimp [c]
  ring

end LectureNotes
