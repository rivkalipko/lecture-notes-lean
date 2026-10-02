import LectureNotes.IIDScoreAsymptotics

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- Joint measurability ensures that evaluating the sample criterion at a
measurable estimated parameter gives a measurable statistic. -/
theorem sampleCriterionAverage_at_estimator_measurable
    (X : ℕ → Ω → Ξ) (g : Ξ → ℝ → ℝ)
    (hX : ∀ i, Measurable (X i)) (hgm : Measurable (Function.uncurry g))
    (T : ℕ → Ω → ℝ) (hTm : ∀ n, Measurable (T n)) (n : ℕ) :
    Measurable (fun ω => sampleCriterionAverage X g n ω (T n ω)) :=
  (sampleCriterionAverage_measurable X g hX hgm n).comp
    (measurable_id.prodMk (hTm n))

/-- A locally Lipschitz statistic can be averaged at a consistent random
parameter. The fixed-parameter and envelope LLNs follow from IID sampling and
integrability, so evaluation at an estimated parameter is justified. -/
theorem iid_plugin_statistic_consistency
    (X : ℕ → Ω → Ξ) (g : Ξ → ℝ → ℝ) (envelope : Ξ → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (D : Set ℝ) (θ₀ : ℝ)
    (hgm : Measurable (Function.uncurry g)) (hem : Measurable envelope)
    (hgi : Integrable (fun ω => g (X 0 ω) θ₀) P)
    (hei : Integrable (fun ω => envelope (X 0 ω)) P)
    (hLip : ∀ x θ, θ ∈ D → |g x θ - g x θ₀| ≤ envelope x * |θ - θ₀|)
    (T : ℕ → Ω → ℝ) (hTin : ∀ n ω, T n ω ∈ D) (hTm : ∀ n, Measurable (T n))
    (hT : ConvergesInProbability P T (fun _ => θ₀)) :
    ConvergesInProbability P (fun n ω => sampleCriterionAverage X g n ω (T n ω))
      (fun _ => ∫ ω, g (X 0 ω) θ₀ ∂P) := by
  have hgm0 : Measurable (fun x => g x θ₀) :=
    hgm.comp (measurable_id.prodMk measurable_const)
  let B n ω := (∑ i ∈ Finset.range n, envelope (X i ω)) / n
  let m := ∫ ω, g (X 0 ω) θ₀ ∂P
  let A n ω := sampleCriterionAverage X g n ω θ₀
  have hBm n : Measurable (B n) :=
    (Finset.measurable_sum _ (fun i _ => hem.comp (hX i))).div_const (n : ℝ)
  have hAm n : Measurable (A n) :=
    (Finset.measurable_sum _ (fun i _ => hgm0.comp (hX i))).div_const (n : ℝ)
  have hTm' n : AEMeasurable (fun ω => |T n ω - θ₀|) P :=
    ((hTm n).sub_const θ₀).abs.aemeasurable
  have hB : ConvergesInProbability P B (fun _ => ∫ ω, envelope (X 0 ω) ∂P) :=
    iid_statistic_average_limit X envelope hX hem hind hident hei
  have hA : ConvergesInProbability P A (fun _ => m) :=
    iid_statistic_average_limit X (fun x => g x θ₀) hX hgm0 hind hident hgi
  have hTabs : ConvergesInProbability P (fun n ω => |T n ω - θ₀|) (fun _ => 0) := by
    simpa using continuous_mapping_probability_const (g := fun x => |x - θ₀|) (by fun_prop) hT
  have hprod : ConvergesInProbability P (fun n ω => B n ω * |T n ω - θ₀|) (fun _ => 0) :=
    slutsky_mul_zero (probability_implies_distribution (fun n => (hBm n).aemeasurable) hB)
      hTabs hTm'
  have hfixed : ConvergesInProbability P (fun n ω => |A n ω - m|) (fun _ => 0) := by
    simpa using continuous_mapping_probability_const (g := fun x => |x - m|) (by fun_prop) hA
  let err n ω := B n ω * |T n ω - θ₀| + |A n ω - m|
  have herr : ConvergesInProbability P err (fun _ => 0) := by
    apply distribution_to_constant_implies_probability (Q := P)
    simpa only [err, add_zero] using! slutsky_add
      (probability_implies_distribution (fun n => (hBm n).aemeasurable.mul (hTm' n)) hprod)
      hfixed (fun n => ((hAm n).sub_const m).abs.aemeasurable)
  have hbound n ω : |sampleCriterionAverage X g n ω (T n ω) - m| ≤ err n ω := by
    have hL := sampleCriterionAverage_lipschitz X g envelope D θ₀ hLip n ω (T n ω) (hTin n ω)
    have htriangle := abs_add_le
      (sampleCriterionAverage X g n ω (T n ω) - A n ω) (A n ω - m)
    have heq : sampleCriterionAverage X g n ω (T n ω) - A n ω + (A n ω - m) =
        sampleCriterionAverage X g n ω (T n ω) - m := by ring
    rw [heq] at htriangle
    exact htriangle.trans (add_le_add hL le_rfl)
  rw [ConvergesInProbability, tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hb n : P.real {ω | ε ≤ ‖sampleCriterionAverage X g n ω (T n ω) - m‖} ≤
      P.real {ω | ε ≤ ‖err n ω - 0‖} := by
    apply measureReal_mono _ (measure_ne_top P _)
    intro ω hω
    simp only [mem_ofPred_eq, Real.norm_eq_abs, sub_zero] at hω ⊢
    exact hω.trans ((hbound n ω).trans (le_abs_self _))
  exact squeeze_zero (fun _ => measureReal_nonneg) hb
    (tendstoInMeasure_iff_measureReal_norm.mp herr ε hε)

/-- Negative sample curvature at a consistent estimate consistently estimates
the negative population curvature. A third-derivative envelope controls the
random evaluation point; no maximization or information equality is needed. -/
theorem iid_observed_information_consistency
    (X : ℕ → Ω → Ξ) (curvature third : Ξ → ℝ → ℝ) (envelope : Ξ → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (D : Set ℝ) (hD : Convex ℝ D) (θ₀ : ℝ) (hθ : θ₀ ∈ D)
    (hcm : Measurable (Function.uncurry curvature)) (hem : Measurable envelope)
    (hci : Integrable (fun ω => curvature (X 0 ω) θ₀) P)
    (hei : Integrable (fun ω => envelope (X 0 ω)) P)
    (hcd : ∀ x θ, θ ∈ D → HasDerivWithinAt (curvature x) (third x θ) D θ)
    (hthird : ∀ x θ, θ ∈ D → |third x θ| ≤ envelope x)
    (T : ℕ → Ω → ℝ) (hTin : ∀ n ω, T n ω ∈ D) (hTm : ∀ n, Measurable (T n))
    (hT : ConvergesInProbability P T (fun _ => θ₀)) :
    ConvergesInProbability P (fun n ω => -sampleCriterionAverage X curvature n ω (T n ω))
      (fun _ => -(∫ ω, curvature (X 0 ω) θ₀ ∂P)) := by
  have hLip x θ (hθ' : θ ∈ D) :
      |curvature x θ - curvature x θ₀| ≤ envelope x * |θ - θ₀| := by
    simpa only [Real.norm_eq_abs] using hD.norm_image_sub_le_of_norm_hasDerivWithin_le
      (hcd x) (by simpa only [Real.norm_eq_abs] using hthird x) hθ hθ'
  exact continuous_mapping_probability_const (g := fun x : ℝ => -x) (by fun_prop)
    (iid_plugin_statistic_consistency X curvature envelope hX hind hident D θ₀
      hcm hem hci hei hLip T hTin hTm hT)

end LectureNotes
