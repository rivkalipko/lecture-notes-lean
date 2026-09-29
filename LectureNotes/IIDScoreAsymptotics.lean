import LectureNotes.MLEAsymptotics

set_option autoImplicit false

/-! IID verification of the scalar score-root limit. Score and curvature
averages are actual finite sums of single-observation functions. Their CLT and
laws of large numbers are derived from independence and moment hypotheses. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {Ω Ξ Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Ω']

def sampleCriterionAverage (X : ℕ → Ω → Ξ) (g : Ξ → ℝ → ℝ)
    (n : ℕ) (ω : Ω) (θ : ℝ) : ℝ := (∑ i ∈ Finset.range n, g (X i ω) θ) / n

theorem sampleCriterionAverage_measurable (X : ℕ → Ω → Ξ) (g : Ξ → ℝ → ℝ)
    (hX : ∀ i, Measurable (X i)) (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (fun p : Ω × ℝ => sampleCriterionAverage X g n p.1 p.2) := by
  unfold sampleCriterionAverage
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  exact hg.comp (((hX i).comp measurable_fst).prodMk measurable_snd)

theorem sampleCriterionAverage_derivative (X : ℕ → Ω → Ξ) (g g' : Ξ → ℝ → ℝ)
    (D : Set ℝ) (hg : ∀ x θ, θ ∈ D → HasDerivWithinAt (g x) (g' x θ) D θ)
    (n : ℕ) (ω : Ω) (θ : ℝ) (hθ : θ ∈ D) :
    HasDerivWithinAt (sampleCriterionAverage X g n ω)
      (sampleCriterionAverage X g' n ω θ) D θ := by
  change HasDerivWithinAt (fun θ => (∑ i ∈ Finset.range n, g (X i ω) θ) / n)
    ((∑ i ∈ Finset.range n, g' (X i ω) θ) / n) D θ
  simpa only [Finset.sum_apply] using!
    (HasDerivWithinAt.sum (u := Finset.range n) (fun i _ => hg (X i ω) θ hθ)).div_const (n : ℝ)

theorem sampleCriterionAverage_lipschitz (X : ℕ → Ω → Ξ) (g : Ξ → ℝ → ℝ)
    (M : Ξ → ℝ) (D : Set ℝ) (θ₀ : ℝ)
    (hg : ∀ x θ, θ ∈ D → |g x θ - g x θ₀| ≤ M x * |θ - θ₀|)
    (n : ℕ) (ω : Ω) (θ : ℝ) (hθ : θ ∈ D) :
    |sampleCriterionAverage X g n ω θ - sampleCriterionAverage X g n ω θ₀| ≤
      ((∑ i ∈ Finset.range n, M (X i ω)) / n) * |θ - θ₀| := by
  unfold sampleCriterionAverage
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  calc
    |∑ i ∈ Finset.range n, (g (X i ω) θ - g (X i ω) θ₀)| / n ≤
        (∑ i ∈ Finset.range n, |g (X i ω) θ - g (X i ω) θ₀|) / n :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg n)
    _ ≤ (∑ i ∈ Finset.range n, M (X i ω) * |θ - θ₀|) / n :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => hg (X i ω) θ hθ))
        (Nat.cast_nonneg n)
    _ = _ := by rw [← Finset.sum_mul]; ring

variable {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

theorem iid_statistic_average_limit (X : ℕ → Ω → Ξ) (g : Ξ → ℝ)
    (hX : ∀ i, Measurable (X i)) (hg : Measurable g)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hint : Integrable (fun ω => g (X 0 ω)) P) :
    ConvergesInProbability P (fun n ω => (∑ i ∈ Finset.range n, g (X i ω)) / n)
      (fun _ => ∫ ω, g (X 0 ω) ∂P) := by
  apply almost_sure_implies_probability
    (fun n => ((Finset.measurable_sum _ (fun i _ => hg.comp (hX i))).div_const (n : ℝ)).aemeasurable)
  exact strong_law_of_large_numbers hint
    (fun i j hij => (hind.comp (fun _ => g) (fun _ => hg)).indepFun hij)
    (fun i => (hident i).comp hg)

theorem sqrt_times_average (n : ℕ) (s : ℝ) :
    Real.sqrt n * (s / n) = (Real.sqrt n)⁻¹ * s := by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).ne'
  have hsq := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  field_simp
  rw [hsq]
  ring

theorem iid_zero_mean_score_clt (X : ℕ → Ω → Ξ) (g : Ξ → ℝ)
    (hg : Measurable g) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (h₂ : MemLp (fun ω => g (X 0 ω)) 2 P)
    (hmean : (∫ ω, g (X 0 ω) ∂P) = 0) {I : ℝ≥0}
    (hvar : Var[fun ω => g (X 0 ω); P] = I) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 I) Q) :
    ConvergesInDistribution P Q
      (fun n ω => Real.sqrt n * ((∑ i ∈ Finset.range n, g (X i ω)) / n)) Z := by
  have hv : Var[fun ω => g (X 0 ω); P].toNNReal = I := by rw [hvar]; simp
  have h := central_limit_theorem (X := fun i ω => g (X i ω))
    (by simpa only [hv] using hZ) h₂
    (hind.comp (fun _ => g) (fun _ => hg)) (fun i => (hident i).comp hg)
  simpa only [hmean, mul_zero, sub_zero, sqrt_times_average] using h

/-- A scalar IID score-root normality theorem with explicit, noncircular
regularity. The score CLT and the two LLNs are consequences, not assumptions.
The third-derivative envelope controls curvature at the random estimate. -/
theorem iid_consistent_score_root_normal
    (X : ℕ → Ω → Ξ) (score curvature third : Ξ → ℝ → ℝ) (envelope : Ξ → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (D : Set ℝ) (hD : Convex ℝ D) (θ₀ : ℝ) (hθ : θ₀ ∈ D)
    (I : ℝ≥0) (hI : 0 < I)
    (hsm : Measurable (Function.uncurry score))
    (hcm : Measurable (fun x => curvature x θ₀)) (hem : Measurable envelope)
    (he0 : ∀ x, 0 ≤ envelope x)
    (hsd : ∀ x θ, θ ∈ D → HasDerivWithinAt (score x) (curvature x θ) D θ)
    (hcd : ∀ x θ, θ ∈ D → HasDerivWithinAt (curvature x) (third x θ) D θ)
    (hthird : ∀ x θ, θ ∈ D → |third x θ| ≤ envelope x)
    (hs₂ : MemLp (fun ω => score (X 0 ω) θ₀) 2 P)
    (hsmean : (∫ ω, score (X 0 ω) θ₀ ∂P) = 0)
    (hsvar : Var[fun ω => score (X 0 ω) θ₀; P] = I)
    (hcint : Integrable (fun ω => curvature (X 0 ω) θ₀) P)
    (hcmean : (∫ ω, curvature (X 0 ω) θ₀ ∂P) = -(I : ℝ))
    (heint : Integrable (fun ω => envelope (X 0 ω)) P)
    (T : ℕ → Ω → ℝ) (hTin : ∀ n ω, T n ω ∈ D) (hTm : ∀ n, Measurable (T n))
    (hT : ConvergesInProbability P T (fun _ => θ₀))
    (hroot : ∀ n ω, sampleCriterionAverage X score n ω (T n ω) = 0)
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 I) Q) :
    ConvergesInDistribution P Q (fun n ω => Real.sqrt n * (T n ω - θ₀))
      (fun ω => Z ω / I) ∧
        HasLaw (fun ω => Z ω / I) (gaussianReal 0 I⁻¹) Q := by
  let B n ω := (∑ i ∈ Finset.range n, envelope (X i ω)) / n
  have hBmeas n : Measurable (B n) :=
    (Finset.measurable_sum _ (fun i _ => hem.comp (hX i))).div_const (n : ℝ)
  have hCmeas n : Measurable (fun ω => sampleCriterionAverage X curvature n ω θ₀) :=
    (Finset.measurable_sum _ (fun i _ => hcm.comp (hX i))).div_const (n : ℝ)
  have hscore0 : Measurable (fun x => score x θ₀) :=
    hsm.comp (measurable_id.prodMk measurable_const)
  have hcurv x θ (hθ' : θ ∈ D) :
      |curvature x θ - curvature x θ₀| ≤ envelope x * |θ - θ₀| := by
    simpa only [Real.norm_eq_abs] using hD.norm_image_sub_le_of_norm_hasDerivWithin_le
      (hcd x) (by simpa only [Real.norm_eq_abs] using hthird x) hθ hθ'
  refine ⟨?_, ?_⟩
  · apply consistent_score_root_limit
      (sampleCriterionAverage X score) (sampleCriterionAverage X curvature) T B
      (fun n => Real.sqrt n) D hD θ₀ I (∫ ω, envelope (X 0 ω) ∂P)
      (by exact_mod_cast hI) hθ hTin hTm
      (sampleCriterionAverage_measurable X score hX hsm)
      (fun n => (hBmeas n).aemeasurable) (fun n => (hCmeas n).aemeasurable)
    · intro n ω
      exact div_nonneg (Finset.sum_nonneg (fun i _ => he0 (X i ω))) (Nat.cast_nonneg n)
    · exact sampleCriterionAverage_derivative X score curvature D hsd
    · exact sampleCriterionAverage_lipschitz X curvature envelope D θ₀ hcurv
    · exact hroot
    · exact hT
    · exact iid_statistic_average_limit X envelope hX hem hind hident heint
    · simpa only [sampleCriterionAverage, hcmean] using
        iid_statistic_average_limit X (fun x => curvature x θ₀) hX hcm hind hident hcint
    · exact iid_zero_mean_score_clt X (fun x => score x θ₀) hscore0 hind hident
        hs₂ hsmean hsvar hZ
  · have h := gaussianReal_div_const hZ (I : ℝ)
    convert! h using 1
    simp only [zero_div]
    congr 1
    apply Subtype.ext
    change (I : ℝ)⁻¹ = (I : ℝ) / (I : ℝ) ^ 2
    have hI0 : (I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
    field_simp

/-- An interior maximizer of the actual average log likelihood is a zero of
the sample score, whose derivative relation is proved term by term. -/
theorem sample_score_zero_at_interior_maximum
    (X : ℕ → Ω → Ξ) (logDensity score : Ξ → ℝ → ℝ)
    (D : Set ℝ) (hD : IsOpen D)
    (hd : ∀ x θ, θ ∈ D → HasDerivWithinAt (logDensity x) (score x θ) D θ)
    (n : ℕ) (ω : Ω) (t : ℝ) (ht : t ∈ D)
    (hmax : ∀ θ ∈ D, sampleCriterionAverage X logDensity n ω θ ≤
      sampleCriterionAverage X logDensity n ω t) :
    sampleCriterionAverage X score n ω t = 0 := by
  have hderiv := (sampleCriterionAverage_derivative X logDensity score D hd n ω t ht).hasDerivAt
    (hD.mem_nhds ht)
  have hm : IsLocalMax (sampleCriterionAverage X logDensity n ω) t := by
    filter_upwards [hD.mem_nhds ht] with θ hθ using hmax θ hθ
  exact hderiv.deriv.symm.trans hm.deriv_eq_zero

/-- L7 T2, scalar form, with explicit sufficient hypotheses and consistency.
`logDensity` is the single-observation log likelihood; its first three
derivatives and the two information identities are specified explicitly.
The proof derives the score CLT, curvature LLN, random-curvature control, and
the MLE first-order equation before applying Slutsky. -/
theorem iid_mle_asymptotic_normality
    (X : ℕ → Ω → Ξ) (logDensity score curvature third : Ξ → ℝ → ℝ)
    (envelope : Ξ → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (D : Set ℝ) (hD : Convex ℝ D) (hDopen : IsOpen D) (θ₀ : ℝ) (hθ : θ₀ ∈ D)
    (I : ℝ≥0) (hI : 0 < I)
    (hsm : Measurable (Function.uncurry score))
    (hcm : Measurable (fun x => curvature x θ₀)) (hem : Measurable envelope)
    (he0 : ∀ x, 0 ≤ envelope x)
    (hld : ∀ x θ, θ ∈ D → HasDerivWithinAt (logDensity x) (score x θ) D θ)
    (hsd : ∀ x θ, θ ∈ D → HasDerivWithinAt (score x) (curvature x θ) D θ)
    (hcd : ∀ x θ, θ ∈ D → HasDerivWithinAt (curvature x) (third x θ) D θ)
    (hthird : ∀ x θ, θ ∈ D → |third x θ| ≤ envelope x)
    (hs₂ : MemLp (fun ω => score (X 0 ω) θ₀) 2 P)
    (hsmean : (∫ ω, score (X 0 ω) θ₀ ∂P) = 0)
    (hsvar : Var[fun ω => score (X 0 ω) θ₀; P] = I)
    (hcint : Integrable (fun ω => curvature (X 0 ω) θ₀) P)
    (hcmean : (∫ ω, curvature (X 0 ω) θ₀ ∂P) = -(I : ℝ))
    (heint : Integrable (fun ω => envelope (X 0 ω)) P)
    (T : ℕ → Ω → ℝ) (hTin : ∀ n ω, T n ω ∈ D) (hTm : ∀ n, Measurable (T n))
    (hT : ConvergesInProbability P T (fun _ => θ₀))
    (hmax : ∀ n ω θ, θ ∈ D → sampleCriterionAverage X logDensity n ω θ ≤
      sampleCriterionAverage X logDensity n ω (T n ω))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 I) Q) :
    ConvergesInDistribution P Q (fun n ω => Real.sqrt n * (T n ω - θ₀))
      (fun ω => Z ω / I) ∧
        HasLaw (fun ω => Z ω / I) (gaussianReal 0 I⁻¹) Q := by
  exact iid_consistent_score_root_normal X score curvature third envelope hX hind hident
    D hD θ₀ hθ I hI hsm hcm hem he0 hsd hcd hthird hs₂ hsmean hsvar hcint hcmean heint
    T hTin hTm hT
    (fun n ω => sample_score_zero_at_interior_maximum X logDensity score D hDopen hld
      n ω (T n ω) (hTin n ω) (hmax n ω)) hZ

end LectureNotes
