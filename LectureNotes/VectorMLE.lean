import LectureNotes.VectorScoreAsymptotics
import LectureNotes.VectorScoreCLT
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false

/-! L7's vector estimating-equation and MLE limits from IID observations.
The score CLT, derivative LLN, and envelope LLN are derived from explicit
moments and independence; consistency remains an explicit hypothesis. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped Topology InnerProductSpace

variable {Ω Ξ Ω' E F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [MeasurableSpace Ω'] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual sample average of a vector-valued criterion or its derivative. -/
def sampleVectorAverage (X : ℕ → Ω → Ξ) (g : Ξ → E → F)
    (n : ℕ) (ω : Ω) (θ : E) : F := (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, g (X i ω) θ

theorem sampleVectorAverage_derivative (X : ℕ → Ω → Ξ)
    (g : Ξ → E → F) (g' : Ξ → E → E →L[ℝ] F) (D : Set E)
    (hg : ∀ x θ, θ ∈ D → HasFDerivWithinAt (g x) (g' x θ) D θ)
    (n : ℕ) (ω : Ω) (θ : E) (hθ : θ ∈ D) :
    HasFDerivWithinAt (sampleVectorAverage X g n ω)
      (sampleVectorAverage X g' n ω θ) D θ := by
  convert! (HasFDerivWithinAt.sum (u := Finset.range n)
    (fun i _ => hg (X i ω) θ hθ)).const_smul (n : ℝ)⁻¹ using 1
  funext t
  simp [sampleVectorAverage]

theorem sampleVectorAverage_lipschitz (X : ℕ → Ω → Ξ) (g : Ξ → E → F)
    (M : Ξ → ℝ) (D : Set E) (θ : E)
    (hg : ∀ x t, t ∈ D → ‖g x t - g x θ‖ ≤ M x * ‖t - θ‖)
    (n : ℕ) (ω : Ω) (t : E) (ht : t ∈ D) :
    ‖sampleVectorAverage X g n ω t - sampleVectorAverage X g n ω θ‖ ≤
      ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, M (X i ω)) * ‖t - θ‖ := by
  simp only [sampleVectorAverage, ← smul_sub, ← Finset.sum_sub_distrib,
    norm_smul, norm_inv, Real.norm_natCast]
  calc
    (n : ℝ)⁻¹ * ‖∑ i ∈ Finset.range n, (g (X i ω) t - g (X i ω) θ)‖ ≤
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ‖g (X i ω) t - g (X i ω) θ‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, M (X i ω) * ‖t - θ‖ := by
      gcongr with i hi
      exact hg (X i ω) t ht
    _ = _ := by rw [← Finset.sum_mul]; ring

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology E] [SecondCountableTopology F]

theorem sampleVectorAverage_measurable (X : ℕ → Ω → Ξ) (g : Ξ → E → F)
    (hX : ∀ i, Measurable (X i)) (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (fun p : Ω × E => sampleVectorAverage X g n p.1 p.2) := by
  apply Measurable.const_smul
  apply Finset.measurable_sum
  intro i _
  exact hg.comp (((hX i).comp measurable_fst).prodMk measurable_snd)

variable {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

theorem iid_vector_statistic_average_limit [CompleteSpace F]
    (X : ℕ → Ω → Ξ) (g : Ξ → F)
    (hX : ∀ i, Measurable (X i)) (hg : Measurable g)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hint : Integrable (fun ω => g (X 0 ω)) P) :
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, g (X i ω))
      atTop (fun _ => ∫ ω, g (X 0 ω) ∂P) := by
  apply tendstoInMeasure_of_tendsto_ae
    (fun n => ((Finset.measurable_sum _ (fun i _ => hg.comp (hX i))).const_smul
      (n : ℝ)⁻¹).aestronglyMeasurable)
  exact strong_law_ae (fun i ω => g (X i ω)) hint
    (fun i j hij => (hind.comp (fun _ => g) (fun _ => hg)).indepFun hij)
    (fun i => (hident i).comp hg)

variable {d : ℕ}

/-- Vector score-root asymptotic normality with actual IID derivative averages
and an integrable bound on the next derivative. It also applies to a
misspecified criterion: expected negative curvature and score covariance may
differ. -/
theorem iid_consistent_vector_score_root_normal
    (X : ℕ → Ω → Ξ) (score : Ξ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : Ξ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (L' : Ξ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ]
      (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (envelope : Ξ → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (D : Set (EuclideanSpace ℝ (Fin d))) (hD : Convex ℝ D)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : θ ∈ D)
    (H : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hsm : Measurable (Function.uncurry score))
    (hLm : Measurable (fun x => L x θ)) (hem : Measurable envelope)
    (he0 : ∀ x, 0 ≤ envelope x)
    (hsd : ∀ x t, t ∈ D → HasFDerivWithinAt (score x) (L x t) D t)
    (hLd : ∀ x t, t ∈ D → HasFDerivWithinAt (L x) (L' x t) D t)
    (hthird : ∀ x t, t ∈ D → ‖L' x t‖ ≤ envelope x)
    (hs₂ : MemLp (fun ω => score (X 0 ω) θ) 2 P)
    (hsmean : (∫ ω, score (X 0 ω) θ ∂P) = 0)
    (hLint : Integrable (fun ω => L (X 0 ω) θ) P)
    (hLmean : (∫ ω, L (X 0 ω) θ ∂P) = -H.toContinuousLinearMap)
    (heint : Integrable (fun ω => envelope (X 0 ω)) P)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hTin : ∀ n ω, T n ω ∈ D) (hTm : ∀ n, Measurable (T n))
    (hT : TendstoInMeasure P T atTop (fun _ => θ))
    (hroot : ∀ n ω, sampleVectorAverage X score n ω (T n ω) = 0)
    {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    (hZ : HasLaw Z (multivariateGaussian 0
      (vectorCovariance P (fun ω => score (X 0 ω) θ))) Q) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ))
      atTop (fun ω => H.symm (Z ω)) (fun _ => P) Q ∧
    HasLaw (fun ω => H.symm (Z ω))
      (multivariateGaussian 0
        ((toEuclideanCLM (𝕜 := ℝ)).symm H.symm.toContinuousLinearMap *
          vectorCovariance P (fun ω => score (X 0 ω) θ) *
          ((toEuclideanCLM (𝕜 := ℝ)).symm H.symm.toContinuousLinearMap)ᵀ)) Q := by
  refine ⟨?_, ?_⟩
  swap
  · simpa only [map_zero] using!
      gaussian_clm_transform (vectorCovariance_posSemidef hs₂) hZ H.symm.toContinuousLinearMap
  let B (n : ℕ) ω := (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, envelope (X i ω)
  have hLbound x t (ht : t ∈ D) : ‖L x t - L x θ‖ ≤ envelope x * ‖t - θ‖ :=
    hD.norm_image_sub_le_of_norm_hasFDerivWithin_le (hLd x) (hthird x) hθ ht
  apply consistent_vector_score_root_limit
    (sampleVectorAverage X score) (sampleVectorAverage X L) T B (fun n => Real.sqrt n)
    D hD θ H (∫ ω, envelope (X 0 ω) ∂P) hθ hTin hTm
    (sampleVectorAverage_measurable X score hX hsm)
  · intro n ω
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      (Finset.sum_nonneg (fun i _ => he0 (X i ω)))
  · exact sampleVectorAverage_derivative X score L D hsd
  · exact sampleVectorAverage_lipschitz X L envelope D θ hLbound
  · exact hroot
  · exact hT
  · simpa only [B, smul_eq_mul] using
      iid_vector_statistic_average_limit X envelope hX hem hind hident heint
  · simpa only [sampleVectorAverage, hLmean] using
      iid_vector_statistic_average_limit X (fun x => L x θ) hX hLm hind hident hLint
  · exact iid_zero_mean_vector_score_clt X (fun x => score x θ)
      (hsm.comp (measurable_id.prodMk measurable_const)) hind hident hs₂ hsmean hZ

/-- The gradient of the actual sample criterion vanishes at an interior
maximizer. The average-gradient identity is obtained by differentiation of
the finite sum. -/
theorem sample_vector_score_zero_at_interior_maximum
    (X : ℕ → Ω → Ξ) (criterion : Ξ → EuclideanSpace ℝ (Fin d) → ℝ)
    (score : Ξ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (D : Set (EuclideanSpace ℝ (Fin d))) (hD : IsOpen D)
    (hd : ∀ x t, t ∈ D → HasFDerivWithinAt (criterion x) (innerSL ℝ (score x t)) D t)
    (n : ℕ) (ω : Ω) (t : EuclideanSpace ℝ (Fin d)) (ht : t ∈ D)
    (hmax : ∀ θ ∈ D, sampleVectorAverage X criterion n ω θ ≤
      sampleVectorAverage X criterion n ω t) :
    sampleVectorAverage X score n ω t = 0 := by
  have hd' : HasFDerivWithinAt (sampleVectorAverage X criterion n ω)
      (innerSL ℝ (sampleVectorAverage X score n ω t)) D t := by
    convert! sampleVectorAverage_derivative X criterion (fun x t => innerSL ℝ (score x t)) D hd n ω t ht using 1
    simp [sampleVectorAverage]
  have hm : IsLocalMax (sampleVectorAverage X criterion n ω) t := by
    filter_upwards [hD.mem_nhds ht] with θ hθ using hmax θ hθ
  have he : innerSL ℝ (sampleVectorAverage X score n ω t) = 0 :=
    (hd'.hasFDerivAt (hD.mem_nhds ht)).fderiv.symm.trans hm.fderiv_eq_zero
  apply norm_eq_zero.mp
  simpa using congrArg norm he

/-- Vector MLE and pseudo-MLE normality for a consistent interior maximizer.
For a misspecified criterion the Gaussian transform has the sandwich covariance;
for a correctly specified likelihood the information identity specializes it. -/
theorem iid_vector_mle_asymptotic_normality
    (X : ℕ → Ω → Ξ) (criterion : Ξ → EuclideanSpace ℝ (Fin d) → ℝ)
    (score : Ξ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : Ξ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (L' : Ξ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ]
      (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (envelope : Ξ → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (D : Set (EuclideanSpace ℝ (Fin d))) (hD : Convex ℝ D) (hDopen : IsOpen D)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : θ ∈ D)
    (H : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hsm : Measurable (Function.uncurry score))
    (hLm : Measurable (fun x => L x θ)) (hem : Measurable envelope)
    (he0 : ∀ x, 0 ≤ envelope x)
    (hld : ∀ x t, t ∈ D → HasFDerivWithinAt (criterion x) (innerSL ℝ (score x t)) D t)
    (hsd : ∀ x t, t ∈ D → HasFDerivWithinAt (score x) (L x t) D t)
    (hLd : ∀ x t, t ∈ D → HasFDerivWithinAt (L x) (L' x t) D t)
    (hthird : ∀ x t, t ∈ D → ‖L' x t‖ ≤ envelope x)
    (hs₂ : MemLp (fun ω => score (X 0 ω) θ) 2 P)
    (hsmean : (∫ ω, score (X 0 ω) θ ∂P) = 0)
    (hLint : Integrable (fun ω => L (X 0 ω) θ) P)
    (hLmean : (∫ ω, L (X 0 ω) θ ∂P) = -H.toContinuousLinearMap)
    (heint : Integrable (fun ω => envelope (X 0 ω)) P)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hTin : ∀ n ω, T n ω ∈ D) (hTm : ∀ n, Measurable (T n))
    (hT : TendstoInMeasure P T atTop (fun _ => θ))
    (hmax : ∀ n ω t, t ∈ D → sampleVectorAverage X criterion n ω t ≤
      sampleVectorAverage X criterion n ω (T n ω))
    {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    (hZ : HasLaw Z (multivariateGaussian 0
      (vectorCovariance P (fun ω => score (X 0 ω) θ))) Q) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ))
      atTop (fun ω => H.symm (Z ω)) (fun _ => P) Q ∧
    HasLaw (fun ω => H.symm (Z ω))
      (multivariateGaussian 0
        ((toEuclideanCLM (𝕜 := ℝ)).symm H.symm.toContinuousLinearMap *
          vectorCovariance P (fun ω => score (X 0 ω) θ) *
          ((toEuclideanCLM (𝕜 := ℝ)).symm H.symm.toContinuousLinearMap)ᵀ)) Q := by
  exact iid_consistent_vector_score_root_normal X score L L' envelope hX hind hident
    D hD θ hθ H hsm hLm hem he0 hsd hLd hthird hs₂ hsmean hLint hLmean heint
    T hTin hTm hT
    (fun n ω => sample_vector_score_zero_at_interior_maximum X criterion score D hDopen
      hld n ω (T n ω) (hTin n ω) (hmax n ω)) hZ

/-- The second information equality reduces the sandwich covariance to the
inverse information. Symmetry comes from the actual score covariance. -/
theorem vector_information_inverse_gaussian_law
    (H : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    {J : Matrix (Fin d) (Fin d) ℝ} (hJ : J.PosSemidef)
    {Z : Ω' → EuclideanSpace ℝ (Fin d)} (hZ : HasLaw Z (multivariateGaussian 0 J) Q)
    (hinfo : toEuclideanCLM (𝕜 := ℝ) J = H.toContinuousLinearMap) :
    HasLaw (fun ω => H.symm (Z ω)) (multivariateGaussian 0 J⁻¹) Q := by
  let A := (toEuclideanCLM (𝕜 := ℝ)).symm H.symm.toContinuousLinearMap
  have hleft : A * J = 1 := by
    apply (toEuclideanCLM (𝕜 := ℝ)).injective
    rw [map_mul, map_one]
    change toEuclideanCLM (𝕜 := ℝ) A * toEuclideanCLM (𝕜 := ℝ) J = 1
    rw [hinfo]
    have ha : toEuclideanCLM (𝕜 := ℝ) A = H.symm.toContinuousLinearMap :=
      (toEuclideanCLM (𝕜 := ℝ)).apply_symm_apply _
    rw [ha]
    apply ContinuousLinearMap.ext
    intro x
    exact H.symm_apply_apply x
  have hA : J⁻¹ = A := Matrix.inv_eq_left_inv hleft
  have hJsym : J.IsSymm := by
    change Jᵀ = J
    simpa only [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] using! hJ.isHermitian
  have hsand : A * J * Aᵀ = J⁻¹ := by
    rw [hleft, one_mul, ← hA]
    exact hJsym.inv
  have h := LectureNotes.gaussian_clm_transform hJ hZ H.symm.toContinuousLinearMap
  change HasLaw (fun ω => H.symm (Z ω)) (multivariateGaussian (H.symm 0) (A * J * Aᵀ)) Q at h
  simpa only [map_zero, hsand] using h

/-- L7's vector MLE information-inverse limit, under explicit sufficient
regularity and consistency, including the second information equality. -/
theorem iid_vector_mle_inverse_information_limit
    (X : ℕ → Ω → Ξ) (criterion : Ξ → EuclideanSpace ℝ (Fin d) → ℝ)
    (score : Ξ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : Ξ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (L' : Ξ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ]
      (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (envelope : Ξ → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (D : Set (EuclideanSpace ℝ (Fin d))) (hD : Convex ℝ D) (hDopen : IsOpen D)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : θ ∈ D)
    (H : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hsm : Measurable (Function.uncurry score))
    (hLm : Measurable (fun x => L x θ)) (hem : Measurable envelope)
    (he0 : ∀ x, 0 ≤ envelope x)
    (hld : ∀ x t, t ∈ D → HasFDerivWithinAt (criterion x) (innerSL ℝ (score x t)) D t)
    (hsd : ∀ x t, t ∈ D → HasFDerivWithinAt (score x) (L x t) D t)
    (hLd : ∀ x t, t ∈ D → HasFDerivWithinAt (L x) (L' x t) D t)
    (hthird : ∀ x t, t ∈ D → ‖L' x t‖ ≤ envelope x)
    (hs₂ : MemLp (fun ω => score (X 0 ω) θ) 2 P)
    (hsmean : (∫ ω, score (X 0 ω) θ ∂P) = 0)
    (hLint : Integrable (fun ω => L (X 0 ω) θ) P)
    (hinfo : toEuclideanCLM (𝕜 := ℝ) (vectorCovariance P (fun ω => score (X 0 ω) θ)) =
      H.toContinuousLinearMap)
    (hLmean : (∫ ω, L (X 0 ω) θ ∂P) = -H.toContinuousLinearMap)
    (heint : Integrable (fun ω => envelope (X 0 ω)) P)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hTin : ∀ n ω, T n ω ∈ D) (hTm : ∀ n, Measurable (T n))
    (hT : TendstoInMeasure P T atTop (fun _ => θ))
    (hmax : ∀ n ω t, t ∈ D → sampleVectorAverage X criterion n ω t ≤
      sampleVectorAverage X criterion n ω (T n ω))
    {Z : Ω' → EuclideanSpace ℝ (Fin d)}
    (hZ : HasLaw Z (multivariateGaussian 0
      (vectorCovariance P (fun ω => score (X 0 ω) θ))) Q) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ))
      atTop (fun ω => H.symm (Z ω)) (fun _ => P) Q ∧
    HasLaw (fun ω => H.symm (Z ω))
      (multivariateGaussian 0 (vectorCovariance P (fun ω => score (X 0 ω) θ))⁻¹) Q := by
  refine ⟨(iid_vector_mle_asymptotic_normality X criterion score L L' envelope hX hind hident
    D hD hDopen θ hθ H hsm hLm hem he0 hld hsd hLd hthird hs₂ hsmean hLint hLmean heint
    T hTin hTm hT hmax hZ).1, ?_⟩
  exact vector_information_inverse_gaussian_law H (vectorCovariance_posSemidef hs₂) hZ hinfo

end LectureNotes
