import LectureNotes.LogisticRegression
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false

/-! L7's fixed-design logistic likelihood, score, and Hessian. The derivatives
are derivatives of the actual log probability of the sample. Concavity gives
global optimality of a score root; full column rank gives uniqueness, but does
not guarantee that a finite maximizer exists. -/
noncomputable section
namespace LectureNotes
open Set

def logisticPredictor {p : ℕ} (x : Fin p → ℝ) : (Fin p → ℝ) →L[ℝ] ℝ :=
  ∑ j, x j • ContinuousLinearMap.proj j

theorem logisticPredictor_apply {p : ℕ} (x β : Fin p → ℝ) :
    logisticPredictor x β = ∑ j, x j * β j := by
  simp [logisticPredictor]

def logisticSampleLogLikelihood {n p : ℕ} (y : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) : ℝ :=
  ∑ i, logisticLogLikelihood (y i) (logisticPredictor (x i) β)

def logisticScore {n p : ℕ} (y : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) : Fin p → ℝ :=
  fun j => ∑ i, ((if y i then 1 else 0) - logistic (logisticPredictor (x i) β)) * x i j

def logisticHessian {n p : ℕ} (x : Fin n → Fin p → ℝ)
    (β : Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => ∑ i, -(logistic (logisticPredictor (x i) β) *
    (1 - logistic (logisticPredictor (x i) β))) * x i j * x i k

theorem logistic_sample_log_probability {n p : ℕ} (y : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) :
    Real.log (∏ i, logisticMass (y i) (logisticPredictor (x i) β)) =
      logisticSampleLogLikelihood y x β := by
  rw [Real.log_prod (fun i _ => (logisticMass_positive _ _).ne')]
  exact Finset.sum_congr rfl (fun i _ => logistic_log_likelihood _ _)

theorem hasFDerivAt_logisticSampleLogLikelihood {n p : ℕ} (y : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) :
    HasFDerivAt (logisticSampleLogLikelihood y x) (logisticPredictor (logisticScore y x β)) β := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_logisticLogLikelihood (y i) (logisticPredictor (x i) β)).comp_hasFDerivAt β
      (logisticPredictor (x i)).hasFDerivAt)
  convert! h using 1
  ext v
  simp only [logisticPredictor_apply, logisticScore, sum_apply,
    smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The derivative of the score has the stated Hessian entries. -/
theorem hasFDerivAt_logisticScore {n p : ℕ} (y : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) :
    HasFDerivAt (logisticScore y x)
      (ContinuousLinearMap.pi (fun j => logisticPredictor (logisticHessian x β j))) β := by
  apply hasFDerivAt_pi.mpr
  intro j
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (((hasDerivAt_logistic (logisticPredictor (x i) β)).comp_hasFDerivAt β
      (logisticPredictor (x i)).hasFDerivAt).const_sub (if y i then 1 else 0)).mul_const
        (x i j))
  convert! h using 1
  ext v
  simp only [logisticPredictor_apply, logisticHessian, sum_apply,
    smul_apply, neg_apply,
    smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem logistic_hessian_quadratic_form {n p : ℕ} (x : Fin n → Fin p → ℝ)
    (β v : Fin p → ℝ) :
    (∑ j, ∑ k, v j * logisticHessian x β j k * v k) =
      ∑ i, -(logistic (logisticPredictor (x i) β) *
        (1 - logistic (logisticPredictor (x i) β))) * (logisticPredictor (x i) v) ^ 2 := by
  simp only [logisticHessian, logisticPredictor_apply, Finset.mul_sum, Finset.sum_mul,
    pow_two]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem logistic_sample_hessian_nonpositive {n p : ℕ} (x : Fin n → Fin p → ℝ)
    (β v : Fin p → ℝ) : (∑ j, ∑ k, v j * logisticHessian x β j k * v k) ≤ 0 := by
  rw [logistic_hessian_quadratic_form]
  simpa only [logisticPredictor_apply] using
    logistic_hessian_nonpositive (fun i => logisticPredictor (x i) β) x v

theorem logistic_logLikelihood_strictConcave (y : Bool) :
    StrictConcaveOn ℝ univ (logisticLogLikelihood y) := by
  apply strictConcaveOn_univ_of_deriv2_neg
  · exact (show Differentiable ℝ (logisticLogLikelihood y) from
      fun t => (hasDerivAt_logisticLogLikelihood y t).differentiableAt).continuous
  · intro t
    change deriv (deriv (logisticLogLikelihood y)) t < 0
    rw [logistic_second_derivative]
    exact neg_neg_of_pos (mul_pos (logistic_mem_Ioo t).1 (sub_pos.mpr (logistic_mem_Ioo t).2))

theorem logistic_sample_concave {n p : ℕ} (y : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) : ConcaveOn ℝ univ (logisticSampleLogLikelihood y x) := by
  refine ⟨convex_univ, ?_⟩
  intro β _ γ _ a b ha hb hab
  simp only [logisticSampleLogLikelihood, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [map_add, map_smul, smul_eq_mul] using
    (logistic_logLikelihood_strictConcave (y i)).concaveOn.2
      (mem_univ _) (mem_univ _) ha hb hab

/-- The tangent to a concave single-observation log likelihood is an upper bound. -/
theorem logistic_logLikelihood_tangent (y : Bool) (s t : ℝ) :
    logisticLogLikelihood y t ≤ logisticLogLikelihood y s +
      ((if y then 1 else 0) - logistic s) * (t - s) := by
  have hc := (logistic_logLikelihood_strictConcave y).concaveOn
  rcases lt_trichotomy s t with h | rfl | h
  · have hh := hc.slope_le_of_hasDerivAt (mem_univ s) (mem_univ t) h
      (hasDerivAt_logisticLogLikelihood y s)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hh
    linarith
  · simp
  · have hh := hc.le_slope_of_hasDerivAt (mem_univ t) (mem_univ s) h
      (hasDerivAt_logisticLogLikelihood y s)
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hh
    nlinarith

theorem logistic_sample_tangent {n p : ℕ} (y : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (β γ : Fin p → ℝ) :
    logisticSampleLogLikelihood y x γ ≤ logisticSampleLogLikelihood y x β +
      logisticPredictor (logisticScore y x β) (γ - β) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    logistic_logLikelihood_tangent (y i) (logisticPredictor (x i) β)
      (logisticPredictor (x i) γ))
  rw [Finset.sum_add_distrib] at h
  convert! h using 1
  congr 1
  simp only [← map_sub]
  simp only [logisticScore, logisticPredictor_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every finite score root is a global maximum, without a rank assumption. -/
theorem logistic_score_root_global_maximum {n p : ℕ} (y : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) (hβ : logisticScore y x β = 0) :
    ∀ γ, logisticSampleLogLikelihood y x γ ≤ logisticSampleLogLikelihood y x β := by
  intro γ
  simpa [hβ, logisticPredictor_apply] using logistic_sample_tangent y x β γ

theorem logistic_global_maximum_iff_score_zero {n p : ℕ} (y : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) :
    (∀ γ, logisticSampleLogLikelihood y x γ ≤ logisticSampleLogLikelihood y x β) ↔
      logisticScore y x β = 0 := by
  constructor
  · intro h
    have hm : IsLocalMax (logisticSampleLogLikelihood y x) β := Filter.Eventually.of_forall h
    have hd := hm.hasFDerivAt_eq_zero (hasFDerivAt_logisticSampleLogLikelihood y x β)
    ext j
    have hj := DFunLike.congr_fun hd (Pi.single j 1)
    simpa [logisticPredictor_apply, Pi.single_apply] using hj
  · exact logistic_score_root_global_maximum y x β

/-- Full column rank is expressed as injectivity of the design map. -/
theorem logistic_sample_strictConcave {n p : ℕ} (y : Fin n → Bool)
    (x : Fin n → Fin p → ℝ)
    (hrank : Function.Injective (fun β : Fin p → ℝ => fun i => logisticPredictor (x i) β)) :
    StrictConcaveOn ℝ univ (logisticSampleLogLikelihood y x) := by
  refine ⟨convex_univ, ?_⟩
  intro β _ γ _ hne a b ha hb hab
  have hi : ∃ i, logisticPredictor (x i) β ≠ logisticPredictor (x i) γ := by
    by_contra h
    push Not at h
    exact hne (hrank (funext h))
  simp only [logisticSampleLogLikelihood, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · intro i _
    simpa only [map_add, map_smul, smul_eq_mul] using
      (logistic_logLikelihood_strictConcave (y i)).concaveOn.2
        (mem_univ _) (mem_univ _) ha.le hb.le hab
  · obtain ⟨i, hi⟩ := hi
    refine ⟨i, Finset.mem_univ _, ?_⟩
    simpa only [map_add, map_smul, smul_eq_mul] using
      (logistic_logLikelihood_strictConcave (y i)).2 (mem_univ _) (mem_univ _) hi ha hb hab

theorem logistic_maximum_unique {n p : ℕ} (y : Fin n → Bool)
    (x : Fin n → Fin p → ℝ)
    (hrank : Function.Injective (fun β : Fin p → ℝ => fun i => logisticPredictor (x i) β))
    {β γ : Fin p → ℝ}
    (hβ : ∀ b, logisticSampleLogLikelihood y x b ≤ logisticSampleLogLikelihood y x β)
    (hγ : ∀ b, logisticSampleLogLikelihood y x b ≤ logisticSampleLogLikelihood y x γ) : β = γ :=
  (logistic_sample_strictConcave y x hrank).eq_of_isMaxOn
    (fun b _ => hβ b) (fun b _ => hγ b) (mem_univ _) (mem_univ _)

theorem logistic_hessian_negative_of_full_rank {n p : ℕ}
    (x : Fin n → Fin p → ℝ)
    (hrank : Function.Injective (fun β : Fin p → ℝ => fun i => logisticPredictor (x i) β))
    (β : Fin p → ℝ) {v : Fin p → ℝ} (hv : v ≠ 0) :
    (∑ j, ∑ k, v j * logisticHessian x β j k * v k) < 0 := by
  rw [logistic_hessian_quadratic_form]
  have hi : ∃ i, logisticPredictor (x i) v ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    apply hrank
    funext i
    simpa using h i
  have hnonpos i : -(logistic (logisticPredictor (x i) β) *
      (1 - logistic (logisticPredictor (x i) β))) * (logisticPredictor (x i) v) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_pos
      (logistic_mem_Ioo _).1 (sub_pos.mpr (logistic_mem_Ioo _).2)).le) (sq_nonneg _)
  have hlt := Finset.sum_lt_sum (s := Finset.univ) (g := fun _ => (0 : ℝ))
    (fun i _ => hnonpos i) (by
      obtain ⟨i, hi⟩ := hi
      refine ⟨i, Finset.mem_univ _, ?_⟩
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos (logistic_mem_Ioo _).1
        (sub_pos.mpr (logistic_mem_Ioo _).2))) (sq_pos_of_ne_zero hi))
  simpa only [Finset.sum_const_zero] using hlt

theorem logistic_conditional_score_mean (t : ℝ) :
    (∑ y : Bool, logisticMass y t * ((if y then 1 else 0) - logistic t)) = 0 := by
  simp only [Fintype.sum_bool, logisticMass, Bool.false_eq_true, ↓reduceIte]
  ring

/-- Conditional Fisher information, with fixed covariates, agrees with the
negative Hessian for a single observation. -/
theorem logistic_conditional_information {p : ℕ} (x β : Fin p → ℝ) (j k : Fin p) :
    (∑ y : Bool, logisticMass y (logisticPredictor x β) *
      (((if y then 1 else 0) - logistic (logisticPredictor x β)) * x j) *
      (((if y then 1 else 0) - logistic (logisticPredictor x β)) * x k)) =
    logistic (logisticPredictor x β) * (1 - logistic (logisticPredictor x β)) * x j * x k := by
  simp only [Fintype.sum_bool, logisticMass, Bool.false_eq_true, ↓reduceIte]
  ring

theorem logistic_success_logLikelihood_strictMono : StrictMono (logisticLogLikelihood true) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(hasDerivAt_logisticLogLikelihood true t).deriv]
  simpa using sub_pos.mpr (logistic_mem_Ioo t).2

theorem logistic_failure_logLikelihood_strictAnti : StrictAnti (logisticLogLikelihood false) := by
  apply strictAnti_of_deriv_neg
  intro t
  rw [(hasDerivAt_logisticLogLikelihood false t).deriv]
  simpa using neg_neg_of_pos (logistic_mem_Ioo t).1

/-- Complete separation provides a direction which strictly improves every
finite parameter, so a finite maximum need not exist even for a concave model. -/
theorem logistic_separation_no_maximum {n p : ℕ} (hn : 0 < n) (y : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (v : Fin p → ℝ)
    (hsep : ∀ i, if y i then 0 < logisticPredictor (x i) v else logisticPredictor (x i) v < 0) :
    ¬ ∃ β, ∀ γ, logisticSampleLogLikelihood y x γ ≤ logisticSampleLogLikelihood y x β := by
  rintro ⟨β, hβ⟩
  have hinc (i : Fin n) :
      logisticLogLikelihood (y i) (logisticPredictor (x i) β) <
        logisticLogLikelihood (y i) (logisticPredictor (x i) (β + v)) := by
    rw [map_add]
    have hs := hsep i
    cases hy : y i <;> simp only [hy, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    · exact logistic_failure_logLikelihood_strictAnti (by linarith)
    · exact logistic_success_logLikelihood_strictMono (by linarith)
  have hlt : logisticSampleLogLikelihood y x β < logisticSampleLogLikelihood y x (β + v) :=
    Finset.sum_lt_sum (fun i _ => (hinc i).le) ⟨⟨0, hn⟩, Finset.mem_univ _, hinc _⟩
  exact (not_lt_of_ge (hβ (β + v))) hlt

end LectureNotes
