import LectureNotes.BinomialConditioning
import Mathlib.Data.Nat.Choose.Cast

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The estimand in L5 Example 19. -/
def binomialOneSuccessProbability (k : ℕ) (p : Icc (0 : ℝ) 1) : ℝ :=
  k * (p : ℝ) * (1 - (p : ℝ)) ^ (k - 1)

theorem binomialCountLaw_one_success (k : ℕ) (p : Icc (0 : ℝ) 1) :
    (binomialCountLaw k p).real {j | (j : ℕ) = 1} = binomialOneSuccessProbability k p := by
  by_cases hk : 0 < k
  · let j₁ : Fin (k + 1) := ⟨1, by omega⟩
    have he : {j : Fin (k + 1) | (j : ℕ) = 1} = {j₁} := by
      ext j
      simp [j₁, Fin.ext_iff]
    rw [he, measureReal_def, binomialCountLaw_singleton,
      ENNReal.toReal_ofReal (binomialCountMass_nonneg k p j₁)]
    simp [binomialCountMass, j₁, binomialOneSuccessProbability]
  · have hk0 : k = 0 := by omega
    subst k
    have he : {j : Fin 1 | (j : ℕ) = 1} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hh := j.isLt
      change (j : ℕ) = 1 at hj
      omega
    rw [he, measureReal_empty]
    simp [binomialOneSuccessProbability]

/-- The observed fraction of one-success blocks is unbiased. -/
theorem binomial_oneSuccessAverage_unbiased {k n : ℕ} (hn : 0 < n)
    (p : Icc (0 : ℝ) 1) :
    Unbiased (binomialSampleLaw k n p) binomialOneSuccessAverage (binomialOneSuccessProbability k p) := by
  refine ⟨Integrable.of_finite, ?_⟩
  unfold binomialOneSuccessAverage
  rw [integral_div, integral_finsetSum Finset.univ (fun i _ => Integrable.of_finite)]
  have hi (i : Fin n) : (∫ x : Fin n → Fin (k + 1),
      (if (x i : ℕ) = 1 then (1 : ℝ) else 0) ∂binomialSampleLaw k n p) =
      binomialOneSuccessProbability k p := by
    have hm := measurePreserving_eval (fun _ : Fin n => binomialCountLaw k p) i
    have he : (∫ j : Fin (k + 1), (if (j : ℕ) = 1 then (1 : ℝ) else 0) ∂binomialCountLaw k p) =
        (∫ x : Fin n → Fin (k + 1), (if (x i : ℕ) = 1 then (1 : ℝ) else 0) ∂binomialSampleLaw k n p) := by
      rw [← hm.map_eq, integral_map hm.measurable.aemeasurable
        (show AEStronglyMeasurable (fun j : Fin (k + 1) => if (j : ℕ) = 1 then (1 : ℝ) else 0)
          ((Measure.pi (fun _ : Fin n => binomialCountLaw k p)).map (Function.eval i)) from
          (measurable_of_finite _).aestronglyMeasurable)]
      rfl
    rw [← he]
    rw [show (fun j : Fin (k + 1) => if (j : ℕ) = 1 then (1 : ℝ) else 0) =
      {j : Fin (k + 1) | (j : ℕ) = 1}.indicator (fun _ => (1 : ℝ)) from by ext y; simp [Set.indicator_apply],
      integral_indicator_const _ MeasurableSet.of_discrete, smul_eq_mul, mul_one]
    exact binomialCountLaw_one_success k p
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne')

/-- The displayed, parameter-free Rao–Blackwell estimator is unbiased and
has no larger MSE or variance for any p in the closed parameter interval. -/
theorem binomial_raoBlackwell_unbiased_and_risk {k n : ℕ} (hn : 0 < n)
    (p : Icc (0 : ℝ) 1) :
    Unbiased (binomialSampleLaw k n p)
      (fun x => binomialRaoBlackwell k n (binomialSampleTotal x)) (binomialOneSuccessProbability k p) ∧
    mse (binomialSampleLaw k n p)
      (fun x => binomialRaoBlackwell k n (binomialSampleTotal x)) (binomialOneSuccessProbability k p) ≤
      mse (binomialSampleLaw k n p) binomialOneSuccessAverage (binomialOneSuccessProbability k p) ∧
    Var[fun x => binomialRaoBlackwell k n (binomialSampleTotal x); binomialSampleLaw k n p] ≤
      Var[binomialOneSuccessAverage; binomialSampleLaw k n p] := by
  let P := binomialSampleLaw k n p
  let T := binomialSampleTotal (k := k) (n := n)
  let U := binomialOneSuccessAverage (k := k) (n := n)
  let G (x : Fin n → Fin (k + 1)) := binomialRaoBlackwell k n (T x)
  let θ := binomialOneSuccessProbability k p
  have hT : Measurable T := measurable_of_finite _
  have hc : P[U | (inferInstance : MeasurableSpace ℕ).comap T] =ᵐ[P] G :=
    binomial_raoBlackwell_condExp hn p
  have hU : Unbiased P U θ := binomial_oneSuccessAverage_unbiased hn p
  have hG : Unbiased P G θ := ⟨Integrable.of_finite,
    (integral_congr_ae hc.symm).trans ((integral_condExp hT.comap_le).trans hU.2)⟩
  have hULp : MemLp U 2 P := MemLp.of_discrete
  have hGLp : MemLp G 2 P := MemLp.of_discrete
  have hr : mse P G θ ≤ mse P U θ := by
    calc
      _ = mse P (P[U | (inferInstance : MeasurableSpace ℕ).comap T]) θ := by
        apply integral_congr_ae
        filter_upwards [hc] with x hx
        rw [hx]
      _ ≤ _ := rao_blackwell_mse P hT.comap_le hULp θ
  refine ⟨hG, hr, ?_⟩
  rw [mse_eq_variance_add_bias_sq P hGLp, mse_eq_variance_add_bias_sq P hULp] at hr
  simpa [bias, hG.2, hU.2] using hr

/-- Outside the feasible one-success range, the Rao–Blackwell estimator is
zero. This includes the upper boundary when k>1. -/
theorem binomialRaoBlackwell_zero_of_outside {k n t : ℕ}
    (h : t = 0 ∨ k * (n - 1) + 1 < t) : binomialRaoBlackwell k n t = 0 := by
  rcases h with rfl | ht
  · simp [binomialRaoBlackwell]
  · have hc : (k * (n - 1)).choose (t - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [binomialRaoBlackwell, hc]

/-- The notes' factorial expression agrees with the binomial-coefficient
formula on the stated feasible positive-total range. -/
theorem binomialRaoBlackwell_factorial {k n t : ℕ} (hk : 0 < k) (hn : 0 < n)
    (ht : 1 ≤ t) (htop : t ≤ k * (n - 1) + 1) :
    binomialRaoBlackwell k n t =
      ((k : ℝ) * (k * (n - 1)).factorial * (k * n - t).factorial * t) /
        ((k * n).factorial * (k * n - k + 1 - t).factorial) := by
  have hdecomp : k * n = k * (n - 1) + k := by
    have hnn : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hnn]
    ring
  have htkn : t ≤ k * n := by omega
  have htt : t - 1 ≤ k * (n - 1) := by omega
  have he : k * (n - 1) - (t - 1) = k * n - k + 1 - t := by omega
  have hfac : (t.factorial : ℝ) = (t : ℝ) * ((t - 1).factorial : ℝ) := by
    have htt' : t = (t - 1) + 1 := by omega
    conv_lhs => rw [htt', Nat.factorial_succ]
    push_cast
    congr 1
    exact_mod_cast (Nat.sub_add_cancel ht)
  rw [binomialRaoBlackwell, if_neg (by omega), Nat.cast_choose ℝ htt,
    Nat.cast_choose ℝ htkn, he, hfac]
  field_simp [Nat.cast_ne_zero.mpr (by omega : t ≠ 0),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k * n)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (t - 1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k * n - t)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k * n - k + 1 - t))]

end LectureNotes
