import LectureNotes.BernoulliModel
import LectureNotes.LikelihoodRatio
import LectureNotes.DKWAnalytic

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open Set
open scoped BigOperators

/-- Ordered Bernoulli-sample likelihood, expressed in success and failure counts. -/
def bernoulliCountLikelihood (s f : ℕ) (p : ℝ) : ℝ := p ^ s * (1 - p) ^ f

def bernoulliCountMLE (s f : ℕ) : ℝ := (s : ℝ) / ((s : ℝ) + f)

def bernoulliSuccessCount {n : ℕ} (x : Fin n → Fin 2) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0).card

def bernoulliFailureCount {n : ℕ} (x : Fin n → Fin 2) : ℕ :=
  (Finset.univ.filter fun i => x i = 0).card

theorem bernoulli_counts_sum {n : ℕ} (x : Fin n → Fin 2) :
    bernoulliSuccessCount x + bernoulliFailureCount x = n := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => x i = 0)
  simpa [bernoulliSuccessCount, bernoulliFailureCount, add_comm] using h

theorem bernoulli_product_likelihood {n : ℕ} (x : Fin n → Fin 2) (p : ℝ) :
    (∏ i, bernoulliMass p (x i)) =
      bernoulliCountLikelihood (bernoulliSuccessCount x) (bernoulliFailureCount x) p := by
  simp only [bernoulliMass, Finset.prod_ite, Finset.prod_const]
  exact mul_comm _ _

theorem bernoulliCountMLE_mem {s f : ℕ} (hn : 0 < s + f) :
    bernoulliCountMLE s f ∈ Icc (0 : ℝ) 1 := by
  have ht : 0 < (s : ℝ) + f := by exact_mod_cast hn
  exact ⟨div_nonneg (Nat.cast_nonneg s) ht.le,
    (div_le_one ht).mpr (by linarith [Nat.cast_nonneg (α := ℝ) f])⟩

theorem bernoulliCountMLE_likelihood_pos {s f : ℕ} (hn : 0 < s + f) :
    0 < bernoulliCountLikelihood s f (bernoulliCountMLE s f) := by
  by_cases hs : s = 0
  · subst s
    simp [bernoulliCountLikelihood, bernoulliCountMLE]
  by_cases hf : f = 0
  · subst f
    simp [bernoulliCountLikelihood, bernoulliCountMLE, hs]
  have hsR : 0 < (s : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hfR : 0 < (f : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hf
  have hm : 0 < bernoulliCountMLE s f := div_pos hsR (by positivity)
  have hm1 : bernoulliCountMLE s f < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  exact mul_pos (pow_pos hm _) (pow_pos (sub_pos.mpr hm1) _)

theorem bernoulliCountLikelihood_pos {s f : ℕ} {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 < bernoulliCountLikelihood s f p :=
  mul_pos (pow_pos hp.1 s) (pow_pos (sub_pos.mpr hp.2) f)

theorem bernoulliCountLikelihood_log {s f : ℕ} {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.log (bernoulliCountLikelihood s f p) =
      s * Real.log p + f * Real.log (1 - p) := by
  rw [bernoulliCountLikelihood, Real.log_mul (pow_pos hp.1 s).ne'
    (pow_pos (sub_pos.mpr hp.2) f).ne', Real.log_pow, Real.log_pow]

theorem bernoulliCountMLE_log {s f : ℕ} (hn : 0 < s + f) :
    Real.log (bernoulliCountLikelihood s f (bernoulliCountMLE s f)) =
      s * Real.log (bernoulliCountMLE s f) + f * Real.log (1 - bernoulliCountMLE s f) := by
  by_cases hs : s = 0
  · subst s
    simp [bernoulliCountLikelihood, bernoulliCountMLE]
  by_cases hf : f = 0
  · subst f
    simp [bernoulliCountLikelihood, bernoulliCountMLE, hs]
  have hsR : 0 < (s : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hfR : 0 < (f : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hf
  exact bernoulliCountLikelihood_log ⟨div_pos hsR (by positivity),
    (div_lt_one (by positivity)).mpr (by linarith)⟩

/-- The log-likelihood loss is the sample size times the actual Bernoulli
relative entropy, including all-zero and all-one samples. -/
theorem bernoulli_log_likelihood_loss {s f : ℕ} (hn : 0 < s + f)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.log (bernoulliCountLikelihood s f (bernoulliCountMLE s f)) -
      Real.log (bernoulliCountLikelihood s f p) =
      ((s : ℝ) + f) * bernoulliDivergence (bernoulliCountMLE s f) p := by
  rw [bernoulliCountMLE_log hn, bernoulliCountLikelihood_log hp]
  have ht : (s : ℝ) + f ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hs : ((s : ℝ) + f) * bernoulliCountMLE s f = s := by
    unfold bernoulliCountMLE
    field_simp
  have hf : ((s : ℝ) + f) * (1 - bernoulliCountMLE s f) = f := by nlinarith [hs]
  unfold bernoulliDivergence
  calc
    _ = (((s : ℝ) + f) * bernoulliCountMLE s f) * Real.log (bernoulliCountMLE s f) +
        (((s : ℝ) + f) * (1 - bernoulliCountMLE s f)) * Real.log (1 - bernoulliCountMLE s f) -
        (((s : ℝ) + f) * bernoulliCountMLE s f) * Real.log p -
        (((s : ℝ) + f) * (1 - bernoulliCountMLE s f)) * Real.log (1 - p) := by rw [hs, hf]; ring
    _ = _ := by ring

/-- The empirical proportion maximizes the genuine Bernoulli likelihood on
its closed parameter extension. In the open model the boundary cases give a supremum. -/
theorem bernoulliCountMLE_maximizes {s f : ℕ} (hn : 0 < s + f)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    bernoulliCountLikelihood s f p ≤ bernoulliCountLikelihood s f (bernoulliCountMLE s f) := by
  have hi : ∀ p ∈ Ioo (0 : ℝ) 1, bernoulliCountLikelihood s f p ≤
      bernoulliCountLikelihood s f (bernoulliCountMLE s f) := by
    intro p hp
    have hd := bernoulliDivergence_pinsker (bernoulliCountMLE_mem hn) hp
    have ht : 0 ≤ (s : ℝ) + f := by positivity
    have hh := mul_nonneg ht (le_trans (by positivity) hd)
    rw [← bernoulli_log_likelihood_loss hn hp] at hh
    exact (Real.log_le_log_iff
      (bernoulliCountLikelihood_pos hp)
      (bernoulliCountMLE_likelihood_pos hn)).mp (sub_nonneg.mp hh)
  have hc : IsClosed {p : ℝ | bernoulliCountLikelihood s f p ≤
      bernoulliCountLikelihood s f (bernoulliCountMLE s f)} :=
    isClosed_le (by unfold bernoulliCountLikelihood; fun_prop) continuous_const
  have he := closure_minimal hi hc
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at he
  exact he hp

/-- Maximizing over the open model gives the same denominator, also when the
empirical proportion is at a boundary and no interior maximizer exists. -/
theorem bernoulli_open_likelihood_sup {s f : ℕ} (hn : 0 < s + f) :
    sSup (bernoulliCountLikelihood s f '' Ioo (0 : ℝ) 1) =
      bernoulliCountLikelihood s f (bernoulliCountMLE s f) := by
  have hne : (bernoulliCountLikelihood s f '' Ioo (0 : ℝ) 1).Nonempty :=
    ⟨_, mem_image_of_mem _ (show (1 / 2 : ℝ) ∈ Ioo 0 1 by constructor <;> norm_num)⟩
  have hb : BddAbove (bernoulliCountLikelihood s f '' Ioo (0 : ℝ) 1) :=
    ⟨_, by rintro _ ⟨p, hp, rfl⟩; exact bernoulliCountMLE_maximizes hn ⟨hp.1.le, hp.2.le⟩⟩
  apply le_antisymm
  · apply csSup_le hne
    rintro _ ⟨p, hp, rfl⟩
    exact bernoulliCountMLE_maximizes hn ⟨hp.1.le, hp.2.le⟩
  · have hc : IsClosed {p : ℝ | bernoulliCountLikelihood s f p ≤
        sSup (bernoulliCountLikelihood s f '' Ioo (0 : ℝ) 1)} :=
      isClosed_le (by unfold bernoulliCountLikelihood; fun_prop) continuous_const
    have hi : Ioo (0 : ℝ) 1 ⊆ {p : ℝ | bernoulliCountLikelihood s f p ≤
        sSup (bernoulliCountLikelihood s f '' Ioo (0 : ℝ) 1)} :=
      fun p hp => le_csSup hb (mem_image_of_mem _ hp)
    have hh := closure_minimal hi hc
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hh
    exact hh (bernoulliCountMLE_mem hn)

/-- The actual supremum likelihood ratio on the source's open parameter space. -/
theorem bernoulli_likelihoodRatio {s f : ℕ} (hn : 0 < s + f)
    (p : Ioo (0 : ℝ) 1) :
    likelihoodRatio (fun (_ : Unit) (q : Ioo (0 : ℝ) 1) => bernoulliCountLikelihood s f q)
      {p} () = bernoulliCountLikelihood s f p /
        bernoulliCountLikelihood s f (bernoulliCountMLE s f) := by
  unfold likelihoodRatio
  rw [Set.image_singleton, csSup_singleton]
  have he : Set.range (fun q : Ioo (0 : ℝ) 1 => bernoulliCountLikelihood s f q) =
      bernoulliCountLikelihood s f '' Ioo (0 : ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q, q.property, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  rw [he, bernoulli_open_likelihood_sup hn]

/-- L11's nonlinear LR statistic, derived from the likelihood supremum.
The zero-count convention handles the two degenerate empirical samples. -/
theorem bernoulli_minus_two_log_likelihoodRatio {s f : ℕ} (hn : 0 < s + f)
    (p : Ioo (0 : ℝ) 1) :
    -2 * Real.log (likelihoodRatio
      (fun (_ : Unit) (q : Ioo (0 : ℝ) 1) => bernoulliCountLikelihood s f q) {p} ()) =
      2 * (s * Real.log (bernoulliCountMLE s f / p) +
        f * Real.log ((1 - bernoulliCountMLE s f) / (1 - p))) := by
  rw [bernoulli_likelihoodRatio hn, minus_two_log_ratio _ _
    (bernoulliCountLikelihood_pos p.property)
    (bernoulliCountMLE_likelihood_pos hn), bernoulliCountMLE_log hn,
    bernoulliCountLikelihood_log p.property]
  have hs : (s : ℝ) * Real.log (bernoulliCountMLE s f / p) =
      s * (Real.log (bernoulliCountMLE s f) - Real.log p) := by
    by_cases hs : s = 0
    · simp [hs]
    have ht : 0 < (s : ℝ) + f := by exact_mod_cast hn
    have hm : 0 < bernoulliCountMLE s f := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hs) ht
    rw [Real.log_div hm.ne' p.property.1.ne']
  have hf : (f : ℝ) * Real.log ((1 - bernoulliCountMLE s f) / (1 - p)) =
      f * (Real.log (1 - bernoulliCountMLE s f) - Real.log (1 - p)) := by
    by_cases hf : f = 0
    · simp [hf]
    have ht : 0 < (s : ℝ) + f := by exact_mod_cast hn
    have hfR : 0 < (f : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hf
    have hm : bernoulliCountMLE s f < 1 := (div_lt_one ht).mpr (by linarith)
    rw [Real.log_div (sub_pos.mpr hm).ne' (sub_pos.mpr p.property.2).ne']
  rw [hs, hf]
  ring

/-- Inverting the genuine likelihood-ratio test is exactly the source's
nonlinear inequality. No finite-sample chi-square calibration is asserted. -/
theorem bernoulli_LR_confidence_set {s f : ℕ} (hn : 0 < s + f) (c : ℝ) :
    {p : Ioo (0 : ℝ) 1 | -2 * Real.log (likelihoodRatio
      (fun (_ : Unit) (q : Ioo (0 : ℝ) 1) => bernoulliCountLikelihood s f q) {p} ()) ≤ c} =
    {p : Ioo (0 : ℝ) 1 | 2 * (s * Real.log (bernoulliCountMLE s f / p) +
      f * Real.log ((1 - bernoulliCountMLE s f) / (1 - p))) ≤ c} := by
  ext p
  simp only [mem_ofPred_eq, bernoulli_minus_two_log_likelihoodRatio hn]

/-- The success count agrees with the sum of the binary observations. -/
theorem bernoulliSuccessCount_eq_sum {n : ℕ} (x : Fin n → Fin 2) :
    bernoulliSuccessCount x = ∑ i, (x i).val := by
  simp only [bernoulliSuccessCount, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  generalize x i = b
  fin_cases b <;> decide

/-- The source's nonlinear statistic is the LR statistic of the product of
Bernoulli masses for the actual ordered sample. -/
theorem bernoulli_product_LR_statistic {n : ℕ} (hn : 0 < n)
    (x : Fin n → Fin 2) (p : Ioo (0 : ℝ) 1) :
    -2 * Real.log (likelihoodRatio
      (fun (y : Fin n → Fin 2) (q : Ioo (0 : ℝ) 1) => ∏ i, bernoulliMass q (y i)) {p} x) =
      2 * (bernoulliSuccessCount x *
          Real.log (bernoulliCountMLE (bernoulliSuccessCount x) (bernoulliFailureCount x) / p) +
        bernoulliFailureCount x * Real.log
          ((1 - bernoulliCountMLE (bernoulliSuccessCount x) (bernoulliFailureCount x)) / (1 - p))) := by
  have hc : 0 < bernoulliSuccessCount x + bernoulliFailureCount x := by
    rwa [bernoulli_counts_sum]
  have hh := bernoulli_minus_two_log_likelihoodRatio hc p
  unfold likelihoodRatio at hh ⊢
  simpa only [bernoulli_product_likelihood] using hh

end LectureNotes
