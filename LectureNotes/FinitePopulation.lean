import LectureNotes.SamplingMoments

/-! L2 finite populations. Simple random sampling is the uniform probability
measure on all subsets of the prescribed size. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

def simpleRandomSampling {N n : ℕ} (hn : n ≤ N) : Measure (Finset (Fin N)) :=
  (PMF.uniformOfFinset (univ.powersetCard n)
    (powersetCard_nonempty.mpr (by simpa using hn))).toMeasure

instance {N n : ℕ} (hn : n ≤ N) : IsProbabilityMeasure (simpleRandomSampling hn) := by
  unfold simpleRandomSampling
  infer_instance

def selectionIndicator {N : ℕ} (i : Fin N) (s : Finset (Fin N)) : ℝ :=
  if i ∈ s then 1 else 0

theorem simpleRandomSampling_contains {N n : ℕ} (hn : n ≤ N)
    (s : Finset (Fin N)) (hs : s.card ≤ n) :
    (simpleRandomSampling hn).real {t | s ⊆ t} =
      ((N - s.card).choose (n - s.card) : ℝ) / N.choose n := by
  rw [measureReal_def, simpleRandomSampling, PMF.toMeasure_uniformOfFinset_apply]
  · simp only [Set.mem_setOf_eq, card_filter_powersetCard_subset s univ n
        (subset_univ s) hs, card_powersetCard, card_univ, Fintype.card_fin,
      ENNReal.toReal_div, ENNReal.toReal_natCast]
  · exact Set.to_countable _ |>.measurableSet

theorem choose_predecessor_ratio {N n : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    ((N - 1).choose (n - 1) : ℝ) / N.choose n = (n : ℝ) / N := by
  have hN0 : 0 < N := hn.trans_le hN
  have hc : (N.choose n : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hN).ne'
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
  have he := Nat.add_one_mul_choose_eq (N - 1) (n - 1)
  rw [Nat.sub_add_cancel hN0, Nat.sub_add_cancel hn] at he
  have her : (N : ℝ) * (N - 1).choose (n - 1) = (N.choose n : ℝ) * n :=
    by exact_mod_cast he
  field_simp
  nlinarith

theorem simpleRandomSampling_inclusion {N n : ℕ} (hn : 0 < n) (hN : n ≤ N)
    (i : Fin N) :
    (simpleRandomSampling hN).real {s | i ∈ s} = (n : ℝ) / N := by
  have h := simpleRandomSampling_contains hN {i} (by simp; omega)
  simpa only [singleton_subset_iff, card_singleton, choose_predecessor_ratio hn hN] using h

theorem simpleRandomSampling_pair_inclusion {N n : ℕ} (hn : 1 < n) (hN : n ≤ N)
    (i j : Fin N) (hij : i ≠ j) :
    (simpleRandomSampling hN).real {s | i ∈ s ∧ j ∈ s} =
      (n : ℝ) * (n - 1) / (N * (N - 1)) := by
  have h := simpleRandomSampling_contains hN {i, j} (by simp [hij]; omega)
  simp only [insert_subset_iff, singleton_subset_iff, mem_singleton, hij,
    not_false_eq_true, card_insert_of_notMem, card_singleton] at h
  rw [h]
  have hn0 : 0 < n := by omega
  have hN0 : 0 < N := by omega
  have hr1 := choose_predecessor_ratio hn0 hN
  have hr2 := choose_predecessor_ratio (N := N - 1) (n := n - 1) (by omega) (by omega)
  have hc : (N.choose n : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hN).ne'
  have hc1 : ((N - 1).choose (n - 1) : ℝ) ≠ 0 :=
    by exact_mod_cast (Nat.choose_pos (show n - 1 ≤ N - 1 by omega)).ne'
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hNm : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < N := by exact_mod_cast hn.trans_le hN
    linarith
  simp only [Nat.sub_sub, Nat.cast_sub (show 1 ≤ n by omega),
    Nat.cast_sub (show 1 ≤ N by omega), Nat.cast_one] at hr2
  rw [div_eq_iff hc] at hr1
  rw [div_eq_iff hc1] at hr2
  rw [hr2, hr1]
  field_simp
  <;> ring

def designMean {N : ℕ} {Ω : Type*} (n : ℕ) (x : Fin N → ℝ)
    (R : Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, R i ω * x i

theorem designMean_expectation {N n : ℕ} (hn : 0 < n) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (x : Fin N → ℝ) {R : Fin N → Ω → ℝ}
    (hR : ∀ i, Integrable (R i) P) (hmean : ∀ i, P[R i] = (n : ℝ) / N) :
    P[designMean n x R] = sampleMean x := by
  unfold designMean sampleMean
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hR i).mul_const _)]
  simp only [integral_mul_const, hmean, Fintype.card_fin, ← mul_sum]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- Moment calculation for a fixed-size sampling design, isolated from the
combinatorial proof of its inclusion probabilities. -/
theorem designMean_variance {N n : ℕ} (hn : 0 < n) (hN : 1 < N) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (x : Fin N → ℝ) {R : Fin N → Ω → ℝ} (hR : ∀ i, MemLp (R i) 2 P)
    (hmean : ∀ i, P[R i] = (n : ℝ) / N)
    (hpair : ∀ i j, (∫ ω, R i ω * R j ω ∂P) =
      if i = j then (n : ℝ) / N else (n : ℝ) * (n - 1) / (N * (N - 1))) :
    Var[designMean n x R; P] = (1 - (n : ℝ) / N) * sampleVariance x / n := by
  classical
  let p : ℝ := (n : ℝ) / N
  let q : ℝ := (n : ℝ) * (n - 1) / (N * (N - 1))
  have hc (i j) : cov[R i, R j; P] =
      (p - q) * (if i = j then 1 else 0) + (q - p ^ 2) := by
    rw [covariance_eq_sub (hR i) (hR j)]
    simp only [Pi.mul_apply, hpair, hmean]
    change (if i = j then p else q) - p * p = _
    split <;> ring
  have hs : (∑ i, ∑ j, cov[R i, R j; P] * x i * x j) =
      (p - q) * ∑ i, x i ^ 2 + (q - p ^ 2) * (∑ i, x i) ^ 2 := by
    have hd (i) : (∑ j, (if i = j then 1 else (0 : ℝ)) * x i * x j) = x i ^ 2 := by
      rw [sum_eq_single i]
      · simp [pow_two]
      · intro j _ hji
        simp [Ne.symm hji]
      · simp
    have he (i j) : cov[R i, R j; P] * x i * x j =
        (p - q) * ((if i = j then 1 else 0) * x i * x j) +
          (q - p ^ 2) * x i * x j := by rw [hc]; ring
    simp only [he, sum_add_distrib, ← mul_sum, hd, ← sum_mul, pow_two]
    ring
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hN' : (N : ℝ) ≠ 0 := by
    have : 0 < N := by omega
    positivity
  have hNm : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < N := by exact_mod_cast hN
    linarith
  letI : NeZero N := ⟨by omega⟩
  have hx := sum_centered_sq_sampleMean x
  simp only [Fintype.card_fin] at hx
  unfold designMean
  rw [variance_const_mul, variance_fun_sum (fun i => (hR i).mul_const _)]
  simp_rw [covariance_mul_const_left, covariance_mul_const_right]
  have hreorder : (∑ i, ∑ j, cov[R i, R j; P] * x j * x i) =
      ∑ i, ∑ j, cov[R i, R j; P] * x i * x j := by
    congr 1; funext i; congr 1; funext j; ring
  rw [hreorder, hs]
  rw [sampleVariance, hx]
  simp only [sampleMean, Fintype.card_fin, p, q]
  field_simp
  <;> ring

theorem selectionIndicator_memLp {N : ℕ} (i : Fin N) (P : Measure (Finset (Fin N)))
    [IsProbabilityMeasure P] : MemLp (selectionIndicator i) 2 P := MemLp.of_discrete

theorem selectionIndicator_expectation {N : ℕ} (i : Fin N)
    (P : Measure (Finset (Fin N))) [IsProbabilityMeasure P] :
    P[selectionIndicator i] = P.real {s | i ∈ s} := by
  have he : selectionIndicator i = Set.indicator {s | i ∈ s} (fun _ => (1 : ℝ)) := by
    funext s
    simp [selectionIndicator, Set.indicator]
  rw [he]
  rw [integral_indicator (Set.to_countable _ |>.measurableSet)]
  simp

theorem selectionIndicator_product_expectation {N : ℕ} (i j : Fin N)
    (P : Measure (Finset (Fin N))) [IsProbabilityMeasure P] :
    (∫ s, selectionIndicator i s * selectionIndicator j s ∂P) =
      P.real {s | i ∈ s ∧ j ∈ s} := by
  have he (s : Finset (Fin N)) : selectionIndicator i s * selectionIndicator j s =
      Set.indicator {s | i ∈ s ∧ j ∈ s} (fun _ => (1 : ℝ)) s := by
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;>
      simp [selectionIndicator, Set.indicator, hi, hj]
  simp only [he]
  rw [integral_indicator (Set.to_countable _ |>.measurableSet)]
  simp

/-- L2 Theorem 2: unbiasedness under the actual uniform subset design. -/
theorem simpleRandomSampling_mean {N n : ℕ} (hn : 0 < n) (hN : n ≤ N)
    (x : Fin N → ℝ) :
    (simpleRandomSampling hN)[designMean n x selectionIndicator] = sampleMean x := by
  apply designMean_expectation hn x
  · exact fun i => (selectionIndicator_memLp i _).integrable (by norm_num)
  · intro i
    rw [selectionIndicator_expectation, simpleRandomSampling_inclusion hn hN]

theorem simpleRandomSampling_pair_single_draw {N : ℕ} (hN : 1 ≤ N)
    (i j : Fin N) (hij : i ≠ j) :
    (simpleRandomSampling hN).real {s | i ∈ s ∧ j ∈ s} = 0 := by
  classical
  have hempty : (univ.powersetCard 1).filter (fun s : Finset (Fin N) => i ∈ s ∧ j ∈ s) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨hs, hi, hj⟩ := mem_filter.mp hs
    have hcard := (mem_powersetCard.mp hs).2
    have hp : ({i, j} : Finset (Fin N)) ⊆ s := insert_subset hi (singleton_subset_iff.mpr hj)
    have := card_le_card hp
    simp [hij, hcard] at this
  rw [measureReal_def, simpleRandomSampling, PMF.toMeasure_uniformOfFinset_apply]
  · simp [hempty]
  · exact Set.to_countable _ |>.measurableSet

/-- L2 Theorem 2: finite population correction, including a single draw.
The population has at least two units so its unbiased variance is defined. -/
theorem simpleRandomSampling_variance {N n : ℕ} (hn : 0 < n) (hN : n ≤ N)
    (hN2 : 1 < N)
    (x : Fin N → ℝ) :
    Var[designMean n x selectionIndicator; simpleRandomSampling hN] =
      (1 - (n : ℝ) / N) * sampleVariance x / n := by
  apply designMean_variance (by omega) (by omega) x
  · exact fun i => selectionIndicator_memLp i _
  · intro i
    rw [selectionIndicator_expectation, simpleRandomSampling_inclusion (by omega) hN]
  · intro i j
    rw [selectionIndicator_product_expectation]
    split_ifs with hij
    · subst j
      simpa only [and_self] using simpleRandomSampling_inclusion (by omega) hN i
    · by_cases hn2 : 1 < n
      · exact simpleRandomSampling_pair_inclusion hn2 hN i j hij
      · have hn1 : n = 1 := by omega
        subst n
        rw [simpleRandomSampling_pair_single_draw hN i j hij]
        norm_num
end LectureNotes
