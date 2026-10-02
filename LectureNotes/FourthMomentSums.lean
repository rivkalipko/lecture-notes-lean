import LectureNotes.SamplingMoments
import LectureNotes.InstrumentalVariables
import Mathlib.Probability.Independence.Integration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem memLp_four_integrable_pow {X : Ω → ℝ} (hX : MemLp X 4 P)
    {k : ℕ} (hk : k ≤ 4) : Integrable (fun ω => X ω ^ k) P := by
  have hkE : (k : ℝ≥0∞) ≤ 4 := by exact_mod_cast hk
  have hi := (hX.mono_exponent hkE).integrable_norm_pow' (p := k)
  apply (integrable_norm_iff (hX.aestronglyMeasurable.pow k)).mp
  simpa only [Pi.pow_apply, norm_pow] using hi

/-- Independence and centering remove both odd cross terms in the fourth
moment expansion. Finite fourth moments justify every integral operation. -/
theorem independent_centered_fourth_moment_add {X Y : Ω → ℝ}
    (hX : MemLp X 4 P) (hY : MemLp Y 4 P) (hi : IndepFun X Y P)
    (hmX : P[X] = 0) (hmY : P[Y] = 0) :
    (∫ ω, (X ω + Y ω) ^ 4 ∂P) = (∫ ω, X ω ^ 4 ∂P) +
      6 * (∫ ω, X ω ^ 2 ∂P) * (∫ ω, Y ω ^ 2 ∂P) + (∫ ω, Y ω ^ 4 ∂P) := by
  have hx k (hk : k ≤ 4) := memLp_four_integrable_pow hX hk
  have hy k (hk : k ≤ 4) := memLp_four_integrable_pow hY hk
  have hind (p q : ℕ) : IndepFun (fun ω => X ω ^ p) (fun ω => Y ω ^ q) P :=
    hi.comp (by fun_prop : Measurable (fun x : ℝ => x ^ p))
      (by fun_prop : Measurable (fun y : ℝ => y ^ q))
  have hint p q (hp : p ≤ 4) (hq : q ≤ 4) : Integrable (fun ω => X ω ^ p * Y ω ^ q) P :=
    (hind p q).integrable_mul (hx p hp) (hy q hq)
  have he (ω : Ω) : (X ω + Y ω) ^ 4 = X ω ^ 4 +
      4 * (X ω ^ 3 * Y ω ^ 1) + 6 * (X ω ^ 2 * Y ω ^ 2) +
      4 * (X ω ^ 1 * Y ω ^ 3) + Y ω ^ 4 := by ring
  simp_rw [he]
  have hsum1 : Integrable (fun ω => X ω ^ 4 + 4 * (X ω ^ 3 * Y ω ^ 1)) P :=
    (hx 4 le_rfl).add ((hint 3 1 (by omega) (by omega)).const_mul 4)
  have hsum2 : Integrable (fun ω => X ω ^ 4 + 4 * (X ω ^ 3 * Y ω ^ 1) +
      6 * (X ω ^ 2 * Y ω ^ 2)) P := hsum1.add ((hint 2 2 (by omega) (by omega)).const_mul 6)
  have hsum3 : Integrable (fun ω => X ω ^ 4 + 4 * (X ω ^ 3 * Y ω ^ 1) +
      6 * (X ω ^ 2 * Y ω ^ 2) + 4 * (X ω ^ 1 * Y ω ^ 3)) P :=
    hsum2.add ((hint 1 3 (by omega) (by omega)).const_mul 4)
  rw [integral_add hsum3 (hy 4 le_rfl),
    integral_add hsum2 ((hint 1 3 (by omega) (by omega)).const_mul 4),
    integral_add hsum1 ((hint 2 2 (by omega) (by omega)).const_mul 6),
    integral_add (hx 4 le_rfl) ((hint 3 1 (by omega) (by omega)).const_mul 4)]
  simp only [integral_const_mul]
  rw [(hind 3 1).integral_fun_mul_eq_mul_integral (hx 3 (by omega)).aestronglyMeasurable
      (hy 1 (by omega)).aestronglyMeasurable,
    (hind 2 2).integral_fun_mul_eq_mul_integral (hx 2 (by omega)).aestronglyMeasurable
      (hy 2 (by omega)).aestronglyMeasurable,
    (hind 1 3).integral_fun_mul_eq_mul_integral (hx 1 (by omega)).aestronglyMeasurable
      (hy 3 (by omega)).aestronglyMeasurable]
  simp only [pow_one, hmX, hmY]
  ring

/-- Exact fourth moment of a centered independent sum with common second
and fourth moments. Identical distributions are stronger than needed. -/
theorem independent_centered_sum_fourth_moment {ι : Type*} {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 4 P) (hi : iIndepFun X P)
    (hmean : ∀ i, P[X i] = 0) {v κ : ℝ}
    (hsecond : ∀ i, (∫ ω, X i ω ^ 2 ∂P) = v)
    (hfourth : ∀ i, (∫ ω, X i ω ^ 4 ∂P) = κ) (s : Finset ι) :
    (∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂P) =
      (s.card : ℝ) * κ + 3 * s.card * ((s.card : ℝ) - 1) * v ^ 2 := by
  classical
  have hsum (s : Finset ι) : MemLp (fun ω => ∑ i ∈ s, X i ω) 4 P :=
    memLp_finsetSum s (fun i _ => hX i)
  have hsm (s : Finset ι) : (∫ ω, ∑ i ∈ s, X i ω ∂P) = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hX i).integrable (by norm_num))]
    simp [hmean]
  have hsv (s : Finset ι) : (∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂P) = s.card * v := by
    have h := IndepFun.variance_sum (s := s)
      (fun i _ => (hX i).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4))
      (fun i _ j _ hij => hi.indepFun hij)
    have hv (i : ι) : Var[X i; P] = v := by
      rw [variance_eq_sub ((hX i).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4))]
      simpa only [Pi.pow_apply, hmean, hsecond, zero_pow (by norm_num : 2 ≠ 0), sub_zero]
    rw [Finset.sum_fn] at h
    rw [variance_eq_sub ((hsum s).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4))] at h
    simpa [Pi.pow_apply, hsm, hv] using h
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hind : IndepFun (fun ω => ∑ i ∈ s, X i ω) (X a) P := by
      simpa only [Finset.sum_fn] using! hi.indepFun_finsetSum_of_notMem₀
        (fun i => (hX i).aemeasurable) ha
    have hh := independent_centered_fourth_moment_add (hsum s) (hX a) hind (hsm s) (hmean a)
    have he (ω : Ω) : (∑ i ∈ insert a s, X i ω) = (∑ i ∈ s, X i ω) + X a ω := by
      rw [sum_insert ha, add_comm]
    simp_rw [he]
    rw [hh, ih, hsv, hsecond, hfourth, card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
    ring

/-- Exact central fourth moment of an independent sample mean. This supplies
an integrable bound for expectation-level Taylor remainders. -/
theorem sampleMean_fourth_central_moment {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hX : ∀ i, MemLp (X i) 4 P) (hi : iIndepFun X P)
    {μ v κ : ℝ} (hm : ∀ i, P[X i] = μ) (hv : ∀ i, Var[X i; P] = v)
    (hk : ∀ i, (∫ ω, (X i ω - μ) ^ 4 ∂P) = κ) :
    (∫ ω, (sampleMean (fun i => X i ω) - μ) ^ 4 ∂P) =
      (κ + 3 * ((n : ℝ) - 1) * v ^ 2) / (n : ℝ) ^ 3 := by
  let Y i ω := X i ω - μ
  have hY i : MemLp (Y i) 4 P := by
    simpa only [Y, Pi.sub_apply] using! (hX i).sub (memLp_const μ)
  have hYi : iIndepFun Y P := hi.comp (fun _ (x : ℝ) => x - μ) (fun _ => by fun_prop)
  have hYm i : P[Y i] = 0 := by
    dsimp only [Y]
    rw [integral_sub ((hX i).integrable (by norm_num)) (integrable_const μ), hm i]
    simp
  have hYv i : (∫ ω, Y i ω ^ 2 ∂P) = v := by
    have hh := hv i
    rw [variance_eq_integral (hX i).aemeasurable, hm i] at hh
    exact hh
  have hh := independent_centered_sum_fourth_moment hY hYi hYm hYv hk Finset.univ
  simp only [Finset.card_univ, Fintype.card_fin] at hh
  have he (ω : Ω) : sampleMean (fun i => X i ω) - μ =
      (n : ℝ)⁻¹ * ∑ i, Y i ω := by
    rw [← sampleMean_sub_const hn]
    simp only [sampleMean, Fintype.card_fin, Y, one_div]
  simp_rw [he, mul_pow]
  rw [integral_const_mul, hh]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  <;> ring

end LectureNotes
