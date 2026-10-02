import LectureNotes.GammaConjugacy
import LectureNotes.PoissonMoments
import LectureNotes.BootstrapVarianceConsistency
import LectureNotes.MonteCarlo

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal

/-- A deterministic version of the Gamma–Poisson posterior-mean limit. -/
theorem gamma_poisson_mean_tendsto {a r rate : ℝ} (s : ℕ → ℕ)
    (hs : Tendsto (fun n => (s n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 rate)) :
    Tendsto (fun n => (a + s n) / (r + ((n : ℝ) + 1))) atTop (𝓝 rate) := by
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have ha : Tendsto (fun n : ℕ => a / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using tendsto_const_nhds.mul hinv
  have hr : Tendsto (fun n : ℕ => r / ((n : ℝ) + 1) + 1) atTop (𝓝 1) := by
    simpa only [mul_zero, mul_one_div, zero_add] using (tendsto_const_nhds.mul hinv).add_const 1
  have hh := (ha.add hs).div hr (by norm_num : (1 : ℝ) ≠ 0)
  simp only [zero_add, div_one] at hh
  convert hh using 1
  funext n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  dsimp only [Pi.div_apply]
  field_simp

/-- The posterior variance vanishes along every path whose sample mean converges. -/
theorem gamma_poisson_variance_tendsto {a r rate : ℝ} (s : ℕ → ℕ)
    (hs : Tendsto (fun n => (s n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 rate)) :
    Tendsto (fun n => (a + s n) / (r + ((n : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (r + ((n : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    exact tendsto_atTop_add_const_left _ _ (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hh := (gamma_poisson_mean_tendsto (a := a) (r := r) s hs).mul hinv
  simp only [mul_zero] at hh
  convert hh using 1
  funext n
  simp only [pow_two, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The actual conjugate posterior puts asymptotically all its mass in every
neighborhood of the limiting empirical rate. This is a pathwise theorem;
no posterior normal approximation is assumed. -/
theorem gamma_poisson_posterior_concentration {a r rate : ℝ} (ha : 0 < a) (hr : 0 < r)
    (s : ℕ → ℕ)
    (hs : Tendsto (fun n => (s n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 rate)) :
    ∀ ε > 0, Tendsto (fun n : ℕ =>
      (bayesUpdate (gammaMeasure a r)
        (fun x => Real.exp (-((n : ℝ) + 1) * x) * x ^ s n)).real
          {x | ε ≤ |x - rate|}) atTop (𝓝 0) := by
  let Q (n : ℕ) : Measure ℝ := gammaMeasure (a + s n) (r + ((n : ℝ) + 1))
  have hQ n : IsProbabilityMeasure (Q n) := isProbabilityMeasure_gammaMeasure (by positivity) (by positivity)
  let : ∀ n, IsProbabilityMeasure (Q n) := hQ
  have hLp n : MemLp (id : ℝ → ℝ) 2 (Q n) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr
      (gamma_power_integrable _ _ (by positivity) (by positivity) 2)
  have hc n : (∫ x : ℝ, x ∂Q n) = (a + s n) / (r + ((n : ℝ) + 1)) :=
    gamma_mean _ _ (by positivity) (by positivity)
  have hv n : Var[id; Q n] = (a + s n) / (r + ((n : ℝ) + 1)) ^ 2 :=
    gamma_variance _ _ (by positivity) (by positivity)
  have hcenterLp n : MemLp (fun x : ℝ => x - (a + s n) / (r + ((n : ℝ) + 1))) 2 (Q n) := by
    simpa only [Pi.sub_apply, id_eq] using! (hLp n).sub (memLp_const _)
  have hmse : Tendsto (fun n => ∫ x : ℝ, (x - (a + s n) / (r + ((n : ℝ) + 1))) ^ 2 ∂Q n)
      atTop (𝓝 0) := by
    have he n : (∫ x : ℝ, (x - (a + s n) / (r + ((n : ℝ) + 1))) ^ 2 ∂Q n) =
        (a + s n) / (r + ((n : ℝ) + 1)) ^ 2 := by
      have hh := variance_eq_integral (by fun_prop : AEMeasurable (id : ℝ → ℝ) (Q n))
      simp only [id_eq] at hh
      rw [← hc n, ← hh]
      exact hv n
    simp_rw [he]
    exact gamma_poisson_variance_tendsto s hs
  have hh := row_probability_center_limit (gamma_poisson_mean_tendsto (a := a) (r := r) s hs)
    (row_secondMoment_implies_probability hcenterLp hmse)
  intro ε hε
  convert hh ε hε using 1
  funext n
  rw [show -((n : ℝ) + 1) = -(((n + 1 : ℕ) : ℝ)) by push_cast; ring,
    gamma_poisson_conjugacy a r ha hr (n + 1) (s n)]
  simp only [Q, Nat.cast_add, Nat.cast_one]

/-- Almost-sure concentration for the actual IID Poisson experiment. The
boundary rate zero is also allowed, as the degenerate Poisson distribution. -/
theorem iid_gamma_poisson_posterior_concentration {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℕ} {rate : ℝ≥0}
    (hX : ∀ i, HasLaw (X i) (poissonMeasure rate) P) (hind : iIndepFun X P)
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ ε > 0, Tendsto (fun n : ℕ =>
      (bayesUpdate (gammaMeasure a r)
        (fun x => Real.exp (-((n : ℝ) + 1) * x) * x ^ (∑ i : Fin (n + 1), X i ω))).real
          {x | ε ≤ |x - rate|}) atTop (𝓝 0) := by
  let Y i ω := (X i ω : ℝ)
  have hcast : Measurable (fun k : ℕ => (k : ℝ)) := Measurable.of_discrete
  have hident i : IdentDistrib (Y i) (fun k : ℕ => (k : ℝ)) P (poissonMeasure rate) :=
    ((hX i).identDistrib HasLaw.id).comp hcast
  have hLp : MemLp (Y 0) 2 P := (hident 0).memLp_iff.mpr (poisson_memLp_two rate)
  have hmean : (∫ ω, Y 0 ω ∂P) = (rate : ℝ) :=
    (hident 0).integral_eq.trans (poisson_mean rate)
  have hindY : iIndepFun Y P := hind.comp (fun _ k => (k : ℝ)) (fun _ => hcast)
  have hh := monteCarlo_mean_strong_consistency (hLp.integrable (by norm_num)) hindY
    (fun i => (hident i).trans (hident 0).symm)
  filter_upwards [hh] with ω hω
  apply gamma_poisson_posterior_concentration ha hr (fun n => ∑ i : Fin (n + 1), X i ω)
  have hω' := hω.comp (tendsto_add_atTop_nat 1)
  rw [hmean] at hω'
  convert! hω' using 1
  funext n
  simp only [sampleMean, Fintype.card_fin, Nat.cast_sum, Nat.cast_add, Nat.cast_one,
    Y, Function.comp_apply]
  ring

end LectureNotes
