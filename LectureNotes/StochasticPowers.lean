import LectureNotes.StochasticOrder
import LectureNotes.Inequalities
import LectureNotes.SamplingMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The lecture indexes samples from one. This positive power scale uses n+1
so every real exponent is well-defined and every scale is nonzero. -/
def powerScale (a : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ a

theorem powerScale_pos (a : ℝ) (n : ℕ) : 0 < powerScale a n :=
  Real.rpow_pos_of_pos (by positivity) _

theorem powerScale_add (a b : ℝ) (n : ℕ) :
    powerScale (a + b) n = powerScale a n * powerScale b n :=
  Real.rpow_add (by positivity) _ _

theorem powerScale_neg_tendsto {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (powerScale (-δ)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hδ).comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

theorem stochasticBigO_negative_power {X : ℕ → Ω → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hX : StochasticBigO (P := P) X (powerScale (-δ))) :
    StochasticLittleO (P := P) X (fun _ => 1) :=
  stochasticBigO_vanishing_scale hX (powerScale_neg_tendsto hδ)

theorem stochasticBigO_mul_power {X Y : ℕ → Ω → ℝ} {a b : ℝ}
    (hX : StochasticBigO (P := P) X (powerScale a))
    (hY : StochasticBigO (P := P) Y (powerScale b)) :
    StochasticBigO (P := P) (fun n ω => X n ω * Y n ω) (powerScale (a+b)) := by
  have he : powerScale (a+b) = fun n => powerScale a n * powerScale b n := funext (powerScale_add a b)
  rw [he]
  exact stochasticBigO_mul hX hY

theorem stochasticBigO_add_power {X Y : ℕ → Ω → ℝ} {a b : ℝ}
    (hX : StochasticBigO (P := P) X (powerScale a))
    (hY : StochasticBigO (P := P) Y (powerScale b)) :
    StochasticBigO (P := P) (fun n ω => X n ω + Y n ω)
      (fun n => max (powerScale a n) (powerScale b n)) := by
  simpa only [abs_of_pos (powerScale_pos _ _)] using stochasticBigO_add hX hY

theorem stochasticBigO_mul_littleO_power {X Y : ℕ → Ω → ℝ} {a b : ℝ}
    (hX : StochasticBigO (P := P) X (powerScale a))
    (hY : StochasticLittleO (P := P) Y (powerScale b)) :
    StochasticLittleO (P := P) (fun n ω => X n ω * Y n ω) (powerScale (a+b)) := by
  have he : powerScale (a+b) = fun n => powerScale a n * powerScale b n := funext (powerScale_add a b)
  rw [he]
  exact stochasticBigO_mul_littleO hX hY

/-- The explicit Chebyshev constant in L3 Example 3. Positive variance is
necessary for the lecture's nonzero normalizing scale. -/
theorem standardized_deviation_bound {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    (hv : 0 < Var[Y; P]) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | Real.sqrt (2 / ε) * Real.sqrt (Var[Y; P]) < |Y ω - P[Y]|} ≤ ε/2 := by
  have hC : 0 < Real.sqrt (2/ε) := Real.sqrt_pos.2 (by positivity)
  have hV : 0 < Real.sqrt (Var[Y; P]) := Real.sqrt_pos.2 hv
  have hm := measureReal_mono (μ := P)
    (show {ω | Real.sqrt (2/ε) * Real.sqrt (Var[Y; P]) < |Y ω - P[Y]|} ⊆
      {ω | Real.sqrt (2/ε) * Real.sqrt (Var[Y; P]) ≤ |Y ω - P[Y]|} from
      fun ω h => show Real.sqrt (2/ε) * Real.sqrt (Var[Y; P]) ≤ |Y ω - P[Y]| from h.le) (measure_ne_top P _)
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (chebyshev_deviation hY (mul_pos hC hV))
  rw [ENNReal.toReal_ofReal (by positivity)] at hb
  have he : Var[Y; P] / (Real.sqrt (2/ε) * Real.sqrt (Var[Y; P]))^2 = ε/2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hv.le]
    field_simp
  rw [he] at hb
  exact hm.trans hb

theorem deviation_stochasticBigO_sd {Y : ℕ → Ω → ℝ}
    (hY : ∀ n, MemLp (Y n) 2 P) (hv : ∀ n, 0 < Var[Y n; P]) :
    StochasticBigO (P := P) (fun n ω => Y n ω - P[Y n])
      (fun n => Real.sqrt (Var[Y n; P])) := by
  refine ⟨fun n => ne_of_gt (Real.sqrt_pos.2 (hv n)), fun ε hε => ?_⟩
  refine ⟨Real.sqrt (2/ε), Real.sqrt_pos.2 (by positivity), fun n => ?_⟩
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (standardized_deviation_bound (hY n) (hv n) hε).trans_lt (by linarith)


/-- A bounded sequence at scale a becomes negligible at a larger scale b
when a/b tends to zero. -/
theorem stochasticBigO_littleO_of_scale_ratio {X : ℕ → Ω → ℝ} {a b : ℕ → ℝ}
    (hX : StochasticBigO (P := P) X a) (hb : ∀ n, b n ≠ 0)
    (hr : Tendsto (fun n => a n / b n) atTop (𝓝 0)) :
    StochasticLittleO (P := P) X b := by
  have hc : StochasticLittleO (P := P) (fun n _ => a n / b n) (fun _ => 1) := by
    refine ⟨by simp, ?_⟩
    simp only [div_one]
    exact almost_sure_implies_probability (fun _ => aemeasurable_const)
      (ae_of_all _ (fun _ => hr))
  have hp := stochasticBigO_mul_littleO (stochasticBigO_normalize hX) hc
  refine ⟨hb, ?_⟩
  have he : (fun n ω => (X n ω / a n) * (a n / b n) / ((1:ℝ)*1)) =
      (fun n ω => X n ω / b n) := by
    funext n ω
    field_simp [hX.1 n, hb n]
  have hc := hp.2
  rwa [he] at hc

/-- L3 Example 2: Gaussian variance n+1 gives order sqrt(n+1), regardless
of dependence between different sample sizes. -/
theorem gaussian_growing_variance_bigO {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 (n+1)) P) :
    StochasticBigO (P := P) X (fun n => Real.sqrt ((n : ℝ)+1)) := by
  have hm (n) : P[X n] = 0 := by simpa using (hX n).integral_eq
  have hv (n) : Var[X n; P] = (n : ℝ)+1 := by simpa using (hX n).variance_eq
  simpa only [hm, hv, sub_zero] using deviation_stochasticBigO_sd
    (fun n => (hX n).hasGaussianLaw.memLp_two) (fun n => by rw [hv]; positivity)

/-- L3 Example 2: the same Gaussian sequence is negligible at scale n+1. -/
theorem gaussian_growing_variance_littleO {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 (n+1)) P) :
    StochasticLittleO (P := P) X (fun n => (n : ℝ)+1) := by
  apply stochasticBigO_littleO_of_scale_ratio (gaussian_growing_variance_bigO hX)
    (fun _ => by positivity)
  have he (n : ℕ) : Real.sqrt ((n : ℝ)+1) / ((n : ℝ)+1) =
      ((n : ℝ)+1)^(-(1/2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity)]
    have hs := Real.sq_sqrt (show 0 ≤ (n : ℝ)+1 by positivity)
    rw [← Real.sqrt_eq_rpow]
    have hp : Real.sqrt ((n : ℝ)+1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    field_simp
    exact hs
  simp_rw [he]
  exact powerScale_neg_tendsto (by norm_num : (0 : ℝ) < 1/2)

end LectureNotes
