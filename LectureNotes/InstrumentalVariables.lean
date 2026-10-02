import LectureNotes.BootstrapMoments
import LectureNotes.Convergence
import Mathlib.Probability.Moments.Covariance

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- L6 Example 3: relevance and the two stated residual moment conditions
identify the slope and intercept. These are statistical moment conditions;
no causal interpretation is added to them. -/
theorem instrumental_variables_identification {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y D Z : Ω → ℝ}
    (hY : MemLp Y 2 P) (hD : MemLp D 2 P) (hZ : MemLp Z 2 P)
    (α β : ℝ) (hmean : (∫ ω, Y ω - α - β * D ω ∂P) = 0)
    (hexog : cov[Z, fun ω => Y ω - α - β * D ω; P] = 0)
    (hrel : cov[Z, D; P] ≠ 0) :
    β = cov[Z, Y; P] / cov[Z, D; P] ∧ α = P[Y] - β * P[D] := by
  have hYi := hY.integrable (by norm_num)
  have hDi := hD.integrable (by norm_num)
  have hcov := covariance_fun_sub_right hZ (hY.sub (memLp_const α)) (hD.const_mul β)
  simp only [Pi.sub_apply] at hcov
  rw [hcov] at hexog
  change cov[Z, fun ω => Y ω - α; P] - cov[Z, fun ω => β * D ω; P] = 0 at hexog
  rw [covariance_sub_const_right hYi α, covariance_const_mul_right β] at hexog
  have hsub := integral_sub (hYi.sub (integrable_const α)) (hDi.const_mul β)
  simp only [Pi.sub_apply] at hsub
  rw [hsub] at hmean
  change (∫ ω, Y ω - α ∂P) - (∫ ω, β * D ω ∂P) = 0 at hmean
  rw [integral_sub hYi (integrable_const α), integral_const, probReal_univ,
    one_smul, integral_const_mul] at hmean
  exact ⟨(eq_div_iff hrel).mpr (by linarith), by linarith⟩

/-- Empirical covariance uses the plug-in denominator n. Its denominator
cancels from the instrumental-variables slope ratio. -/
def sampleCovariance {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  sampleMean (fun i => x i * y i) - sampleMean x * sampleMean y

theorem sampleMean_sub_const {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (c : ℝ) :
    sampleMean (fun i => x i - c) = sampleMean x - c := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [sampleMean, Fintype.card_fin, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem sampleMean_sub {n : ℕ} (x y : Fin n → ℝ) :
    sampleMean (fun i => x i - y i) = sampleMean x - sampleMean y := by
  simp only [sampleMean, Fintype.card_fin, Finset.sum_sub_distrib, mul_sub]

theorem sampleMean_const_mul {n : ℕ} (x : Fin n → ℝ) (c : ℝ) :
    sampleMean (fun i => c * x i) = c * sampleMean x := by
  simp only [sampleMean, Fintype.card_fin, ← Finset.mul_sum]
  ring

theorem sampleCovariance_centered {n : ℕ} (hn : 0 < n) (x y : Fin n → ℝ) :
    sampleCovariance x y = sampleMean (fun i => (x i - sampleMean x) * (y i - sampleMean y)) := by
  have he : (fun i => (x i - sampleMean x) * (y i - sampleMean y)) =
      (fun i => x i * y i - sampleMean y * x i -
        (sampleMean x * y i - sampleMean x * sampleMean y)) := by
    funext i
    ring
  rw [he, sampleMean_sub, sampleMean_sub, sampleMean_const_mul,
    sampleMean_sub_const hn, sampleMean_const_mul]
  unfold sampleCovariance
  ring

theorem sampleCovariance_residual {n : ℕ} (hn : 0 < n)
    (y d z : Fin n → ℝ) (α β : ℝ) :
    sampleCovariance z (fun i => y i - α - β * d i) =
      sampleCovariance z y - β * sampleCovariance z d := by
  unfold sampleCovariance
  rw [sampleMean_sub, sampleMean_sub_const hn, sampleMean_const_mul]
  have he : (fun i => z i * (y i - α - β * d i)) =
      (fun i => z i * y i - α * z i - β * (z i * d i)) := by funext i; ring
  rw [he, sampleMean_sub, sampleMean_sub, sampleMean_const_mul, sampleMean_const_mul]
  ring

/-- The displayed IV slope and intercept uniquely solve the empirical
counterparts of the two population residual moments. -/
theorem instrumental_variables_sample_equations {n : ℕ} (hn : 0 < n)
    (y d z : Fin n → ℝ) (hrel : sampleCovariance z d ≠ 0) (α β : ℝ) :
    (sampleMean (fun i => y i - α - β * d i) = 0 ∧
      sampleCovariance z (fun i => y i - α - β * d i) = 0) ↔
    (β = sampleCovariance z y / sampleCovariance z d ∧
      α = sampleMean y - β * sampleMean d) := by
  rw [sampleCovariance_residual hn, sampleMean_sub, sampleMean_sub_const hn, sampleMean_const_mul]
  constructor
  · rintro ⟨hmean, hcov⟩
    exact ⟨(eq_div_iff hrel).mpr (by linarith), by linarith⟩
  · rintro ⟨hβ, hα⟩
    have hh := (eq_div_iff hrel).mp hβ
    constructor <;> linarith

/-- The empirical covariance is strongly consistent under finite second
moments, with arbitrary dependence of the two coordinates within a draw. -/
theorem sampleCovariance_strong_consistency {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → α} (g h : α → ℝ) (hg : Measurable g) (hh : Measurable h)
    (hgp : MemLp (fun ω => g (X 0 ω)) 2 P) (hhp : MemLp (fun ω => h (X 0 ω)) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ConvergesAlmostSurely P
      (fun n ω => sampleCovariance (fun i : Fin n => g (X i ω)) (fun i : Fin n => h (X i ω)))
      (fun _ => cov[fun ω => g (X 0 ω), fun ω => h (X 0 ω); P]) := by
  have hprod : Measurable (fun a => g a * h a) := hg.mul hh
  have hlaw (f : α → ℝ) (hf : Measurable f) (hfi : Integrable (fun ω => f (X 0 ω)) P) :=
    strong_law_of_large_numbers hfi
      (fun i j hij => (hind.comp (fun _ => f) (fun _ => hf)).indepFun hij)
      (fun i => (hident i).comp hf)
  filter_upwards [hlaw g hg (hgp.integrable (by norm_num)),
    hlaw h hh (hhp.integrable (by norm_num)), hlaw (fun a => g a * h a) hprod (hgp.integrable_mul hhp)]
      with ω hgω hhω hprodω
  have hc := hprodω.sub (hgω.mul hhω)
  simp only [Function.comp_def] at hc
  have hcov := covariance_eq_sub hgp hhp
  simp only [Pi.mul_apply] at hcov
  rw [← hcov] at hc
  convert! hc using 1
  funext n
  simp only [sampleCovariance, sampleMean, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => g (X i ω) * h (X i ω)) n,
    Fin.sum_univ_eq_sum_range (fun i => g (X i ω)) n,
    Fin.sum_univ_eq_sum_range (fun i => h (X i ω)) n]
  ring

/-- Under instrument relevance, the sample covariance ratio converges almost
surely to its population counterpart. The two covariances may be dependent. -/
theorem instrumental_variables_slope_consistency {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → α} (y d z : α → ℝ)
    (hy : Measurable y) (hd : Measurable d) (hz : Measurable z)
    (hyp : MemLp (fun ω => y (X 0 ω)) 2 P)
    (hdp : MemLp (fun ω => d (X 0 ω)) 2 P)
    (hzp : MemLp (fun ω => z (X 0 ω)) 2 P)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hrel : cov[fun ω => z (X 0 ω), fun ω => d (X 0 ω); P] ≠ 0) :
    ConvergesAlmostSurely P
      (fun n ω => sampleCovariance (fun i : Fin n => z (X i ω)) (fun i : Fin n => y (X i ω)) /
        sampleCovariance (fun i : Fin n => z (X i ω)) (fun i : Fin n => d (X i ω)))
      (fun _ => cov[fun ω => z (X 0 ω), fun ω => y (X 0 ω); P] /
        cov[fun ω => z (X 0 ω), fun ω => d (X 0 ω); P]) := by
  filter_upwards [sampleCovariance_strong_consistency z y hz hy hzp hyp hind hident,
    sampleCovariance_strong_consistency z d hz hd hzp hdp hind hident] with ω hyω hdω
  exact hyω.div hdω hrel

end LectureNotes
