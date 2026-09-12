import LectureNotes.Estimation

namespace LectureNotes

open Filter MeasureTheory ProbabilityTheory Set Function
open scoped Topology

/-! Definitions from Lecture 3 and the convergence theorems supplied by Mathlib. -/

def ConvergesAlmostSurely {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))

def ConvergesInProbability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) : Prop :=
  TendstoInMeasure μ X atTop Y

def ConvergesInDistribution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (μ' : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (X : ℕ → Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  TendstoInDistribution X atTop Y (fun _ => μ) μ'

def ConvergesInMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) : Prop :=
  (∀ n, Integrable (fun ω => X n ω - Y ω) P) ∧
    Tendsto (fun n => ∫ ω, |X n ω - Y ω| ∂P) atTop (𝓝 0)

def ConvergesInMeanSquare {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) : Prop :=
  (∀ n, MemLp (fun ω => X n ω - Y ω) 2 P) ∧
    Tendsto (fun n => ∫ ω, |X n ω - Y ω| ^ 2 ∂P) atTop (𝓝 0)

def Consistent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : ℕ → Ω → ℝ) (θ : ℝ) : Prop :=
  ConvergesInProbability μ T (fun _ => θ)

def AsymptoticallyNormal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (T : ℕ → Ω → ℝ) (a r : ℕ → ℝ) (σ : ℝ) (Z : Ω → ℝ) : Prop :=
  0 < σ ∧ HasLaw Z (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) μ ∧
    ConvergesInDistribution μ μ (fun n ω => r n * (T n ω - a n)) Z

theorem strong_law_of_large_numbers
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hint : Integrable (X 0) P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ConvergesAlmostSurely P
      (fun n ω => (∑ i ∈ Finset.range n, X i ω) / n) (fun _ => P[X 0]) :=
  ProbabilityTheory.strong_law_ae_real X hint hindep hident

theorem central_limit_theorem
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ConvergesInDistribution P P'
      (fun n ω => (√n)⁻¹ *
        (∑ k ∈ Finset.range n, X k ω - n * P[X 0])) Y := by
  exact ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub hY hX hindep hident

/-! The empirical CDF and the nonparametric bootstrap. -/

noncomputable def empiricalCDF {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i, if x i ≤ t then (1 : ℝ) else 0) / n

theorem empiricalCDF_nonneg {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    0 ≤ empiricalCDF x t := by
  unfold empiricalCDF
  positivity

theorem empiricalCDF_mono {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    Monotone (empiricalCDF x) := by
  intro s t hst
  unfold empiricalCDF
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro i hi
  by_cases hs : x i ≤ s
  · have ht : x i ≤ t := hs.trans hst
    simp [hs, ht]
  · by_cases ht : x i ≤ t <;> simp [hs, ht]

theorem empiricalCDF_le_one {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (t : ℝ) :
    empiricalCDF x t ≤ 1 := by
  unfold empiricalCDF
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n)).2
  calc
    (∑ i, if x i ≤ t then (1 : ℝ) else 0) ≤ ∑ _ : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      split <;> simp
    _ = 1 * (n : ℝ) := by simp

def BootstrapIndex (n : ℕ) := Fin n → Fin n

def bootstrapSample {α : Type*} {n : ℕ} (x : Fin n → α)
    (b : BootstrapIndex n) : Fin n → α := fun i => x (b i)

theorem bootstrapSample_is_resample {α : Type*} {n : ℕ} (x : Fin n → α)
    (b : BootstrapIndex n) (i : Fin n) : ∃ j : Fin n, bootstrapSample x b i = x j :=
  ⟨b i, rfl⟩

end LectureNotes
