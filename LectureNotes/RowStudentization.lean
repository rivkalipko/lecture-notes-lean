import LectureNotes.UniformCDFConvergence

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- Finite-sample CDF bounds for division by a random scale close to one.
The exceptional event contains zero and negative scales, so they need not be
excluded everywhere or even at each finite sample size. -/
theorem studentization_cdf_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y S : Ω → ℝ)
    (t : ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    P.real {ω | Y ω ≤ t - |t| * δ} - P.real {ω | δ ≤ |S ω - 1|} ≤
        P.real {ω | Y ω / S ω ≤ t} ∧
    P.real {ω | Y ω / S ω ≤ t} ≤
        P.real {ω | Y ω ≤ t + |t| * δ} + P.real {ω | δ ≤ |S ω - 1|} := by
  have hcontrol (ω : Ω) (hω : ¬ δ ≤ |S ω - 1|) :
      0 < S ω ∧ t - |t| * δ ≤ t * S ω ∧ t * S ω ≤ t + |t| * δ := by
    have habs : |S ω - 1| < δ := lt_of_not_ge hω
    have hS : 0 < S ω := by have hh := (abs_lt.mp habs).1; linarith
    have hm : |t * S ω - t| ≤ |t| * δ := by
      calc
        _ = |t| * |S ω - 1| := by rw [← abs_mul]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left habs.le (abs_nonneg t)
    exact ⟨hS, by have hh := (abs_le.mp hm).1; linarith,
      by have hh := (abs_le.mp hm).2; linarith⟩
  constructor
  · have hsub : {ω | Y ω ≤ t - |t| * δ} ⊆
        {ω | Y ω / S ω ≤ t} ∪ {ω | δ ≤ |S ω - 1|} := by
      intro ω hω
      by_cases hb : δ ≤ |S ω - 1|
      · exact Or.inr hb
      · have hc := hcontrol ω hb
        exact Or.inl ((div_le_iff₀ hc.1).mpr (hω.trans hc.2.1))
    have hh := (measureReal_mono (μ := P) hsub).trans (measureReal_union_le (μ := P) _ _)
    linarith
  · have hsub : {ω | Y ω / S ω ≤ t} ⊆
        {ω | Y ω ≤ t + |t| * δ} ∪ {ω | δ ≤ |S ω - 1|} := by
      intro ω hω
      by_cases hb : δ ≤ |S ω - 1|
      · exact Or.inr hb
      · have hc := hcontrol ω hb
        exact Or.inl (((div_le_iff₀ hc.1).mp hω).trans hc.2.2)
    exact (measureReal_mono (μ := P) hsub).trans (measureReal_union_le (μ := P) _ _)

/-- Slutsky studentization with sample spaces and probability laws that vary
by row. Only closeness of the scale in its own row probability is required. -/
theorem dependent_rows_studentization_cdf {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (P : (n : ℕ) → Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (Y S : (n : ℕ) → Ω n → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hY : ∀ t, Tendsto (fun n => (P n).real {ω | Y n ω ≤ t}) atTop (𝓝 (cdf ν t)))
    (hS : ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ |S n ω - 1|}) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n => (P n).real {ω | Y n ω / S n ω ≤ t}) atTop (𝓝 (cdf ν t)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hc : ContinuousAt (fun δ : ℝ => cdf ν (t - |t| * δ)) 0 :=
      (continuous_cdf_of_atomless ν).continuousAt.comp (by fun_prop)
    have hc' : Tendsto (fun δ : ℝ => cdf ν (t - |t| * δ)) (𝓝 0) (𝓝 (cdf ν t)) := by
      simpa using hc.tendsto
    have he := hc'.eventually (lt_mem_nhds ha)
    have hs : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < 1 ∧ a < cdf ν (t - |t| * δ) := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
        nhdsWithin_le_nhds he] with δ hδ0 hδ1 hδ
      exact ⟨hδ0, hδ1, hδ⟩
    obtain ⟨δ, hδ0, hδ1, hδ⟩ := hs.exists
    have hl := (hY (t - |t| * δ)).sub (hS δ hδ0)
    simp only [sub_zero] at hl
    filter_upwards [hl.eventually (lt_mem_nhds hδ)] with n hn
    exact hn.trans_le (studentization_cdf_bounds (P n) (Y n) (S n) t hδ0 hδ1).1
  · intro b hb
    have hc : ContinuousAt (fun δ : ℝ => cdf ν (t + |t| * δ)) 0 :=
      (continuous_cdf_of_atomless ν).continuousAt.comp (by fun_prop)
    have hc' : Tendsto (fun δ : ℝ => cdf ν (t + |t| * δ)) (𝓝 0) (𝓝 (cdf ν t)) := by
      simpa using hc.tendsto
    have he := hc'.eventually (gt_mem_nhds hb)
    have hs : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < 1 ∧ cdf ν (t + |t| * δ) < b := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
        nhdsWithin_le_nhds he] with δ hδ0 hδ1 hδ
      exact ⟨hδ0, hδ1, hδ⟩
    obtain ⟨δ, hδ0, hδ1, hδ⟩ := hs.exists
    have hl := (hY (t + |t| * δ)).add (hS δ hδ0)
    simp only [add_zero] at hl
    filter_upwards [hl.eventually (gt_mem_nhds hδ)] with n hn
    exact ((studentization_cdf_bounds (P n) (Y n) (S n) t hδ0 hδ1).2).trans_lt hn

/-- Equivalent pushforward-law CDF statement for measurable row statistics. -/
theorem dependent_rows_studentization_map_cdf {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (P : (n : ℕ) → Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (Y S : (n : ℕ) → Ω n → ℝ)
    (hYm : ∀ n, Measurable (Y n)) (hSm : ∀ n, Measurable (S n))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hY : ∀ t, Tendsto (fun n => (P n).real {ω | Y n ω ≤ t}) atTop (𝓝 (cdf ν t)))
    (hS : ∀ ε > 0, Tendsto (fun n => (P n).real {ω | ε ≤ |S n ω - 1|}) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n => cdf ((P n).map (fun ω => Y n ω / S n ω)) t) atTop (𝓝 (cdf ν t)) := by
  have he n : cdf ((P n).map (fun ω => Y n ω / S n ω)) t =
      (P n).real {ω | Y n ω / S n ω ≤ t} := by
    letI := Measure.isProbabilityMeasure_map ((hYm n).div (hSm n)).aemeasurable (μ := P n)
    rw [cdf_eq_real]
    change ((P n).map (Y n / S n)).real (Iic t) = _
    rw [map_measureReal_apply ((hYm n).div (hSm n)) measurableSet_Iic]
    rfl
  simp_rw [he]
  exact dependent_rows_studentization_cdf P Y S ν hY hS t

end LectureNotes
