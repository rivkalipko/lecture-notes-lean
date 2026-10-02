import LectureNotes.DKWCensorBridge
import LectureNotes.EmpiricalSupMeasurable

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

/-- Extend the lower quantile by zero outside the open probability interval.
The extension only changes a null set for the uniform law. -/
def quantileTransport (μ : Measure ℝ) (u : ℝ) : ℝ :=
  if u ∈ Ioo (0 : ℝ) 1 then distributionQuantile μ u else 0

theorem quantileTransport_le_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    quantileTransport μ u ≤ t ↔ u ≤ cdf μ t := by
  rw [quantileTransport, if_pos hu]
  exact distributionQuantile_le_iff μ hu

theorem measurable_quantileTransport (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (quantileTransport μ) := by
  apply measurable_of_Iic
  intro t
  have he : quantileTransport μ ⁻¹' Iic t =
      (Ioo (0 : ℝ) 1 ∩ Iic (cdf μ t)) ∪
        (if 0 ≤ t then (Ioo (0 : ℝ) 1)ᶜ else ∅) := by
    ext u
    by_cases hu : u ∈ Ioo (0 : ℝ) 1
    · simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, hu, true_and]
      rw [quantileTransport_le_iff μ hu]
      split_ifs <;> simp [hu]
    · simp [quantileTransport, hu]
  rw [he]
  apply (measurableSet_Ioo.inter measurableSet_Iic).union
  split_ifs
  · exact measurableSet_Ioo.compl
  · exact MeasurableSet.empty

theorem dkwUniformLaw_ae_mem_Ioo : ∀ᵐ u ∂dkwUniformLaw, u ∈ Ioo (0 : ℝ) 1 := by
  have : NullSingletonClass dkwUniformLaw := by unfold dkwUniformLaw; infer_instance
  have h := ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Icc (0 : ℝ) 1) measurableSet_Icc
  filter_upwards [h, (Ioo_ae_eq_Icc (μ := dkwUniformLaw) (a := (0 : ℝ)) (b := 1))] with u hu he
  exact he.mpr hu

/-- Generalized inverse sampling works for every real probability law,
including laws with atoms and gaps in their support. -/
theorem quantileTransport_map (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    dkwUniformLaw.map (quantileTransport μ) = μ := by
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply (measurable_quantileTransport μ) measurableSet_Iic]
  have he : quantileTransport μ ⁻¹' Iic t =ᵐ[dkwUniformLaw] Iic (cdf μ t) := by
    filter_upwards [dkwUniformLaw_ae_mem_Ioo] with u hu
    exact propext (quantileTransport_le_iff μ (t := t) hu)
  rw [measure_congr he, dkwUniformLaw_Iic (cdf_nonneg μ t) (cdf_le_one μ t),
    cdf_eq_real, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]

theorem dkwProductLaw_ae_mem_Ioo (n : ℕ) :
    ∀ᵐ u : Fin n → ℝ ∂dkwProductLaw n, ∀ i, u i ∈ Ioo (0 : ℝ) 1 := by
  exact eventually_all.mpr (fun _ => Measure.tendsto_eval_ae_ae.eventually dkwUniformLaw_ae_mem_Ioo)

theorem quantileTransport_product_map (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    (dkwProductLaw n).map (fun u : Fin n → ℝ => fun i => quantileTransport μ (u i)) =
      Measure.pi (fun _ : Fin n => μ) := by
  change (Measure.pi (fun _ : Fin n => dkwUniformLaw)).map _ = _
  rw [Measure.pi_map_pi (μ := fun _ : Fin n => dkwUniformLaw)
    (f := fun _ : Fin n => quantileTransport μ) (fun _ => (measurable_quantileTransport μ).aemeasurable)]
  simp only [quantileTransport_map]

theorem empiricalCDF_quantileTransport (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, u i ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    empiricalCDF (fun i => quantileTransport μ (u i)) t = empiricalCDF u (cdf μ t) := by
  unfold empiricalCDF
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [quantileTransport_le_iff μ (hu i)]

/-- Quantile coupling reduces the actual supremum statistic for an arbitrary
real law to the uniform empirical error on the unit interval. -/
theorem empiricalCDFSupError_quantile_event_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (ε : ℝ) :
    (Measure.pi (fun _ : Fin n => μ)) {x | ε < empiricalCDFSupError μ x} ≤
      dkwProductLaw n {u | ∃ t ∈ Icc (0 : ℝ) 1, ε < |empiricalCDF u t - t|} := by
  have hm : Measurable (fun u : Fin n → ℝ => fun i => quantileTransport μ (u i)) :=
    measurable_pi_lambda _ (fun i => (measurable_quantileTransport μ).comp (measurable_pi_apply i))
  have hs : MeasurableSet {x : Fin n → ℝ | ε < empiricalCDFSupError μ x} :=
    measurableSet_lt measurable_const (measurable_empiricalCDFSupError μ
      (fun i (x : Fin n → ℝ) => x i) (fun i => measurable_pi_apply i))
  rw [← quantileTransport_product_map μ n, Measure.map_apply hm hs]
  apply measure_mono_ae
  filter_upwards [dkwProductLaw_ae_mem_Ioo n] with u hu
  intro hx
  change ε < sSup (range (fun t => |empiricalCDF (fun i => quantileTransport μ (u i)) t - cdf μ t|)) at hx
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := exists_lt_of_lt_csSup (range_nonempty _) hx
  refine ⟨cdf μ t, ⟨cdf_nonneg μ t, cdf_le_one μ t⟩, ?_⟩
  dsimp only at ht
  rwa [empiricalCDF_quantileTransport μ hu t] at ht

/-- The quantile comparison transfers to any independent sample with the
same marginal law; no continuity assumption on its CDF is required. -/
theorem iid_empiricalCDFSupError_le_uniform {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) μ P) (ε : ℝ) :
    P {ω | ε < empiricalCDFSupError μ (fun i => X i ω)} ≤
      dkwProductLaw n {u | ∃ t ∈ Icc (0 : ℝ) 1, ε < |empiricalCDF u t - t|} := by
  have hmap : P.map (fun ω i => X i ω) = Measure.pi (fun _ : Fin n => μ) := by
    rw [hind.map_fun_eq_pi_map (fun i => (hX i).aemeasurable)]
    simp only [(hlaw _).map_eq]
  calc
    P {ω | ε < empiricalCDFSupError μ (fun i => X i ω)} =
        (Measure.pi (fun _ : Fin n => μ)) {x | ε < empiricalCDFSupError μ x} := by
      rw [← hmap, Measure.map_apply (measurable_pi_lambda _ hX)
        (measurableSet_lt measurable_const (measurable_empiricalCDFSupError μ
          (fun i (x : Fin n → ℝ) => x i) (fun i => measurable_pi_apply i)))]
      rfl
    _ ≤ _ := empiricalCDFSupError_quantile_event_le μ n ε

end LectureNotes
