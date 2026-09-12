import LectureNotes.EmpiricalDistribution

/-! L4: resampling independently from the empirical distribution. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Finset

variable {n : ℕ} [NeZero n]

def empiricalLaw (x : Fin n → ℝ) : Measure ℝ :=
  (PMF.uniformOfFintype (Fin n)).toMeasure.map x

instance empiricalLaw_isProbabilityMeasure (x : Fin n → ℝ) :
    IsProbabilityMeasure (empiricalLaw x) :=
  Measure.isProbabilityMeasure_map (show Measurable x from Measurable.of_discrete).aemeasurable

theorem empiricalLaw_cdf (x : Fin n → ℝ) (t : ℝ) :
    cdf (empiricalLaw x) t = empiricalCDF x t := by
  classical
  rw [cdf_eq_real, empiricalLaw, measureReal_def,
    Measure.map_apply_of_aemeasurable (show Measurable x from Measurable.of_discrete).aemeasurable measurableSet_Iic,
    PMF.toMeasure_uniformOfFintype_apply (α := Fin n) (s := x ⁻¹' Set.Iic t)
      (Set.to_countable _ |>.measurableSet), Fintype.card_subtype]
  simp only [Set.mem_preimage, Set.mem_Iic, Fintype.card_fin, ENNReal.toReal_div,
    ENNReal.toReal_natCast, empiricalCDF]
  congr 1
  simp

def bootstrapIndexLaw (n : ℕ) [NeZero n] : Measure (Fin n → Fin n) :=
  Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype (Fin n)).toMeasure)

def bootstrapLaw (x : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => empiricalLaw x)

/-- Independent uniform indices give an IID sample from the empirical law. -/
theorem bootstrapSample_hasLaw (x : Fin n → ℝ) :
    HasLaw (bootstrapSample x) (bootstrapLaw x) (bootstrapIndexLaw n) := by
  have hx : Measurable x := Measurable.of_discrete
  have hind : iIndepFun (fun i (b : Fin n → Fin n) => x (b i)) (bootstrapIndexLaw n) :=
    iIndepFun_pi (fun _ => hx.aemeasurable)
  apply hind.hasLaw_pi
  intro i
  have hi := measurePreserving_eval
    (fun _ : Fin n => (PMF.uniformOfFintype (Fin n)).toMeasure) i
  have hlaw : HasLaw x (empiricalLaw x) (PMF.uniformOfFintype (Fin n)).toMeasure :=
    ⟨hx.aemeasurable, rfl⟩
  exact hlaw.comp ⟨hi.measurable.aemeasurable, hi.map_eq⟩
end LectureNotes
