import LectureNotes.Foundations

/-! L1 continuity of probability, finite partitions, chain rule, and CDFs. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

theorem probability_continuous_from_below {A : ℕ → Set Ω} (hA : Monotone A) :
    Tendsto (fun n => P.real (A n)) atTop (𝓝 (P.real (⋃ n, A n))) :=
  (ENNReal.continuousAt_toReal (measure_ne_top P _)).tendsto.comp
    (tendsto_measure_iUnion_atTop hA)

theorem probability_continuous_from_above {A : ℕ → Set Ω}
    (hm : ∀ n, MeasurableSet (A n)) (hA : Antitone A) :
    Tendsto (fun n => P.real (A n)) atTop (𝓝 (P.real (⋂ n, A n))) :=
  (ENNReal.continuousAt_toReal (measure_ne_top P _)).tendsto.comp
    (tendsto_measure_iInter_atTop (fun n => (hm n).nullMeasurableSet)
      hA ⟨0, measure_ne_top P _⟩)

theorem total_probability {k : ℕ} {A : Set Ω} {B : Fin k → Set Ω}
    (hA : MeasurableSet A) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hcover : (⋃ i, B i) = univ) (hpos : ∀ i, P.real (B i) ≠ 0) :
    P.real A = ∑ i, conditionalProbability P A (B i) * P.real (B i) := by
  simp_rw [conditional_probability P (hpos _)]
  have heq : (⋃ i, A ∩ B i) = A := by
    rw [← inter_iUnion, hcover, inter_univ]
  rw [← heq, measureReal_iUnion_fintype
    (fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right)
    (fun i => hA.inter (hB i))]
  simp_rw [heq]

def eventPrefix (A : ℕ → Set Ω) : ℕ → Set Ω
  | 0 => univ
  | n + 1 => A n ∩ eventPrefix A n

theorem multiplication_rule (A : ℕ → Set Ω) (n : ℕ)
    (hpos : ∀ i < n, P.real (eventPrefix A i) ≠ 0) :
    P.real (eventPrefix A n) =
      ∏ i ∈ Finset.range n, conditionalProbability P (A i) (eventPrefix A i) := by
  induction n with
  | zero => simp [eventPrefix]
  | succ n ih =>
    rw [Finset.prod_range_succ, ← ih (fun i hi => hpos i (by omega))]
    change P.real (A n ∩ eventPrefix A n) =
      P.real (eventPrefix A n) *
        (P.real (A n ∩ eventPrefix A n) / P.real (eventPrefix A n))
    field_simp [hpos n (by omega)]

def ConditionallyIndependentEvents (A B C : Set Ω) : Prop :=
  MeasurableSet A ∧ MeasurableSet B ∧ MeasurableSet C ∧ P.real C ≠ 0 ∧
    conditionalProbability P (A ∩ B) C =
    conditionalProbability P A C * conditionalProbability P B C

def cdfOf (X : Ω → ℝ) : ℝ → ℝ := cdf (P.map X)

theorem cdfOf_eq_probability {X : Ω → ℝ} (hX : AEMeasurable X P) (x : ℝ) :
    cdfOf P X x = P.real {ω | X ω ≤ x} := by
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  rw [cdfOf, cdf_eq_real]
  simp only [measureReal_def, Measure.map_apply_of_aemeasurable hX measurableSet_Iic]
  rfl

theorem cdfOf_monotone (X : Ω → ℝ) : Monotone (cdfOf P X) :=
  monotone_cdf (P.map X)
theorem cdfOf_atBot (X : Ω → ℝ) : Tendsto (cdfOf P X) atBot (𝓝 0) :=
  tendsto_cdf_atBot (P.map X)
theorem cdfOf_atTop (X : Ω → ℝ) : Tendsto (cdfOf P X) atTop (𝓝 1) :=
  tendsto_cdf_atTop (P.map X)
theorem cdfOf_right_continuous (X : Ω → ℝ) (x : ℝ) :
    ContinuousWithinAt (cdfOf P X) (Ici x) x := (cdf (P.map X)).right_continuous x

/-- L1 Definition 6, using all finite subfamilies, not just pairs. -/
def JointlyIndependentEvents {ι : Type*} (A : ι → Set Ω) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧
    ∀ s : Finset ι, P (⋂ i ∈ s, A i) = ∏ i ∈ s, P (A i)
end LectureNotes
