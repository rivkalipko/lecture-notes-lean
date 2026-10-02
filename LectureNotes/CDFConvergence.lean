import LectureNotes.QuantileConvergence
import Mathlib.Topology.Algebra.Module.Cardinality

set_option autoImplicit false

/-! L3: the CDF definition of convergence in distribution agrees with weak
convergence of probability measures. Only continuity points of the limiting
CDF are required, so discrete and mixed laws are included. -/
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem measure_singleton_zero_of_continuousAt_cdf (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {x : ℝ} (hx : ContinuousAt (cdf μ) x) : μ {x} = 0 := by
  rw [← measure_cdf μ, StieltjesFunction.measure_singleton]
  rw [((monotone_cdf μ).continuousWithinAt_Iio_iff_leftLim_eq).mp hx.continuousWithinAt]
  simp

theorem dense_continuity_points_cdf (μ : Measure ℝ) :
    Dense {x | ContinuousAt (cdf μ) x} := by
  simpa only [compl_ofPred, not_not] using
    (monotone_cdf μ).countable_not_continuousAt.dense_compl ℝ

/-- CDF convergence at continuity points characterizes weak convergence. -/
theorem probabilityMeasure_tendsto_iff_cdf (μ : ℕ → ProbabilityMeasure ℝ)
    (ν : ProbabilityMeasure ℝ) :
    Tendsto μ atTop (𝓝 ν) ↔
      ∀ x, ContinuousAt (cdf (ν : Measure ℝ)) x →
        Tendsto (fun n => cdf (μ n : Measure ℝ) x) atTop
          (𝓝 (cdf (ν : Measure ℝ) x)) := by
  constructor
  · intro h x hx
    have hb : (ν : Measure ℝ) (frontier (Iic x)) = 0 := by
      rw [frontier_Iic]
      exact measure_singleton_zero_of_continuousAt_cdf _ hx
    have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hb
    simpa only [cdf_eq_real, measureReal_def, Function.comp_def] using
      (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure ℝ) (Iic x))).comp ht
  · intro h
    let C := {x | ContinuousAt (cdf (ν : Measure ℝ)) x}
    apply (isPiSystem_Ioc_mem C C).tendsto_probabilityMeasure_of_tendsto_of_mem
    · rintro s ⟨a, ha, b, hb, hab, rfl⟩
      exact measurableSet_Ioc
    · intro u hu x hx
      obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (hu.mem_nhds hx)
      obtain ⟨a', ha', haa', ha'x⟩ := (dense_continuity_points_cdf (ν : Measure ℝ)).exists_between hax
      obtain ⟨b', hb', hxb', hb'b⟩ := (dense_continuity_points_cdf (ν : Measure ℝ)).exists_between hxb
      refine ⟨Ioc a' b', ⟨a', ha', b', hb', ha'x.trans hxb', rfl⟩,
        Ioc_mem_nhds ha'x hxb', ?_⟩
      intro y hy
      exact hab ⟨haa'.trans hy.1, hy.2.trans_lt hb'b⟩
    · rintro s ⟨a, ha, b, hb, hab, rfl⟩
      have hm (ρ : ProbabilityMeasure ℝ) :
          (ρ : Measure ℝ) (Ioc a b) =
            ENNReal.ofReal (cdf (ρ : Measure ℝ) b - cdf (ρ : Measure ℝ) a) := by
        calc
          _ = (cdf (ρ : Measure ℝ)).measure (Ioc a b) := by rw [measure_cdf]
          _ = _ := StieltjesFunction.measure_Ioc _ _ _
      have ht : Tendsto (fun n => (μ n : Measure ℝ) (Ioc a b)) atTop
          (𝓝 ((ν : Measure ℝ) (Ioc a b))) := by
        simp_rw [hm]
        exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((h b hb).sub (h a ha))
      exact (ENNReal.tendsto_toNNReal (measure_ne_top (ν : Measure ℝ) (Ioc a b))).comp ht

/-- The notes' real-valued distributional convergence criterion, for random
variables on possibly different probability spaces. -/
theorem convergesInDistribution_iff_cdf {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : ∀ n, AEMeasurable (X n) P) (hZ : AEMeasurable Z Q) :
    ConvergesInDistribution P Q X Z ↔
      ∀ x, ContinuousAt (cdf (Q.map Z)) x →
        Tendsto (fun n => P.real {ω | X n ω ≤ x}) atTop
          (𝓝 (Q.real {ω | Z ω ≤ x})) := by
  letI (n : ℕ) : IsProbabilityMeasure (P.map (X n)) :=
    Measure.isProbabilityMeasure_map (hX n)
  letI : IsProbabilityMeasure (Q.map Z) := Measure.isProbabilityMeasure_map hZ
  have he (x : ℝ) : cdf (Q.map Z) x = Q.real {ω | Z ω ≤ x} := by
    rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hZ measurableSet_Iic]
    rfl
  have heX (n : ℕ) (x : ℝ) : cdf (P.map (X n)) x = P.real {ω | X n ω ≤ x} := by
    rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable (hX n) measurableSet_Iic]
    rfl
  have ht := probabilityMeasure_tendsto_iff_cdf
    (fun n => ⟨P.map (X n), inferInstance⟩) ⟨Q.map Z, inferInstance⟩
  simp only [ProbabilityMeasure.coe_mk, heX, he] at ht
  exact ⟨fun h => ht.mp h.tendsto, fun h => ⟨hX, hZ, ht.mpr h⟩⟩

end LectureNotes
