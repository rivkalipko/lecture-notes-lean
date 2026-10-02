import LectureNotes.MixtureMinimalSufficiency
import Mathlib.Topology.Instances.EReal.Lemmas

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Under a dominated reference, the zero set of a likelihood ratio agrees
with the zero set of the actual model density, up to reference-null sets. -/
theorem rnDeriv_nonzero_iff_density {Ω : Type*} [MeasurableSpace Ω]
    (P μ ν : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hPμ : P ≪ μ) {f : Ω → ℝ≥0∞} (hf : Measurable f)
    (hP : ν.withDensity f = P) :
    ∀ᵐ x ∂μ, P.rnDeriv μ x ≠ 0 ↔ f x ≠ 0 := by
  have hchain := Measure.rnDeriv_mul_rnDeriv (κ := ν) hPμ
  have hd := Measure.rnDeriv_withDensity ν hf
  rw [hP] at hd
  filter_upwards [hμν.ae_le hchain, hμν.ae_le hd, Measure.rnDeriv_pos hμν] with x hx hd hp
  change P.rnDeriv μ x * μ.rnDeriv ν x = P.rnDeriv ν x at hx
  rw [← hd, ← hx, mul_ne_zero_iff]
  exact (and_iff_left hp.ne').symm

/-- A common almost-sure property is preserved by arbitrary countable
combinations of the experiment's models. -/
theorem ae_mixture_of_ae_models {Θ Ω ι : Type*} [MeasurableSpace Ω]
    [Countable ι] (P : Θ → Measure Ω) (parameters : ι → Θ) (w : ι → ℝ≥0∞)
    {p : Ω → Prop} (hp : ∀ θ, ∀ᵐ x ∂P θ, p x) :
    ∀ᵐ x ∂Measure.sum (fun i => w i • P (parameters i)), p x := by
  rw [Measure.ae_sum_iff]
  exact fun i => Measure.ae_smul_measure (hp (parameters i)) (w i)

/-- A measurable decoder for a positive endpoint from the likelihood ratios
of the positive rational endpoint models. -/
def positiveRationalCutDecode (r : {q : ℚ // 0 < q} → ℝ≥0∞) : ℝ :=
  (⨅ q : {q : ℚ // 0 < q}, if r q ≠ 0 then ((q.1 : ℝ) : EReal) else ⊤).toReal

theorem positiveRationalCutDecode_measurable : Measurable positiveRationalCutDecode := by
  unfold positiveRationalCutDecode
  apply measurable_ereal_toReal.comp
  apply Measurable.iInf
  intro q
  exact Measurable.ite ((measurable_pi_apply q) (measurableSet_singleton 0)).compl
    measurable_const measurable_const

/-- The positive rational upper cut uniquely recovers any positive real. -/
theorem positiveRationalCutDecode_recover {m : ℝ} (hm : 0 < m)
    (r : {q : ℚ // 0 < q} → ℝ≥0∞)
    (hr : ∀ q, r q ≠ 0 ↔ m ≤ (q.1 : ℝ)) : positiveRationalCutDecode r = m := by
  have he : (⨅ q : {q : ℚ // 0 < q}, if r q ≠ 0 then ((q.1 : ℝ) : EReal) else ⊤) = (m : EReal) := by
    apply le_antisymm
    · by_contra hh
      obtain ⟨q, hmq, hq⟩ := EReal.exists_rat_btwn_of_lt (lt_of_not_ge hh)
      have hmqR : m < (q : ℝ) := by exact_mod_cast hmq
      have hqpos : (0 : ℚ) < q := by exact_mod_cast hm.trans hmqR
      have hcut : r ⟨q, hqpos⟩ ≠ 0 := (hr ⟨q, hqpos⟩).mpr hmqR.le
      have hle := iInf_le (fun q : {q : ℚ // 0 < q} =>
        if r q ≠ 0 then ((q.1 : ℝ) : EReal) else ⊤) ⟨q, hqpos⟩
      change (⨅ q : {q : ℚ // 0 < q}, if r q ≠ 0 then ((q.1 : ℝ) : EReal) else ⊤) ≤
        (if r ⟨q, hqpos⟩ ≠ 0 then ((q : ℝ) : EReal) else ⊤) at hle
      rw [if_pos hcut] at hle
      exact (not_lt_of_ge hle) hq
    · apply le_iInf
      intro q
      split_ifs with hq
      · exact_mod_cast (hr q).mp hq
      · exact le_top
  unfold positiveRationalCutDecode
  rw [he, EReal.toReal_coe]

end LectureNotes
