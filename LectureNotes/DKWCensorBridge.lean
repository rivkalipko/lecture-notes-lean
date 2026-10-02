import LectureNotes.ExponentialFamilySufficiency

set_option autoImplicit false
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

def dkwUniformLaw : Measure ℝ := volume.restrict (Icc 0 1)

instance dkwUniformLaw_probability : IsProbabilityMeasure dkwUniformLaw := by
  constructor
  simp [dkwUniformLaw, Real.volume_Icc]

theorem dkwUniformLaw_Iic {u : ℝ} (_hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    dkwUniformLaw (Iic u) = ENNReal.ofReal u := by
  rw [dkwUniformLaw, Measure.restrict_apply measurableSet_Iic]
  have he : Iic u ∩ Icc (0 : ℝ) 1 = Icc 0 u := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hxu, hx0, _⟩
      exact ⟨hx0, hxu⟩
    · rintro ⟨hx0, hxu⟩
      exact ⟨hxu, hx0, hxu.trans hu1⟩
  rw [he, Real.volume_Icc, sub_zero]

/-- The unnormalized tilted law has mass `1+ℓ`. -/
def dkwTiltedFiniteMeasure (u ℓ : ℝ) : Measure ℝ :=
  dkwUniformLaw + ENNReal.ofReal (ℓ / u) • dkwUniformLaw.restrict (Iic u)

instance dkwTiltedFiniteMeasure_finite (u ℓ : ℝ) :
    IsFiniteMeasure (dkwTiltedFiniteMeasure u ℓ) := by
  constructor
  unfold dkwTiltedFiniteMeasure
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  finiteness

def dkwCountWeight (u ℓ x : ℝ) : ℝ := if x ≤ u then 1 + ℓ / u else 1

theorem dkwCountWeight_measurable (u ℓ : ℝ) : Measurable (dkwCountWeight u ℓ) := by
  unfold dkwCountWeight
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const

theorem dkwTiltedFiniteMeasure_density {u ℓ : ℝ} (hu : 0 < u) (hℓ : 0 ≤ ℓ) :
    dkwUniformLaw.withDensity (fun x => ENNReal.ofReal (dkwCountWeight u ℓ x)) =
      dkwTiltedFiniteMeasure u ℓ := by
  have he : (fun x => ENNReal.ofReal (dkwCountWeight u ℓ x)) =
      (fun _ => (1 : ℝ≥0∞)) + (Iic u).indicator (fun _ => ENNReal.ofReal (ℓ / u)) := by
    funext x
    by_cases hx : x ≤ u
    · simp [dkwCountWeight, hx, ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) (div_nonneg hℓ hu.le)]
    · simp [dkwCountWeight, hx]
  rw [he, withDensity_add_left measurable_const, withDensity_const, one_smul,
    withDensity_indicator measurableSet_Iic, withDensity_const]
  rfl

theorem dkwTiltedFiniteMeasure_censor {u v ℓ : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (huv : u ≤ v) (hℓ : 0 ≤ ℓ) :
    (dkwTiltedFiniteMeasure u ℓ).map (fun x => max x v) =
      dkwUniformLaw.map (fun x => max x v) + ENNReal.ofReal ℓ • Measure.dirac v := by
  have hm : Measurable (fun x : ℝ => max x v) := by fun_prop
  have hr : (dkwUniformLaw.restrict (Iic u)).map (fun x => max x v) =
      ENNReal.ofReal u • Measure.dirac v := by
    have hc : (fun x : ℝ => max x v) =ᵐ[dkwUniformLaw.restrict (Iic u)] (fun _ => v) := by
      filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      exact max_eq_right (hx.trans huv)
    rw [Measure.map_congr hc, Measure.map_const, Measure.restrict_apply_univ,
      dkwUniformLaw_Iic hu.le hu1]
  rw [dkwTiltedFiniteMeasure, Measure.map_add _ _ hm, Measure.map_smul, hr, smul_smul,
    ← ENNReal.ofReal_mul (div_nonneg hℓ hu.le), div_mul_cancel₀ _ hu.ne']

/-- Censoring at any later threshold erases the location of the earlier tilt. -/
theorem dkwTiltedFiniteMeasure_censor_eq {u v ℓ : ℝ}
    (hu : 0 < u) (hv1 : v ≤ 1) (huv : u ≤ v) (hℓ : 0 ≤ ℓ) :
    (dkwTiltedFiniteMeasure u ℓ).map (fun x => max x v) =
      (dkwTiltedFiniteMeasure v ℓ).map (fun x => max x v) := by
  rw [dkwTiltedFiniteMeasure_censor hu (huv.trans hv1) huv hℓ,
    dkwTiltedFiniteMeasure_censor (hu.trans_le huv) hv1 le_rfl hℓ]

theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {g : α → β} (hg : Measurable g)
    {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (fun x => f (g x))).map g = (μ.map g).withDensity f := by
  ext s hs
  rw [Measure.map_apply hg hs, withDensity_apply _ (hs.preimage hg), withDensity_apply _ hs,
    setLIntegral_map hs hf hg]

theorem finite_iid_product_withDensity {Ω : Type*} [MeasurableSpace Ω]
    (ν Q : Measure Ω) [SigmaFinite ν] [IsFiniteMeasure Q]
    (f : Ω → ℝ≥0∞) (hf : Measurable f) (hQ : ν.withDensity f = Q) (n : ℕ) :
    Measure.pi (fun _ : Fin n => Q) =
      (Measure.pi (fun _ : Fin n => ν)).withDensity (fun x => ∏ i, f (x i)) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    change Measure.pi (fun _ : Fin 0 => Q) =
      (Measure.pi (fun _ : Fin 0 => ν)).withDensity (1 : (Fin 0 → Ω) → ℝ≥0∞)
    rw [withDensity_one]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0
    have hsample := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => Q) 0
    have hbase := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    have : IsFiniteMeasure (ν.withDensity f) := by rw [hQ]; infer_instance
    apply e.measurableEmbedding.map_injective
    rw [hsample.map_eq, map_withDensity_equiv _ e _ (by fun_prop), hbase.map_eq,
      ih, ← hQ, prod_withDensity]
    · congr 1
      ext z
      simp [e, Fin.prod_univ_succ]
    all_goals fun_prop

def dkwProductLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => dkwUniformLaw)

instance dkwProductLaw_probability (n : ℕ) : IsProbabilityMeasure (dkwProductLaw n) := by
  unfold dkwProductLaw
  infer_instance

def dkwProductTilted (n : ℕ) (u ℓ : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => dkwTiltedFiniteMeasure u ℓ)

instance dkwProductTilted_finite (n : ℕ) (u ℓ : ℝ) : IsFiniteMeasure (dkwProductTilted n u ℓ) := by
  unfold dkwProductTilted
  infer_instance

def dkwProductWeight {n : ℕ} (u ℓ : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, dkwCountWeight u ℓ (x i)

def dkwCensor {n : ℕ} (v : ℝ) (x : Fin n → ℝ) : Fin n → ℝ := fun i => max (x i) v

theorem measurable_dkwCensor {n : ℕ} (v : ℝ) : Measurable (@dkwCensor n v) := by
  unfold dkwCensor
  fun_prop

theorem measurable_dkwProductWeight {n : ℕ} (u ℓ : ℝ) : Measurable (@dkwProductWeight n u ℓ) := by
  apply Finset.measurable_prod
  intro i _
  exact (dkwCountWeight_measurable u ℓ).comp (measurable_pi_apply i)

theorem dkwCountWeight_nonneg {u ℓ : ℝ} (hu : 0 < u) (hℓ : 0 ≤ ℓ) (x : ℝ) :
    0 ≤ dkwCountWeight u ℓ x := by
  unfold dkwCountWeight
  split_ifs <;> positivity

theorem dkwProductWeight_nonneg {n : ℕ} {u ℓ : ℝ} (hu : 0 < u) (hℓ : 0 ≤ ℓ) (x : Fin n → ℝ) :
    0 ≤ dkwProductWeight u ℓ x := Finset.prod_nonneg (fun i _ => dkwCountWeight_nonneg hu hℓ (x i))

theorem dkwProductWeight_censor {n : ℕ} (v ℓ : ℝ) (x : Fin n → ℝ) :
    dkwProductWeight v ℓ (dkwCensor v x) = dkwProductWeight v ℓ x := by
  simp only [dkwProductWeight, dkwCensor, dkwCountWeight, max_le_iff, le_refl, and_true]

theorem dkwProductTilted_density {n : ℕ} {u ℓ : ℝ} (hu : 0 < u) (hℓ : 0 ≤ ℓ) :
    (dkwProductLaw n).withDensity (fun x => ENNReal.ofReal (dkwProductWeight u ℓ x)) =
      dkwProductTilted n u ℓ := by
  rw [dkwProductTilted, finite_iid_product_withDensity dkwUniformLaw
    (dkwTiltedFiniteMeasure u ℓ) _ ((dkwCountWeight_measurable u ℓ).ennreal_ofReal)
    (dkwTiltedFiniteMeasure_density hu hℓ) n]
  congr 1
  funext x
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => dkwCountWeight_nonneg hu hℓ (x i))

theorem dkwProductTilted_censor_eq {n : ℕ} {u v ℓ : ℝ}
    (hu : 0 < u) (hv1 : v ≤ 1) (huv : u ≤ v) (hℓ : 0 ≤ ℓ) :
    (dkwProductTilted n u ℓ).map (dkwCensor v) =
      (dkwProductTilted n v ℓ).map (dkwCensor v) := by
  change (Measure.pi (fun _ : Fin n => dkwTiltedFiniteMeasure u ℓ)).map
      (fun x i => max (x i) v) =
    (Measure.pi (fun _ : Fin n => dkwTiltedFiniteMeasure v ℓ)).map (fun x i => max (x i) v)
  rw [Measure.pi_map_pi (μ := fun _ : Fin n => dkwTiltedFiniteMeasure u ℓ)
      (f := fun _ : Fin n => fun x : ℝ => max x v) (fun _ => by fun_prop),
    Measure.pi_map_pi (μ := fun _ : Fin n => dkwTiltedFiniteMeasure v ℓ)
      (f := fun _ : Fin n => fun x : ℝ => max x v) (fun _ => by fun_prop)]
  congr 1
  funext i
  exact dkwTiltedFiniteMeasure_censor_eq hu hv1 huv hℓ

set_option maxHeartbeats 800000 in
/-- Exact conditional expectation under the censored-coordinate sigma field.
All variables and the original product sampling law are explicit. -/
theorem dkw_censored_condExp_product {n : ℕ} {u v ℓ : ℝ}
    (hu : 0 < u) (hv1 : v ≤ 1) (huv : u ≤ v) (hℓ : 0 ≤ ℓ) :
    (dkwProductLaw n)[dkwProductWeight u ℓ |
      MeasurableSpace.comap (dkwCensor v) inferInstance] =ᵐ[dkwProductLaw n]
      dkwProductWeight v ℓ := by
  let P := dkwProductLaw n
  let Q := dkwProductTilted n u ℓ
  let C := @dkwCensor n v
  have hv : 0 < v := hu.trans_le huv
  have hm : Measurable C := measurable_dkwCensor v
  have hWu := @measurable_dkwProductWeight n u ℓ
  have hWv := @measurable_dkwProductWeight n v ℓ
  have hQ : Q = P.withDensity (fun x => ENNReal.ofReal (dkwProductWeight u ℓ x)) :=
    (dkwProductTilted_density hu hℓ).symm
  have hmap : Q.map C = (P.map C).withDensity (fun x => ENNReal.ofReal (dkwProductWeight v ℓ x)) := by
    calc
      Q.map C = (dkwProductTilted n v ℓ).map C := dkwProductTilted_censor_eq hu hv1 huv hℓ
      _ = (P.withDensity (fun x => ENNReal.ofReal (dkwProductWeight v ℓ (C x)))).map C := by
        have hf : (fun x : Fin n → ℝ => ENNReal.ofReal (dkwProductWeight v ℓ (C x))) =
            (fun x => ENNReal.ofReal (dkwProductWeight v ℓ x)) := by
          funext x
          rw [dkwProductWeight_censor]
        rw [hf]
        exact congrArg (fun ν : Measure (Fin n → ℝ) => ν.map C)
          (dkwProductTilted_density (n := n) hv hℓ).symm
      _ = _ := map_withDensity_comp P (g := C)
        (f := fun x : Fin n → ℝ => ENNReal.ofReal (dkwProductWeight v ℓ x)) hm hWv.ennreal_ofReal
  have hQac : Q ≪ P := by
    rw [hQ]
    exact withDensity_absolutelyContinuous _ _
  have hRN : (fun x => (Q.rnDeriv P x).toReal) =ᵐ[P] dkwProductWeight u ℓ := by
    rw [hQ]
    filter_upwards [Measure.rnDeriv_withDensity P hWu.ennreal_ofReal] with x hx
    rw [hx, ENNReal.toReal_ofReal (dkwProductWeight_nonneg hu hℓ x)]
  have hRNmap : (fun x => ((Q.map C).rnDeriv (P.map C) (C x)).toReal) =ᵐ[P]
      dkwProductWeight v ℓ := by
    rw [hmap]
    filter_upwards [ae_of_ae_map hm.aemeasurable
      (Measure.rnDeriv_withDensity (P.map C) hWv.ennreal_ofReal)] with x hx
    rw [hx, ENNReal.toReal_ofReal (dkwProductWeight_nonneg hv hℓ (C x)), dkwProductWeight_censor]
  have hCE := toReal_rnDeriv_map hQac hm
  calc
    P[dkwProductWeight u ℓ | MeasurableSpace.comap C inferInstance] =ᵐ[P]
        P[(fun x => (Q.rnDeriv P x).toReal) | MeasurableSpace.comap C inferInstance] :=
      condExp_congr_ae hRN.symm
    _ =ᵐ[P] (fun x => ((Q.map C).rnDeriv (P.map C) (C x)).toReal) := hCE.symm
    _ =ᵐ[P] dkwProductWeight v ℓ := hRNmap

theorem dkwProductWeight_integrable {n : ℕ} {u ℓ : ℝ} (hu : 0 < u) (hℓ : 0 ≤ ℓ) :
    Integrable (@dkwProductWeight n u ℓ) (dkwProductLaw n) := by
  apply (integrable_const ((1 + ℓ / u) ^ n)).mono'
    (measurable_dkwProductWeight u ℓ).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (dkwProductWeight_nonneg hu hℓ x)]
  calc
    dkwProductWeight u ℓ x ≤ ∏ i : Fin n, (1 + ℓ / u) := by
      apply Finset.prod_le_prod (fun i _ => dkwCountWeight_nonneg hu hℓ (x i))
      intro i _
      unfold dkwCountWeight
      split_ifs
      · exact le_rfl
      · have h := div_nonneg hℓ hu.le
        linarith
    _ = _ := by simp

theorem dkwCountWeight_integral {u ℓ : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    (∫ x, dkwCountWeight u ℓ x ∂dkwUniformLaw) = 1 + ℓ := by
  have hi : Integrable ((Iic u).indicator (fun _ : ℝ => (1 : ℝ))) dkwUniformLaw :=
    (integrable_const 1).indicator measurableSet_Iic
  have he : dkwCountWeight u ℓ =
      (fun x => 1 + (ℓ / u) * (Iic u).indicator (fun _ => (1 : ℝ)) x) := by
    funext x
    by_cases hx : x ≤ u <;> simp [dkwCountWeight, hx]
  rw [he, integral_add (integrable_const 1) (hi.const_mul _), integral_const_mul,
    integral_indicator measurableSet_Iic, setIntegral_const]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  rw [measureReal_def, dkwUniformLaw_Iic hu.le hu1, ENNReal.toReal_ofReal hu.le]
  field_simp

theorem dkwProductWeight_integral {n : ℕ} {u ℓ : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    (∫ x, dkwProductWeight u ℓ x ∂dkwProductLaw n) = (1 + ℓ) ^ n := by
  change (∫ x : Fin n → ℝ, ∏ i, dkwCountWeight u ℓ (x i)
    ∂Measure.pi (fun _ : Fin n => dkwUniformLaw)) = _
  rw [integral_fintype_prod_eq_prod]
  simp only [dkwCountWeight_integral hu hu1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem measurable_dkwProductWeight_comap {n : ℕ} (v ℓ : ℝ) :
    @Measurable (Fin n → ℝ) ℝ (MeasurableSpace.comap (@dkwCensor n v) inferInstance)
      inferInstance (dkwProductWeight v ℓ) := by
  have hm : @Measurable (Fin n → ℝ) (Fin n → ℝ)
      (MeasurableSpace.comap (@dkwCensor n v) inferInstance) inferInstance (dkwCensor v) :=
    measurable_iff_comap_le.mpr le_rfl
  have h := (measurable_dkwProductWeight v ℓ).comp hm
  have he : (dkwProductWeight v ℓ) ∘ (@dkwCensor n v) = dkwProductWeight v ℓ := by
    funext x
    exact dkwProductWeight_censor v ℓ x
  rwa [he] at h

end LectureNotes
