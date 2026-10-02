import LectureNotes.GaussianBlockConditioning
import LectureNotes.NormalSufficiency

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace LectureNotes
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

/-- Independent prior and observation errors for the normal hierarchical model.
The first coordinate is the common mean, the other coordinates are its errors. -/
def normalHierarchicalLaw (n : ℕ) (μ : ℝ) (w v : ℝ≥0) :
    Measure (ℝ × (Fin n → ℝ)) :=
  (gaussianReal μ w).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 v))

instance normalHierarchicalLaw_probability (n : ℕ) (μ : ℝ) (w v : ℝ≥0) :
    IsProbabilityMeasure (normalHierarchicalLaw n μ w v) := by
  unfold normalHierarchicalLaw
  infer_instance

/-- The observed sample in the hierarchical normal model. -/
def normalHierarchicalSample {n : ℕ} (z : ℝ × (Fin n → ℝ)) : Fin n → ℝ :=
  fun i => z.1 + z.2 i

/-- The actual conditional sampling law is the product of normals with the
common latent mean. This derives the model from independent prior/error draws. -/
theorem normal_hierarchical_sampling_law (n : ℕ) (μ : ℝ) (w v : ℝ≥0) :
    condDistrib (normalHierarchicalSample (n := n)) Prod.fst
      (normalHierarchicalLaw n μ w v) =ᵐ[gaussianReal μ w]
      (fun θ => normalLocationExperiment n v θ) := by
  let Q := Measure.pi (fun _ : Fin n => gaussianReal 0 v)
  have hh := condDistrib_independent_noise (normalHierarchicalLaw n μ w v)
    (Y := Prod.fst) (R := Prod.snd) measurable_fst measurable_snd
    (indepFun_prod measurable_id measurable_id) (normalHierarchicalSample (n := n))
    (by unfold normalHierarchicalSample; fun_prop)
  have hfst : (normalHierarchicalLaw n μ w v).map Prod.fst = gaussianReal μ w :=
    measurePreserving_fst.map_eq
  have hsnd : (normalHierarchicalLaw n μ w v).map Prod.snd = Q :=
    measurePreserving_snd.map_eq
  rw [hfst] at hh
  filter_upwards [hh] with θ hθ
  rw [hθ]
  change ((normalHierarchicalLaw n μ w v).map Prod.snd).map (fun e i => θ + e i) = _
  rw [hsnd]
  change (Measure.pi (fun _ : Fin n => gaussianReal 0 v)).map
    (fun e i => θ + e i) = Measure.pi (fun _ : Fin n => gaussianReal θ v)
  have hmap := Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 v)
    (f := fun _ (e : ℝ) => θ + e) (fun _ => (measurable_const.add measurable_id).aemeasurable)
  change (Measure.pi (fun _ : Fin n => gaussianReal 0 v)).map (fun e i => θ + e i) = _ at hmap
  rw [hmap]
  congr 1
  funext i
  simpa using gaussianReal_map_const_add (μ := (0 : ℝ)) (v := v) θ

/-- L13 Example 3's full Gaussian block. Its covariance entries are
Cov(Xᵢ,Xⱼ)=w+v·1{i=j}, Cov(Xᵢ,θ)=w, and Var(θ)=w; all means are μ.
Setting v=1 gives exactly the covariance matrix displayed in the notes. -/
theorem normal_hierarchical_joint_parameters (n : ℕ) (μ : ℝ) (w v : ℝ≥0) :
    let P := normalHierarchicalLaw n μ w v
    HasGaussianLaw (fun z => (normalHierarchicalSample z, z.1)) P ∧
      (∀ i, (∫ z, normalHierarchicalSample z i ∂P) = μ) ∧
      (∫ z, z.1 ∂P) = μ ∧
      (∀ i j, cov[fun z => normalHierarchicalSample z i,
        fun z => normalHierarchicalSample z j; P] =
          (w : ℝ) + if i = j then (v : ℝ) else 0) ∧
      (∀ i, cov[fun z => normalHierarchicalSample z i, Prod.fst; P] = (w : ℝ)) ∧
      Var[Prod.fst; P] = (w : ℝ) := by
  classical
  let Q := Measure.pi (fun _ : Fin n => gaussianReal 0 v)
  let P := normalHierarchicalLaw n μ w v
  have hθ : HasLaw (Prod.fst : ℝ × (Fin n → ℝ) → ℝ) (gaussianReal μ w) P :=
    measurePreserving_fst.hasLaw
  have hE : HasLaw (Prod.snd : ℝ × (Fin n → ℝ) → (Fin n → ℝ)) Q P :=
    measurePreserving_snd.hasLaw
  have hQi (i : Fin n) : HasLaw (fun e : Fin n → ℝ => e i) (gaussianReal 0 v) Q :=
    (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 v) i).hasLaw
  have hQind : iIndepFun (fun i (e : Fin n → ℝ) => e i) Q :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hQg : HasGaussianLaw (id : (Fin n → ℝ) → (Fin n → ℝ)) Q :=
    hQind.hasGaussianLaw (fun i => (hQi i).hasGaussianLaw)
  haveI : IsGaussian Q := by
    simpa using hQg.isGaussian_map
  have hEi (i : Fin n) : HasLaw (fun z : ℝ × (Fin n → ℝ) => z.2 i)
      (gaussianReal 0 v) P := by
    simpa only [Function.comp_def] using (hQi i).comp hE
  have hi : IndepFun (Prod.fst : ℝ × (Fin n → ℝ) → ℝ) Prod.snd P :=
    indepFun_prod measurable_id measurable_id
  have hpair := hi.hasGaussianLaw hθ.hasGaussianLaw hE.hasGaussianLaw
  let L : (ℝ × (Fin n → ℝ)) →L[ℝ] ((Fin n → ℝ) × ℝ) :=
    (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ) +
      (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)))).prod
        (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ))
  have hg : HasGaussianLaw (fun z => (normalHierarchicalSample z, z.1)) P :=
    hpair.map_fun L
  have hmθ : (∫ z, z.1 ∂P) = μ := by simpa using! hθ.integral_eq
  have hmE (i) : (∫ z, z.2 i ∂P) = 0 := by simpa using! (hEi i).integral_eq
  have hvθ : Var[Prod.fst; P] = (w : ℝ) := by simpa using! hθ.variance_eq
  have hvE (i) : Var[fun z => z.2 i; P] = (v : ℝ) := by
    simpa using! (hEi i).variance_eq
  have hθE (i : Fin n) : cov[(Prod.fst : ℝ × (Fin n → ℝ) → ℝ), fun z => z.2 i; P] = 0 := by
    have hh := hi.comp measurable_id (measurable_pi_apply i)
    exact hh.covariance_eq_zero hθ.hasGaussianLaw.memLp_two (hEi i).hasGaussianLaw.memLp_two
  have hEE (i j : Fin n) : cov[fun z => z.2 i, fun z => z.2 j; P] =
      if i = j then (v : ℝ) else 0 := by
    by_cases hij : i = j
    · subst j
      rw [covariance_self (hEi i).aemeasurable, hvE i, if_pos rfl]
    · rw [if_neg hij]
      have hc := covariance_map_fun (μ := P) (Z := Prod.snd)
        (X := fun e : Fin n → ℝ => e i) (Y := fun e : Fin n → ℝ => e j)
        (measurable_pi_apply i).aestronglyMeasurable
        (measurable_pi_apply j).aestronglyMeasurable measurable_snd.aemeasurable
      rw [hE.map_eq] at hc
      exact hc.symm.trans ((hQind.indepFun hij).covariance_eq_zero
        (hQi i).hasGaussianLaw.memLp_two (hQi j).hasGaussianLaw.memLp_two)
  have haddL {A B C : (ℝ × (Fin n → ℝ)) → ℝ}
      (hA : MemLp A 2 P) (hB : MemLp B 2 P) (hC : MemLp C 2 P) :
      cov[fun z => A z + B z, C; P] = cov[A, C; P] + cov[B, C; P] := by
    simpa only [Pi.add_apply] using! covariance_add_left hA hB hC
  have haddR {A B C : (ℝ × (Fin n → ℝ)) → ℝ}
      (hA : MemLp A 2 P) (hB : MemLp B 2 P) (hC : MemLp C 2 P) :
      cov[A, fun z => B z + C z; P] = cov[A, B; P] + cov[A, C; P] := by
    simpa only [Pi.add_apply] using! covariance_add_right hA hB hC
  have hxLp (i : Fin n) : MemLp (fun z : ℝ × (Fin n → ℝ) => z.1 + z.2 i) 2 P := by
    simpa only [Pi.add_apply] using! hθ.hasGaussianLaw.memLp_two.add (hEi i).hasGaussianLaw.memLp_two
  refine ⟨hg, ?_, hmθ, ?_, ?_, hvθ⟩
  · intro i
    change (∫ z, z.1 + z.2 i ∂P) = μ
    rw [integral_add hθ.hasGaussianLaw.integrable (hEi i).hasGaussianLaw.integrable,
      hmθ, hmE, add_zero]
  · intro i j
    change cov[fun z => z.1 + z.2 i, fun z => z.1 + z.2 j; P] = _
    rw [haddL hθ.hasGaussianLaw.memLp_two (hEi i).hasGaussianLaw.memLp_two
      (hxLp j),
      haddR hθ.hasGaussianLaw.memLp_two hθ.hasGaussianLaw.memLp_two
        (hEi j).hasGaussianLaw.memLp_two,
      haddR (hEi i).hasGaussianLaw.memLp_two hθ.hasGaussianLaw.memLp_two
        (hEi j).hasGaussianLaw.memLp_two,
      covariance_self hθ.aemeasurable, hvθ, hθE,
      covariance_comm (X := fun z : ℝ × (Fin n → ℝ) => z.2 i) (Y := Prod.fst), hθE, hEE]
    ring
  · intro i
    change cov[fun z => z.1 + z.2 i, Prod.fst; P] = _
    rw [haddL hθ.hasGaussianLaw.memLp_two (hEi i).hasGaussianLaw.memLp_two
      hθ.hasGaussianLaw.memLp_two, covariance_self hθ.aemeasurable, hvθ,
      covariance_comm (X := fun z : ℝ × (Fin n → ℝ) => z.2 i) (Y := Prod.fst), hθE, add_zero]

/-- The vector ordered as in L13: all observations first, then their latent mean. -/
def normalHierarchicalVector {n : ℕ} (z : ℝ × (Fin n → ℝ)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.lastCases z.1 (normalHierarchicalSample z))

/-- The displayed covariance block: w times the all-ones matrix, plus v
on each observation's diagonal and zero on the final latent-mean diagonal. -/
def normalHierarchicalCovariance (n : ℕ) (w v : ℝ≥0) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => (w : ℝ) + if i = j ∧ i ≠ Fin.last n then (v : ℝ) else 0

/-- The actual full hierarchical vector has the multivariate Gaussian law
with the mean and covariance displayed in L13 Example 3 (v=1 there). -/
theorem normal_hierarchical_vector_law (n : ℕ) (μ : ℝ) (w v : ℝ≥0) :
    HasLaw (normalHierarchicalVector (n := n))
      (multivariateGaussian (WithLp.toLp 2 (fun _ => μ))
        (normalHierarchicalCovariance n w v)) (normalHierarchicalLaw n μ w v) := by
  classical
  obtain ⟨hg, hmX, hmθ, hXX, hXθ, hvθ⟩ := normal_hierarchical_joint_parameters n μ w v
  let L : ((Fin n → ℝ) × ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    ContinuousLinearMap.pi (fun i => Fin.lastCases
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ)
      (fun j => (ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ)) i)
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm
  have hY : HasGaussianLaw (normalHierarchicalVector (n := n))
      (normalHierarchicalLaw n μ w v) := by
    have hh := (hg.map_fun L).map_equiv e
    have heq : (fun z => e (L (normalHierarchicalSample z, z.1))) =
        normalHierarchicalVector (n := n) := by
      funext z
      ext i
      induction i using Fin.lastCases <;> simp [e, L, normalHierarchicalVector]
    simpa only [Function.comp_def, heq] using! hh
  have hmean : (∫ z, normalHierarchicalVector z ∂normalHierarchicalLaw n μ w v) =
      WithLp.toLp 2 (fun _ => μ) := by
    ext i
    rw [eval_integral_piLp (fun i => hY.integrable.eval_piLp i)]
    induction i using Fin.lastCases with
    | last => simpa [normalHierarchicalVector] using hmθ
    | cast i => simpa [normalHierarchicalVector] using hmX i
  have hcov : vectorCovariance (normalHierarchicalLaw n μ w v)
      (normalHierarchicalVector (n := n)) = normalHierarchicalCovariance n w v := by
    ext i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        simpa [vectorCovariance, normalHierarchicalVector, normalHierarchicalCovariance,
          covariance_self (measurable_fst.aemeasurable)] using hvθ
      | cast j =>
        simpa [vectorCovariance, normalHierarchicalVector, normalHierarchicalCovariance,
          covariance_comm] using hXθ j
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simpa [vectorCovariance, normalHierarchicalVector, normalHierarchicalCovariance] using hXθ i
      | cast j =>
        simpa [vectorCovariance, normalHierarchicalVector, normalHierarchicalCovariance] using hXX i j
  refine ⟨hY.aemeasurable, ?_⟩
  rw [gaussian_vector_law _ hY, hmean, hcov]

end LectureNotes
