import BartlettJointLaw

noncomputable section
open MeasureTheory ProbabilityTheory
open GaussianTensorMoments

namespace GaussianMixedNormHelpers

/-- Flattening two independent finite Gaussian coordinate families gives the
actual scalar iid law on the product index. -/
theorem gaussianProductColumns_map_uncurry {κ ι : Type*} [Fintype κ] [Fintype ι] :
    Measure.map (fun g : κ → ι → ℝ => fun p : κ × ι => g p.1 p.2)
      (Measure.pi (fun _ : κ => gaussianProductLaw ι)) = gaussianProductLaw (κ × ι) := by
  have hm : Measurable (fun g : κ → ι → ℝ => fun p : κ × ι => g p.1 p.2) :=
    measurable_pi_iff.mpr (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))
  unfold gaussianProductLaw
  apply (Measure.pi_eq (fun S hS => ?_)).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hS)]
  have heq : (fun g : κ → ι → ℝ => fun p : κ × ι => g p.1 p.2) ⁻¹' Set.univ.pi S =
      Set.univ.pi (fun k : κ => Set.univ.pi (fun i : ι => S (k, i))) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Prod.forall]
  rw [heq, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun p : κ × ι => gaussianReal 0 1 (S p))).symm

/-- Grouping scalar Gaussian coordinates into rows gives the independent row law. -/
theorem gaussianProductLaw_map_curry {κ ι : Type*} [Fintype κ] [Fintype ι] :
    Measure.map (fun z : (κ × ι) → ℝ => fun k i => z (k,i)) (gaussianProductLaw (κ × ι)) =
      Measure.pi (fun _ : κ => gaussianProductLaw ι) := by
  rw [← gaussianProductColumns_map_uncurry]
  rw [Measure.map_map]
  · exact Measure.map_id
  · exact measurable_pi_iff.mpr (fun k => measurable_pi_iff.mpr (fun i => measurable_pi_apply (k,i)))
  · exact measurable_pi_iff.mpr (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))

/-- Ordinary scalar Gaussian rows transported to their genuine Euclidean norm. -/
theorem gaussianProductRows_map_euclideanRows (r m : ℕ) :
    Measure.map (fun G : Fin r → Fin m → ℝ => matrixEuclideanRows G)
      (Measure.pi (fun _ : Fin r => gaussianProductLaw (Fin m))) =
        Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin m)) := by
  have h := measurePreserving_pi
    (fun _ : Fin r => gaussianProductLaw (Fin m))
    (fun _ : Fin r => euclideanGaussianLaw (Fin m))
    (f := fun _ => ((MeasurableEquiv.toLp 2 ((Fin m) → ℝ)).symm).symm)
    (fun _ => ⟨((MeasurableEquiv.toLp 2 ((Fin m) → ℝ)).symm).symm.measurable, rfl⟩)
  exact h.map_eq

/-- Any injectively selected finite block of actual independent Gaussian columns,
transposed into Euclidean rows, has exactly the iid Euclidean Gaussian row law. -/
theorem gaussianColumns_map_selectedRows {κ : Type*} [Fintype κ]
    (r m : ℕ) (e : Fin m → κ) (he : Function.Injective e) :
    Measure.map (fun g : κ → Fin r → ℝ => matrixEuclideanRows (fun p j => g (e j) p))
      (Measure.pi (fun _ : κ => gaussianProductLaw (Fin r))) =
      Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin m)) := by
  let u := fun g : κ → Fin r → ℝ => fun p : κ × Fin r => g p.1 p.2
  let t := fun p : Fin r × Fin m => (e p.2, p.1)
  let q := fun z : (κ × Fin r) → ℝ => fun p : Fin r × Fin m => z (t p)
  let c := fun z : (Fin r × Fin m) → ℝ => fun p j => z (p,j)
  have ht : Function.Injective t := by
    intro a b hab
    apply Prod.ext
    · exact congrArg Prod.snd hab
    · exact he (congrArg Prod.fst hab)
  have hu : Measurable u :=
    measurable_pi_iff.mpr (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))
  have hq : Measurable q := measurable_pi_iff.mpr (fun p => measurable_pi_apply (t p))
  have hc : Measurable c :=
    measurable_pi_iff.mpr (fun p => measurable_pi_iff.mpr (fun j => measurable_pi_apply (p,j)))
  have hE : Measurable (fun G : Fin r → Fin m → ℝ => matrixEuclideanRows G) :=
    measurable_pi_iff.mpr (fun p =>
      ((MeasurableEquiv.toLp 2 ((Fin m) → ℝ)).symm).symm.measurable.comp (measurable_pi_apply p))
  change Measure.map ((fun G : Fin r → Fin m → ℝ => matrixEuclideanRows G) ∘ c ∘ q ∘ u) _ = _
  rw [← Measure.map_map hE (hc.comp (hq.comp hu)),
    ← Measure.map_map hc (hq.comp hu), ← Measure.map_map hq hu]
  rw [show Measure.map u (Measure.pi (fun _ : κ => gaussianProductLaw (Fin r))) =
      gaussianProductLaw (κ × Fin r) from gaussianProductColumns_map_uncurry]
  rw [show Measure.map q (gaussianProductLaw (κ × Fin r)) =
      gaussianProductLaw (Fin r × Fin m) from gaussianProductLaw_map_subfamily t ht]
  rw [show Measure.map c (gaussianProductLaw (Fin r × Fin m)) =
      Measure.pi (fun _ : Fin r => gaussianProductLaw (Fin m)) from gaussianProductLaw_map_curry]
  exact gaussianProductRows_map_euclideanRows r m

end GaussianMixedNormHelpers
