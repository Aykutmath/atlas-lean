import BMGordonCompactSpecialization

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory ProbabilityTheory GaussianEllipsoid GaussianMixedNormHelpers GaussianTensorMoments
namespace BMGordon

abbrev coordinateCount (n d : ℕ) := Fintype.card (Index n d)

def flatSample (n d : ℕ) (x : Fin (coordinateCount n d) → ℝ) : Space n d :=
  (WithLp.equiv 2 _).symm (fun i => x (Fintype.equivFin (Index n d) i))

def flatCoefficient {n d : ℕ} (a : Space n d) (i : Fin (coordinateCount n d)) : ℝ :=
  a ((Fintype.equivFin (Index n d)).symm i)

theorem flatSample_preserving (n d : ℕ) :
    MeasurePreserving (flatSample n d) (gaussianProductLaw (Fin (coordinateCount n d))) (law n d) := by
  have hraw : MeasurePreserving
      (fun x : Fin (coordinateCount n d) → ℝ => fun i : Index n d => x (Fintype.equivFin (Index n d) i))
      (gaussianProductLaw (Fin (coordinateCount n d))) (gaussianProductLaw (Index n d)) := by
    convert! measurePreserving_piCongrLeft (fun _ : Index n d => gaussianReal 0 1)
      (Fintype.equivFin (Index n d)).symm using 1
    ext x i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have he : MeasurePreserving (MeasurableEquiv.toLp 2 ((Index n d) → ℝ))
      (gaussianProductLaw (Index n d)) (law n d) :=
    ⟨(MeasurableEquiv.toLp 2 ((Index n d) → ℝ)).measurable,rfl⟩
  exact he.comp hraw

theorem flatCoefficient_inner {n d : ℕ} (a b : Space n d) :
    (∑ i, flatCoefficient a i*flatCoefficient b i) = ⟪a,b⟫_ℝ := by
  unfold flatCoefficient
  have h := (Fintype.equivFin (Index n d)).symm.sum_comp (fun j => a j*b j)
  rw [h]
  change (∑ i, a i*b i) = ∑ i, b i*a i
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem flatCoefficient_pairing {n d : ℕ} (a : Space n d)
    (x : Fin (coordinateCount n d) → ℝ) :
    (∑ i, flatCoefficient a i*x i) = ⟪a,flatSample n d x⟫_ℝ := by
  change (∑ i, a ((Fintype.equivFin (Index n d)).symm i)*x i) =
    ∑ j : Index n d, x (Fintype.equivFin (Index n d) j)*a j
  have h := (Fintype.equivFin (Index n d)).symm.sum_comp
    (fun j : Index n d => a j*x (Fintype.equivFin (Index n d) j))
  simp only [Equiv.apply_symm_apply] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem finite_integral_eq_flat {n d : ℕ} {I J : Type*}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (C : I × J → Space n d) (v : I × J → ℝ) :
    (∫ ω, finiteValue (fun i j ω => ⟪C (i,j),ω⟫_ℝ+v (i,j)) ω ∂law n d) =
      ∫ x, finiteValue (fun i j x => (∑ k, flatCoefficient (C (i,j)) k*x k)+v (i,j)) x
        ∂gaussianProductLaw (Fin (coordinateCount n d)) := by
  have hc : Continuous (finiteValue (fun i j ω => ⟪C (i,j),ω⟫_ℝ+v (i,j))) :=
    finiteValue_continuous _ fun i j => (continuous_const.inner continuous_id).add continuous_const
  have h := integral_map (flatSample_preserving n d).measurable.aemeasurable
    (f := finiteValue (fun i j ω => ⟪C (i,j),ω⟫_ℝ+v (i,j))) (by
      rw [(flatSample_preserving n d).map_eq]
      exact hc.aestronglyMeasurable)
  rw [(flatSample_preserving n d).map_eq] at h
  simp_rw [flatCoefficient_pairing]
  exact h

end BMGordon
