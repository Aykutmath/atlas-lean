import AHHSphereMomentReduction
import AHHLiteralHaarJensen
import Mathlib.Data.Finset.Max

/-! Pathwise positive-semidefinite radial extrema and inclusive tail selection.
All radii in the concrete polar product model are strictly positive. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers AHHAlgebraBridges
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace AHHRadial

abbrev PolarSample (n h : ℕ) := (Fin n → Radius × Radius) × Directions n h

def polarLaw (n h : ℕ) : Measure (PolarSample n h) :=
  (radiiLaw n h).prod (directionsLaw n h)

def polarCovarianceNorm (n h : ℕ) (w : PolarSample n h) : ℝ :=
  ‖gaussianCovariance n h (assembleSample n h w)‖

theorem polarLaw_probability (n h : ℕ) (hh : 0 < h) :
    IsProbabilityMeasure (polarLaw n h) := by
  letI := radiiLaw_probability n h hh
  letI := directionsLaw_probability n h hh
  unfold polarLaw
  infer_instance

theorem radialWeight_pos {n : ℕ} (r : Fin n → Radius × Radius) (i : Fin n) :
    0 < radialWeight r i :=
  mul_pos (sq_pos_of_pos (r i).1.property) (sq_pos_of_pos (r i).2.property)

private def directionMatrix (n h : ℕ) (d : Directions n h) (i : Fin n) :=
  projector (fun p : Fin h × Fin h => ((d i).1 : CE h) p.1 * ((d i).2 : CE h) p.2)

private theorem directionMatrix_nonneg (n h : ℕ) (d : Directions n h) (i : Fin n) :
    0 ≤ directionMatrix n h d i := (projector_posSemidef _).nonneg

private theorem directionMatrix_sum_norm (n h : ℕ) (d : Directions n h) :
    ‖∑ i, directionMatrix n h d i‖ = unitCovarianceNorm n h d := by
  rw [← cMatrixCLM_norm]
  congr 1
  unfold cMatrixCLM unitCovariance
  rw [map_sum]
  rfl

private theorem directionMatrix_weighted_norm (n h : ℕ) (w : PolarSample n h) :
    ‖∑ i, radialWeight w.1 i • directionMatrix n h w.2 i‖ =
      polarCovarianceNorm n h w := by
  rw [← cMatrixCLM_norm]
  unfold polarCovarianceNorm
  rw [gaussianCovariance_assemble]
  congr 1
  unfold cMatrixCLM
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact LinearMapClass.map_smul_of_tower
    (Matrix.toEuclideanCLM (n := Fin h × Fin h) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv _ _

/-- PSD norm comparison with every uniform upper bound on the radial weights. -/
theorem polarCovarianceNorm_le_weight (n h : ℕ) (w : PolarSample n h)
    (a : ℝ) (ha : 0 ≤ a) (hw : ∀ i, radialWeight w.1 i ≤ a) :
    polarCovarianceNorm n h w ≤ a * unitCovarianceNorm n h w.2 := by
  have hm : (∑ i, radialWeight w.1 i • directionMatrix n h w.2 i) ≤
      a • (∑ i, directionMatrix n h w.2 i) := by
    rw [Finset.smul_sum]
    exact Finset.sum_le_sum (fun i _ => smul_le_smul_of_nonneg_right
      (hw i) (directionMatrix_nonneg n h w.2 i))
  have hp : 0 ≤ ∑ i, radialWeight w.1 i • directionMatrix n h w.2 i :=
    Finset.sum_nonneg (fun i _ => smul_nonneg (radialWeight_pos w.1 i).le
      (directionMatrix_nonneg n h w.2 i))
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hm hp
  rw [directionMatrix_weighted_norm, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ha, directionMatrix_sum_norm] at hn
  exact hn

/-- PSD norm comparison with every uniform lower bound on the radial weights. -/
theorem weight_le_polarCovarianceNorm (n h : ℕ) (w : PolarSample n h)
    (a : ℝ) (ha : 0 ≤ a) (hw : ∀ i, a ≤ radialWeight w.1 i) :
    a * unitCovarianceNorm n h w.2 ≤ polarCovarianceNorm n h w := by
  have hm : a • (∑ i, directionMatrix n h w.2 i) ≤
      (∑ i, radialWeight w.1 i • directionMatrix n h w.2 i) := by
    rw [Finset.smul_sum]
    exact Finset.sum_le_sum (fun i _ => smul_le_smul_of_nonneg_right
      (hw i) (directionMatrix_nonneg n h w.2 i))
  have hp : 0 ≤ a • ∑ i, directionMatrix n h w.2 i :=
    smul_nonneg ha (Finset.sum_nonneg (fun i _ => directionMatrix_nonneg n h w.2 i))
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hm hp
  rw [directionMatrix_weighted_norm, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ha, directionMatrix_sum_norm] at hn
  exact hn

/-- The upper selector handles equality in the tail event. -/
theorem polar_upper_select (n h : ℕ) (hn : 0 < n) (w : PolarSample n h) :
    ∃ i : Fin n, polarCovarianceNorm n h w ≤
      radialWeight w.1 i * unitCovarianceNorm n h w.2 := by
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image Finset.univ (radialWeight w.1)
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨⟨0,hn⟩, Finset.mem_univ _⟩)
  exact ⟨i, polarCovarianceNorm_le_weight n h w _ (radialWeight_pos w.1 i).le
    (fun j => himax j (Finset.mem_univ j))⟩

/-- The lower selector handles equality in the tail event. -/
theorem polar_lower_select (n h : ℕ) (hn : 0 < n) (w : PolarSample n h) :
    ∃ i : Fin n, radialWeight w.1 i * unitCovarianceNorm n h w.2 ≤
      polarCovarianceNorm n h w := by
  obtain ⟨i, hi, himin⟩ := Finset.exists_min_image Finset.univ (radialWeight w.1)
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨⟨0,hn⟩, Finset.mem_univ _⟩)
  exact ⟨i, weight_le_polarCovarianceNorm n h w _ (radialWeight_pos w.1 i).le
    (fun j => himin j (Finset.mem_univ j))⟩

/-- Positive almost surely, in fact everywhere in the polar sample space. -/
theorem polarCovarianceNorm_pos (n h : ℕ) (hn : 0 < n) (w : PolarSample n h) :
    0 < polarCovarianceNorm n h w := by
  obtain ⟨i, hi⟩ := polar_lower_select n h hn w
  exact (mul_pos (radialWeight_pos w.1 i)
    (lt_of_lt_of_le zero_lt_one (one_le_unitCovarianceNorm n h hn w.2))).trans_le hi

#print axioms polar_upper_select
#print axioms polar_lower_select
#print axioms polarCovarianceNorm_pos
end AHHRadial
