import Section_10_Zonoid.Hypercube.Geometry.VolumeBridge

/-!
The exact determinant bridge for the consecutive-edge affine map.
No sign adjustment is required: the suffix-one reference simplex has
affine determinant one in the paper's (w,1) row convention.
-/

noncomputable section

namespace Hypercube.Geometry

def edgeAffineMatrix {m : Nat} (w : Fin (m + 1) -> Point m) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) Real :=
  fun i => Fin.lastCases (Fin.lastCases 1 (w (Fin.last m)))
    (fun i => Fin.lastCases 0 (fun j => edgeMatrix w j i)) i

theorem edgeAffineMatrix_minor {m : Nat} (w : Fin (m + 1) -> Point m) :
    (edgeAffineMatrix w).submatrix (Fin.last m).succAbove (Fin.last m).succAbove =
      (edgeMatrix w).transpose := by
  funext i j
  simp only [edgeAffineMatrix, Matrix.submatrix, Fin.succAbove_last,
    Fin.lastCases_castSucc, Matrix.transpose_apply, Matrix.of_apply]

theorem edgeAffineMatrix_det {m : Nat} (w : Fin (m + 1) -> Point m) :
    (edgeAffineMatrix w).det = (edgeMatrix w).det := by
  rw [Matrix.det_succ_column _ (Fin.last m), Fin.sum_univ_castSucc]
  have hzero : Finset.sum Finset.univ
      (fun i : Fin m => (-1 : Real) ^ (i.castSucc.val + (Fin.last m).val) *
        edgeAffineMatrix w i.castSucc (Fin.last m) *
        ((edgeAffineMatrix w).submatrix i.castSucc.succAbove
          (Fin.last m).succAbove).det) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [edgeAffineMatrix, Fin.lastCases_castSucc, Fin.lastCases_last,
      mul_zero, zero_mul]
  rw [hzero, zero_add, edgeAffineMatrix_minor, Matrix.det_transpose]
  simp only [edgeAffineMatrix, Fin.lastCases_last, Fin.val_last, mul_one]
  rw [show m + m = 2 * m from by omega, pow_mul]
  norm_num

theorem affineMatrix_eq_reference_mul {m : Nat} (w : Fin (m + 1) -> Point m) :
    affineMatrix w = affineMatrix (chamberVertex m) * edgeAffineMatrix w := by
  funext r j
  refine Fin.lastCases ?_ (fun j => ?_) j
  next =>
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [affineMatrix, edgeAffineMatrix, Fin.lastCases_last,
      Fin.lastCases_castSucc, mul_zero, mul_one, Finset.sum_const_zero, zero_add]
  next j =>
    have h := congrFun (edgeMatrix_reference_image w r) j
    change Finset.sum Finset.univ
        (fun k : Fin m => edgeMatrix w j k * chamberVertex m r k)
        + w (Fin.last m) j = w r j at h
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [affineMatrix, edgeAffineMatrix, Fin.lastCases_last,
      Fin.lastCases_castSucc, one_mul]
    rw [<- h]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _

theorem affineDet_eq_edgeMatrix_det {m : Nat} (w : Fin (m + 1) -> Point m) :
    affineDet w = (edgeMatrix w).det := by
  unfold affineDet
  rw [affineMatrix_eq_reference_mul, Matrix.det_mul]
  change affineDet (chamberVertex m) * (edgeAffineMatrix w).det = (edgeMatrix w).det
  rw [chamberVertex_affineDet, edgeAffineMatrix_det, one_mul]

end Hypercube.Geometry
