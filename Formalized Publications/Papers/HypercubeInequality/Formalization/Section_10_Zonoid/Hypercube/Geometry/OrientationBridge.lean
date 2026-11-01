import Section_10_Zonoid.Hypercube.Geometry.AffineVolume

/- Source Appendix A: the ordered standard-simplex parameterization uses
base vertex w_0, whereas the paper's affine determinant has rows (w_i,1).
The sign relating these conventions is exactly (-1)^m. -/

noncomputable section

namespace Hypercube.Geometry.OrientationBridge

open Hypercube.Geometry

/-- The j-th coordinate of edge vector w_(i+1)-w_0 is the (j,i) entry. -/
def baseEdgeMatrix {m : Nat} (w : Fin (m + 1) -> Point m) :
    Matrix (Fin m) (Fin m) Real := fun j i => w i.succ j - w 0 j

def orderedSimplexDet {m : Nat} (w : Fin (m + 1) -> Point m) : Real :=
  (baseEdgeMatrix w).det

def standardSimplexPhi {m : Nat} (w : Fin (m + 1) -> Point m) :
    AffineMap Real (Point m) (Point m) where
  toFun t := (Matrix.toLin' (baseEdgeMatrix w)) t + w 0
  linear := Matrix.toLin' (baseEdgeMatrix w)
  map_vadd' t v := by
    change (Matrix.toLin' (baseEdgeMatrix w)) (v + t) + w 0 =
      (Matrix.toLin' (baseEdgeMatrix w)) v +
        ((Matrix.toLin' (baseEdgeMatrix w)) t + w 0)
    rw [map_add, add_assoc]

theorem standardSimplexPhi_formula {m : Nat} (w : Fin (m + 1) -> Point m)
    (t : Point m) (j : Fin m) :
    standardSimplexPhi w t j = w 0 j +
      Finset.sum Finset.univ (fun i => t i * (w i.succ j - w 0 j)) := by
  change Finset.sum Finset.univ (fun i => (w i.succ j - w 0 j) * t i) + w 0 j = _
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem standardSimplexPhi_zero {m : Nat} (w : Fin (m + 1) -> Point m) :
    standardSimplexPhi w 0 = w 0 := by
  change (Matrix.toLin' (baseEdgeMatrix w)) 0 + w 0 = w 0
  rw [map_zero, zero_add]

theorem standardSimplexPhi_basis {m : Nat} (w : Fin (m + 1) -> Point m)
    (i : Fin m) : standardSimplexPhi w (Pi.single i 1) = w i.succ := by
  classical
  funext j
  rw [standardSimplexPhi_formula]
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

theorem affineDet_translation {m : Nat} (w : Fin (m + 1) -> Point m)
    (a : Point m) : affineDet (fun i => w i - a) = affineDet w := by
  let c : Fin (m + 1) -> Real := Fin.lastCases 0 (fun j => -a j)
  have h := Matrix.det_eq_of_forall_row_eq_smul_add_const
    (A := (affineMatrix (fun i => w i - a)).transpose)
    (B := (affineMatrix w).transpose) c (Fin.last m)
    (show c (Fin.last m) = 0 from by simp only [c, Fin.lastCases_last])
    (fun i j => by
      refine Fin.lastCases ?_ (fun i => ?_) i
      next =>
        simp only [Matrix.transpose_apply, affineMatrix, Fin.lastCases_last,
          c, zero_mul, add_zero]
      next i =>
        simp only [Matrix.transpose_apply, affineMatrix, Fin.lastCases_castSucc,
          Fin.lastCases_last, Pi.sub_apply, c, mul_one]
        ring)
  simpa only [Matrix.det_transpose, affineDet] using h

theorem translated_minor {m : Nat} (w : Fin (m + 1) -> Point m) :
    (affineMatrix (fun i => w i - w 0)).submatrix Fin.succ (Fin.last m).succAbove =
      (baseEdgeMatrix w).transpose := by
  funext i j
  simp only [Matrix.submatrix_apply, Fin.succAbove_last, affineMatrix,
    Fin.lastCases_castSucc, Pi.sub_apply, Matrix.transpose_apply, baseEdgeMatrix]

theorem affineDet_eq_signed_orderedSimplexDet {m : Nat}
    (w : Fin (m + 1) -> Point m) :
    affineDet w = (-1 : Real) ^ m * orderedSimplexDet w := by
  rw [<- affineDet_translation w (w 0)]
  unfold affineDet
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_castSucc]
  have hzero : Finset.sum Finset.univ
      (fun j : Fin m => (-1 : Real) ^ j.castSucc.val *
        affineMatrix (fun i => w i - w 0) 0 j.castSucc *
        ((affineMatrix (fun i => w i - w 0)).submatrix Fin.succ
          j.castSucc.succAbove).det) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp only [affineMatrix, Fin.lastCases_castSucc, sub_self,
      Pi.zero_apply, mul_zero, zero_mul]
  rw [hzero, zero_add, translated_minor, Matrix.det_transpose]
  simp only [affineMatrix, Fin.lastCases_last, Fin.val_last, mul_one, orderedSimplexDet]

theorem standardSimplexPhi_linear_det {m : Nat} (w : Fin (m + 1) -> Point m) :
    (standardSimplexPhi w).linear.det = orderedSimplexDet w := by
  exact LinearMap.det_toLin' (baseEdgeMatrix w)

end Hypercube.Geometry.OrientationBridge
