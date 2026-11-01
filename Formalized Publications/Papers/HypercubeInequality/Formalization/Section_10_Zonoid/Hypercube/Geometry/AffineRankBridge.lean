import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Fin.SuccPred

/- A full-row-rank n by (n+1) matrix has a nonsingular omission minor.
This bridges the source full affine span hypothesis to a nonzero cofactor. -/

noncomputable section

namespace Hypercube.Geometry.AffineRankBridge

/-- Full row rank supplies one nonzero maximal minor, with the source omission indexing. -/
theorem exists_omission_det_ne_zero {n : Nat}
    (A : Matrix (Fin n) (Fin (n + 1)) Real) (hfull : A.rank = n) :
    exists p : Fin (n + 1), Not ((A.submatrix id p.succAbove).det = 0) := by
  classical
  have hx := exists_linearIndependent' Real A.col
  let Index := Classical.choose hx
  have hx2 := Classical.choose_spec hx
  let a : Index -> Fin (n + 1) := Classical.choose hx2
  have hs := Classical.choose_spec hx2
  have ha : Function.Injective a := hs.1
  have hspan := hs.2.1
  have hli := hs.2.2
  let _ := Fintype.ofInjective a ha
  have hcard : Fintype.card Index = n := by
    rw [linearIndependent_iff_card_eq_finrank_span] at hli
    rw [Set.finrank, hspan, <- Matrix.rank_eq_finrank_span_cols] at hli
    exact hli.trans hfull
  have hun := Fintype.existsUnique_notMem_image_of_injective_of_card_eq_add_one a ha
    (by simp only [Fintype.card_fin, hcard])
  let p := Classical.choose hun
  have hp := (Classical.choose_spec hun).1
  have hunique := (Classical.choose_spec hun).2
  have hsurj : forall i : Fin (n + 1), Not (i = p) -> exists x : Index, a x = i := by
    intro i hip
    by_contra hi
    have hnot : Not (Membership.mem (Finset.univ.image a) i) := by
      simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hi
    exact hip (hunique i hnot)
  have hex : forall j : Fin n, exists x : Index, a x = p.succAbove j := by
    intro j
    exact hsurj (p.succAbove j) (Fin.succAbove_ne p j)
  choose g hg using hex
  have hgInjective : Function.Injective g := by
    intro j k hjk
    apply Fin.succAbove_right_injective
    rw [<- hg j, <- hg k, hjk]
  have hcol : (A.submatrix id p.succAbove).col = Function.comp (Function.comp A.col a) g := by
    funext j i
    change A i (p.succAbove j) = A i (a (g j))
    rw [hg j]
  refine Exists.intro p ?_
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.linearIndependent_col_iff.mp
  rw [hcol]
  exact hli.comp g hgInjective

end Hypercube.Geometry.AffineRankBridge
