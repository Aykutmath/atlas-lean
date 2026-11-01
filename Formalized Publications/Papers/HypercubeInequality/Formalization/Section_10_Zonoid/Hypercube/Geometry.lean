import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Source: hypercube_readable.tex, Section 2 and Section 3.
The last coordinate of affineMatrix is the constant 1, exactly as in the paper.
The auxiliary firstColumnMatrix puts the height first so its Laplace expansion
has no common column-permutation sign. paper_height_determinant independently
proves the common (-1)^m sign for the paper's actual (W,T,1) matrix.
No determinant/Euclidean-volume bridge or simplex cocycle is assumed here.
-/

noncomputable section

namespace Hypercube.Geometry

open MeasureTheory

abbrev Point (m : Nat) := Fin m -> Real

/-- The paper's square matrix with rows (w_i,1), in the specified row order. -/
def affineMatrix {m : Nat} (w : Fin (m + 1) -> Point m) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) Real :=
  fun i => Fin.lastCases 1 (w i)

def affineDet {m : Nat} (w : Fin (m + 1) -> Point m) : Real :=
  (affineMatrix w).det

/-- Cofactor signs use positions, and succAbove preserves the remaining order. -/
def cofactor {m : Nat} (w : Fin (m + 2) -> Point m)
    (i : Fin (m + 2)) : Real :=
  (-1 : Real) ^ i.val * affineDet (fun j => w (i.succAbove j))

def radonMass {m : Nat} (w : Fin (m + 2) -> Point m) : Real :=
  (1 / 2 : Real) * Finset.sum Finset.univ (fun i => |cofactor w i|)

/-- Rows (t_i,w_i,1). This is only an auxiliary determinant. -/
def firstColumnMatrix {m : Nat} (w : Fin (m + 2) -> Point m)
    (t : Fin (m + 2) -> Real) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) Real :=
  fun i => Fin.cases (t i) (Fin.lastCases 1 (w i))

/-- The paper's actual row order (w_i,t_i,1). -/
def paperHeightMatrix {m : Nat} (w : Fin (m + 2) -> Point m)
    (t : Fin (m + 2) -> Real) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) Real :=
  fun i => Fin.lastCases 1 (Fin.lastCases (t i) (w i))

def liftedPoint {m : Nat} (w : Point m) (t : Real) : Point (m + 1) :=
  Fin.lastCases t w

theorem paperHeightMatrix_eq_affineMatrix {m : Nat}
    (w : Fin (m + 2) -> Point m) (t : Fin (m + 2) -> Real) :
    paperHeightMatrix w t = affineMatrix (fun i => liftedPoint (w i) (t i)) := rfl

theorem paperHeightMatrix_minor {m : Nat}
    (w : Fin (m + 2) -> Point m) (t : Fin (m + 2) -> Real)
    (i : Fin (m + 2)) :
    (paperHeightMatrix w t).submatrix i.succAbove (Fin.last m).castSucc.succAbove =
      affineMatrix (fun j => w (i.succAbove j)) := by
  funext j k
  refine Fin.lastCases ?_ (fun k => ?_) k
  next =>
    simp [paperHeightMatrix, affineMatrix, Matrix.submatrix]
  next =>
    change paperHeightMatrix w t (i.succAbove j)
      ((Fin.last m).castSucc.succAbove k.castSucc) =
      affineMatrix (fun j => w (i.succAbove j)) j k.castSucc
    rw [Fin.succAbove_castSucc_of_lt _ _ (Fin.castSucc_lt_last k)]
    simp [paperHeightMatrix, affineMatrix]

/-- Exact common sign from the manuscript: determinant(W,T,1) =
(-1)^m times the cofactor-height sum. -/
theorem paper_height_determinant {m : Nat}
    (w : Fin (m + 2) -> Point m) (t : Fin (m + 2) -> Real) :
    (paperHeightMatrix w t).det =
      (-1 : Real) ^ m * Finset.sum Finset.univ (fun i => cofactor w i * t i) := by
  rw [Matrix.det_succ_column _ (Fin.last m).castSucc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [paperHeightMatrix_minor]
  simp only [paperHeightMatrix, Fin.lastCases_castSucc, Fin.lastCases_last,
    Fin.val_castSucc, Fin.val_last, pow_add, cofactor, affineDet]
  ring

theorem paper_height_absolute_determinant {m : Nat}
    (w : Fin (m + 2) -> Point m) (t : Fin (m + 2) -> Real) :
    |affineDet (fun i => liftedPoint (w i) (t i))| =
      |Finset.sum Finset.univ (fun i => cofactor w i * t i)| := by
  change |(paperHeightMatrix w t).det| = _
  rw [paper_height_determinant, abs_mul, abs_pow]
  norm_num

theorem firstColumnMatrix_minor {m : Nat}
    (w : Fin (m + 2) -> Point m) (t : Fin (m + 2) -> Real)
    (i : Fin (m + 2)) :
    (firstColumnMatrix w t).submatrix i.succAbove Fin.succ =
      affineMatrix (fun j => w (i.succAbove j)) := by
  funext j k
  simp [firstColumnMatrix, affineMatrix, Matrix.submatrix]

theorem height_first_determinant {m : Nat}
    (w : Fin (m + 2) -> Point m) (t : Fin (m + 2) -> Real) :
    (firstColumnMatrix w t).det =
      Finset.sum Finset.univ (fun i => cofactor w i * t i) := by
  rw [Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [firstColumnMatrix_minor]
  simp only [firstColumnMatrix, Fin.cases_zero, cofactor, affineDet]
  ring

theorem cofactor_sum_zero {m : Nat}
    (w : Fin (m + 2) -> Point m) :
    Finset.sum Finset.univ (cofactor w) = 0 := by
  have hdet : (firstColumnMatrix w (fun _ => 1)).det = 0 := by
    apply Matrix.det_zero_of_column_eq
      (i := (0 : Fin (m + 2))) (j := Fin.last (m + 1))
    case i_ne_j =>
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_last] at hv
      omega
    case hij =>
      intro i
      change (1 : Real) = firstColumnMatrix w (fun _ => 1) i (Fin.last (m + 1))
      unfold firstColumnMatrix
      rw [show Fin.last (m + 1) = (Fin.last m).succ from rfl]
      simp only [Fin.cases_succ, Fin.lastCases_last]
  rw [height_first_determinant] at hdet
  simpa using hdet

theorem cofactor_affine_relation {m : Nat}
    (w : Fin (m + 2) -> Point m) (j : Fin m) :
    Finset.sum Finset.univ (fun i => cofactor w i * w i j) = 0 := by
  have hdet : (firstColumnMatrix w (fun i => w i j)).det = 0 := by
    apply Matrix.det_zero_of_column_eq
      (i := (0 : Fin (m + 2))) (j := j.castSucc.succ)
    case i_ne_j =>
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc] at hv
      omega
    case hij =>
      intro i
      simp [firstColumnMatrix]
  rw [height_first_determinant] at hdet
  exact hdet

theorem cofactor_annihilates_affine_height {m : Nat}
    (w : Fin (m + 2) -> Point m) (a : Real) (b : Point m) :
    Finset.sum Finset.univ
      (fun i => cofactor w i *
        (a + Finset.sum Finset.univ (fun j => b j * w i j))) = 0 := by
  simp_rw [mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  have hconstant : Finset.sum Finset.univ (fun i => cofactor w i * a) = 0 := by
    rw [<- Finset.sum_mul, cofactor_sum_zero]
    simp
  rw [hconstant, zero_add, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  have hpoint (i : Fin (m + 2)) :
      cofactor w i * (b j * w i j) = b j * (cofactor w i * w i j) := by ring
  simp_rw [hpoint]
  rw [<- Finset.mul_sum, cofactor_affine_relation]
  simp

theorem radonMass_nonneg {m : Nat} (w : Fin (m + 2) -> Point m) :
    0 <= radonMass w := by
  unfold radonMass
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => abs_nonneg _))

theorem radonMass_positive_mass {m : Nat} (w : Fin (m + 2) -> Point m) :
    radonMass w = Finset.sum Finset.univ (fun i => max (cofactor w i) 0) := by
  have hpoint (i : Fin (m + 2)) :
      |cofactor w i| = 2 * max (cofactor w i) 0 - cofactor w i := by
    rcases le_total 0 (cofactor w i) with hi | hi
    case inl =>
      rw [abs_of_nonneg hi, max_eq_left hi]
      ring
    case inr =>
      rw [abs_of_nonpos hi, max_eq_right hi]
      ring
  unfold radonMass
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, <- Finset.mul_sum, cofactor_sum_zero]
  ring

theorem radonMass_negative_mass {m : Nat} (w : Fin (m + 2) -> Point m) :
    radonMass w = Finset.sum Finset.univ (fun i => max (-cofactor w i) 0) := by
  have hpoint (i : Fin (m + 2)) :
      |cofactor w i| = 2 * max (-cofactor w i) 0 + cofactor w i := by
    rcases le_total 0 (cofactor w i) with hi | hi
    case inl =>
      rw [abs_of_nonneg hi, max_eq_right (neg_nonpos.mpr hi)]
      ring
    case inr =>
      rw [abs_of_nonpos hi, max_eq_left (neg_nonneg.mpr hi)]
      ring
  unfold radonMass
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, <- Finset.mul_sum, cofactor_sum_zero]
  ring

theorem radonMass_zero_iff {m : Nat} (w : Fin (m + 2) -> Point m) :
    radonMass w = 0 <-> forall i, cofactor w i = 0 := by
  constructor
  next =>
    intro hz i
    have hsum : Finset.sum Finset.univ (fun j => |cofactor w j|) = 0 := by
      unfold radonMass at hz
      linarith
    have hi : |cofactor w i| <= Finset.sum Finset.univ (fun j => |cofactor w j|) := by
      exact Finset.single_le_sum
        (f := fun j => |cofactor w j|)
        (fun j _ => abs_nonneg (cofactor w j)) (Finset.mem_univ i)
    have ha : |cofactor w i| = 0 := by
      rw [hsum] at hi
      exact le_antisymm hi (abs_nonneg _)
    exact abs_eq_zero.mp ha
  next =>
    intro hz
    unfold radonMass
    simp [hz]

theorem affineDet_zero_of_repeated_point {m : Nat}
    (w : Fin (m + 1) -> Point m) {i j : Fin (m + 1)}
    (hij : Not (i = j)) (hw : w i = w j) : affineDet w = 0 := by
  unfold affineDet
  apply Matrix.det_zero_of_row_eq hij
  funext k
  simp [affineMatrix, hw]

/-- The actual geometric convex hull; labels can repeat projected points. -/
def simplexHull {m : Nat} (w : Fin (m + 1) -> Point m) : Set (Point m) :=
  convexHull Real (Set.range w)

/-- Ordinary coordinate Lebesgue volume, not determinant-defined volume. -/
def simplexVolume {m : Nat} (w : Fin (m + 1) -> Point m) : Real :=
  (volume (simplexHull w)).toReal

/-- Real-valued sign with the degenerate orientation equal to zero. -/
def orientation (a : Real) : Real :=
  if 0 < a then 1 else if a < 0 then -1 else 0

/-- This is the paper's h_I, including zero on determinant-zero simplices. -/
def signedSimplex {m : Nat} (w : Fin (m + 1) -> Point m) : Point m -> Real :=
  (simplexHull w).indicator (fun _ => orientation (affineDet w))

theorem simplexHull_compact {m : Nat} (w : Fin (m + 1) -> Point m) :
    IsCompact (simplexHull w) := by
  exact (Set.finite_range w).isCompact_convexHull Real

theorem simplexHull_measurable {m : Nat} (w : Fin (m + 1) -> Point m) :
    MeasurableSet (simplexHull w) := by
  exact (simplexHull_compact w).isClosed.measurableSet

theorem simplexVolume_nonneg {m : Nat} (w : Fin (m + 1) -> Point m) :
    0 <= simplexVolume w := ENNReal.toReal_nonneg

theorem orientation_values (a : Real) :
    Or (orientation a = -1) (Or (orientation a = 0) (orientation a = 1)) := by
  unfold orientation
  split_ifs
  all_goals simp

theorem signedSimplex_values {m : Nat} (w : Fin (m + 1) -> Point m)
    (x : Point m) :
    Or (signedSimplex w x = -1)
      (Or (signedSimplex w x = 0) (signedSimplex w x = 1)) := by
  classical
  simp only [signedSimplex, Set.indicator_apply]
  split_ifs
  next => exact orientation_values _
  next => simp

theorem signedSimplex_degenerate {m : Nat} (w : Fin (m + 1) -> Point m)
    (ha : affineDet w = 0) : signedSimplex w = 0 := by
  funext x
  simp [signedSimplex, ha, orientation]

theorem signedSimplex_repeated_point {m : Nat}
    (w : Fin (m + 1) -> Point m) {i j : Fin (m + 1)}
    (hij : Not (i = j)) (hw : w i = w j) : signedSimplex w = 0 := by
  exact signedSimplex_degenerate w (affineDet_zero_of_repeated_point w hij hw)

theorem signedSimplex_measurable {m : Nat} (w : Fin (m + 1) -> Point m) :
    Measurable (signedSimplex w) := by
  exact measurable_const.indicator (simplexHull_measurable w)

theorem signedSimplex_integrable {m : Nat} (w : Fin (m + 1) -> Point m) :
    Integrable (signedSimplex w) volume := by
  exact (integrableOn_const (simplexHull_compact w).measure_ne_top).integrable_indicator
    (simplexHull_measurable w)

/-- This evaluates the geometric indicator integral; it is not yet the
factorial determinant-volume theorem required by the paper. -/
theorem signedSimplex_integral {m : Nat} (w : Fin (m + 1) -> Point m) :
    MeasureTheory.integral volume (signedSimplex w) =
      simplexVolume w * orientation (affineDet w) := by
  rw [signedSimplex, integral_indicator_const _ (simplexHull_measurable w)]
  rfl

theorem signedSimplex_square {m : Nat} (w : Fin (m + 1) -> Point m)
    (x : Point m) : (signedSimplex w x) ^ 2 = |signedSimplex w x| := by
  rcases signedSimplex_values w x with hx | hx | hx
  all_goals rw [hx]; norm_num

end Hypercube.Geometry
