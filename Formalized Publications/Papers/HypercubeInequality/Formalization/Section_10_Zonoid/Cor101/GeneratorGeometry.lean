import Section_10_Zonoid.Cor101.Definitions
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
The positive-height generator normalization as an equality of actual sets.
This module does not identify any determinant sum with geometric volume.
-/

noncomputable section

namespace Cor101

/-- Append a last coordinate to a projected vector. -/
def appendHeight {d : Nat} (a : Fin d -> Real) (b : Real) : Space d :=
  WithLp.toLp 2 (Fin.snoc a b)

/-- The paper's lifted vector (z,1). -/
def liftPoint {d : Nat} (z : Fin d -> Real) : Space d :=
  appendHeight z 1

/-- Explicit bridge to the coordinate-row convention in the recovered
finite determinant proof. The last matrix column is the height. -/
theorem coordinates_appendHeight {d : Nat} (a : Fin d -> Real) (b : Real) :
    (fun j => appendHeight a b j) = Fin.lastCases b a := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [appendHeight]

/-- Every ambient generator is represented by its first d coordinates
and its last coordinate, with no geometric restriction. -/
theorem appendHeight_coordinates {d : Nat} (g : Space d) :
    appendHeight (fun j : Fin d => g j.castSucc) (g (Fin.last d)) = g := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [appendHeight]

/-- The normalized lifted generator reconstructs the original generator. -/
theorem normalize_generator {d : Nat} (a : Fin d -> Real) (b H : Real)
    (hb : Not (b = 0)) (hH : Not (H = 0)) :
    H • ((b / H) • liftPoint (fun j => a j / b)) = appendHeight a b := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [liftPoint, appendHeight, smul_smul, PiLp.smul_apply,
      Fin.snoc_last, smul_eq_mul, mul_one]
    field_simp
  · simp only [liftPoint, appendHeight, smul_smul, PiLp.smul_apply,
      Fin.snoc_castSucc, smul_eq_mul]
    field_simp

/-- Scalar multiplication commutes with the actual finite Minkowski sum. -/
theorem image_parallelepiped_smul {d N : Nat} (H : Real)
    (v : Fin N -> Space d) :
    (fun x : Space d => H • x) '' parallelepiped v =
      parallelepiped (fun i => H • v i) := by
  exact image_parallelepiped (H • LinearMap.id) v

/-- Set-valued normalization K = H K_nu, before any volume calculation.
Positive generator heights imply the nonzero hypotheses used here.
No injectivity or distinctness of the projected points is required. -/
theorem normalized_zonotope_set {d N : Nat}
    (a : Fin N -> Fin d -> Real) (b : Fin N -> Real) (H : Real)
    (hb : forall i, Not (b i = 0)) (hH : Not (H = 0)) :
    parallelepiped (fun i => appendHeight (a i) (b i)) =
      (fun x : Space d => H • x) ''
        parallelepiped (fun i => (b i / H) •
          liftPoint (fun j => a i j / b i)) := by
  rw [image_parallelepiped_smul]
  congr 1
  funext i
  exact (normalize_generator (a i) (b i) H (hb i) hH).symm

end Cor101
