/-
Kernel-checked coordinate bridges between mathlib PSD/PD predicates and paper coordinates.
Mathematical source: paper.tex, Section 2.
-/
import GaussianEllipsoid.Basic
import Mathlib.Analysis.RCLike.Basic

noncomputable section

namespace GaussianEllipsoid

/-- Draft: the matrix expression agrees with its double coordinate sum. -/
theorem quadratic_eq_sum {d : Nat} (S : Square d) (x : Vector d) :
    quadratic S x = Finset.univ.sum (fun i =>
      x i * Finset.univ.sum (fun j => S i j * x j)) := rfl

/-- Draft: real Hermitian matrices are exactly real symmetric matrices. -/
theorem hermitian_iff_symmetric {d : Nat} (S : Square d) :
    S.IsHermitian <-> S.IsSymm := Matrix.isHermitian_iff_isSymm

/-- Draft: mathlib's PSD predicate has the literal quadratic-form meaning. -/
theorem posSemidef_iff_coordinates {d : Nat} (S : Square d) :
    S.PosSemidef <-> S.IsSymm /\ forall v : Vector d, 0 <= quadratic S v := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  simp [quadratic]

/-- Draft: mathlib's PD predicate has the literal strict quadratic-form meaning. -/
theorem posDef_iff_coordinates {d : Nat} (S : Square d) :
    S.PosDef <-> S.IsSymm /\ forall v : Vector d, Not (v = 0) -> 0 < quadratic S v := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  simp [quadratic]

/-- Draft: feasibility is exactly the paper's symmetric PSD coordinate condition. -/
theorem feasible_iff_paper_coordinates {d n : Nat} (x : Sample d n) (S : Square d) :
    Feasible x S <->
      (S.IsSymm /\ forall v : Vector d, 0 <= quadratic S v) /\
      (forall i : Fin n, quadratic S (x i) = (d : Real)) := by
  rw [Feasible, posSemidef_iff_coordinates]

/-- Draft: the quadratic measurement is linear in the matrix argument. -/
theorem quadratic_smul {d : Nat} (c : Real) (S : Square d) (v : Vector d) :
    quadratic (c • S) v = c * quadratic S v := by
  simp only [quadratic, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- Draft: a positive common measurement can be scaled to the exact target `d`. -/
theorem feasible_of_positive_common_value {d n : Nat}
    {x : Sample d n} {S : Square d} {c : Real}
    (hS : S.PosSemidef) (hc : 0 < c)
    (hcommon : forall i, quadratic S (x i) = c) :
    Feasible x (((d : Real) / c) • S) := by
  have : StarOrderedRing ℝ := RCLike.toStarOrderedRing
  constructor
  case left =>
    apply hS.smul
    exact div_nonneg (by positivity) hc.le
  case right =>
    intro i
    rw [quadratic_smul, hcommon i]
    field_simp [ne_of_gt hc]

/-- Draft: the same rescaling preserves positive definiteness. -/
theorem strictlyFeasible_of_positive_common_value {d n : Nat} (hd : 0 < d)
    {x : Sample d n} {S : Square d} {c : Real}
    (hS : S.PosDef) (hc : 0 < c)
    (hcommon : forall i, quadratic S (x i) = c) :
    StrictlyFeasible x (((d : Real) / c) • S) := by
  have : StarOrderedRing ℝ := RCLike.toStarOrderedRing
  constructor
  case left =>
    apply hS.smul
    exact div_pos (by exact_mod_cast hd) hc
  case right =>
    intro i
    rw [quadratic_smul, hcommon i]
    field_simp [ne_of_gt hc]

/-- Draft: centering subtracts the coordinate mean exactly. -/
theorem center_eq_zero_iff_mean {n : Nat} (v : Vector n) :
    center v = 0 <-> forall i, v i = mean v := by
  constructor
  case mp =>
    intro h i
    have hi := congrFun h i
    exact sub_eq_zero.mp hi
  case mpr =>
    intro h
    funext i
    exact sub_eq_zero.mpr (h i)

/-- Draft: the mean of a constant vector is that constant for a nonempty sample. -/
theorem mean_const {n : Nat} (hn : 0 < n) (c : Real) :
    mean (fun _ : Fin n => c) = c := by
  have hnR : Not ((n : Real) = 0) := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [mean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hnR]

/-- Draft: adding a constant to every coordinate adds it to the mean. -/
theorem mean_add_const {n : Nat} (hn : 0 < n) (v : Vector n) (c : Real) :
    mean (fun i => v i + c) = mean v + c := by
  have hnR : Not ((n : Real) = 0) := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [mean, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp [hnR]

/-- Draft: adding a constant vector does not change the centered vector. -/
theorem center_add_const {n : Nat} (hn : 0 < n) (v : Vector n) (c : Real) :
    center (fun i => v i + c) = center v := by
  funext i
  simp only [center, mean_add_const hn]
  ring

/-- Draft: centering commutes with division by a scalar, including zero. -/
theorem center_div {n : Nat} (v : Vector n) (c : Real) :
    center (fun i => v i / c) = fun i => center v i / c := by
  funext i
  simp only [center, mean, <- Finset.sum_div]
  ring

/-- Draft: the centered residual agrees with the paper's operator `T_d`. -/
theorem center_residual_eq_measurementT {d n : Nat} (hn : 0 < n)
    (x : Sample d n) (S : Square d) :
    center (residual x S) = measurementT x S := by
  unfold residual
  rw [center_div]
  have hc := center_add_const hn (measurementA x S) (-(d : Real))
  simp only [measurementA] at hc
  funext i
  change center (fun j => quadratic S (x j) - (d : Real)) i /
      Real.sqrt (d : Real) = _
  rw [show center (fun j => quadratic S (x j) - (d : Real)) =
      center (measurementA x S) by simpa [measurementA, sub_eq_add_neg] using hc]
  rfl

/-- Draft: the centered `Q_d` is the centered `A_d` divided by sqrt(2). -/
theorem center_measurementQ {d n : Nat} (hn : 0 < n)
    (x : Sample d n) (S : Square d) :
    center (measurementQ x S) =
      fun i => center (measurementA x S) i / Real.sqrt 2 := by
  unfold measurementQ
  rw [center_div]
  have hc := center_add_const hn (measurementA x S) (-Matrix.trace S)
  have he : center (fun j => quadratic S (x j) - Matrix.trace S) =
      center (measurementA x S) := by
    simpa [measurementA, sub_eq_add_neg] using hc
  rw [he]

end GaussianEllipsoid
