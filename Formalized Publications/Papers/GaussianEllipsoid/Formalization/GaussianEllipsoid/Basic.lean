/-
Copyright (c) 2026 Aykut Arslan. All rights reserved.

Kernel-checked coordinate definitions and restriction bridges.
The mathematical source is paper.tex, Sections 1 and 2.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic

noncomputable section

namespace GaussianEllipsoid

/-- Real coordinate vectors in the paper's dimension `d`. -/
abbrev Vector (d : Nat) := Fin d -> Real

/-- Real square matrices. Symmetry is required by the feasibility predicates. -/
abbrev Square (d : Nat) := Matrix (Fin d) (Fin d) Real

/-- The `n` observed points in dimension `d`, with indices numbered from zero. -/
abbrev Sample (d n : Nat) := Fin n -> Vector d

/-- Extended nonnegative ratio, so unbounded sequences are not silently excluded.
The value at dimension zero does not affect an `atTop` statement.
The equivalence with the manuscript's limsup/liminf convention remains unproved. -/
def dimensionRatio (n : Nat -> Nat) (d : Nat) : ENNReal :=
  (n d : ENNReal) / (d : ENNReal) ^ 2

/-- The literal coordinate quadratic measurement `x^T S x`. -/
def quadratic {d : Nat} (S : Square d) (x : Vector d) : Real :=
  dotProduct x (Matrix.mulVec S x)

/-- The uncentered measurement operator from Section 2. -/
def measurementA {d n : Nat} (x : Sample d n) (S : Square d) : Vector n :=
  fun i => quadratic S (x i)

/-- The centered rank-one measurement operator with the paper's normalization. -/
def measurementQ {d n : Nat} (x : Sample d n) (S : Square d) : Vector n :=
  fun i => (quadratic S (x i) - Matrix.trace S) / Real.sqrt 2

/-- The residual vector, normalized by the square root of the dimension. -/
def residual {d n : Nat} (x : Sample d n) (S : Square d) : Vector n :=
  fun i => (quadratic S (x i) - (d : Real)) / Real.sqrt (d : Real)

/-- Arithmetic mean. The theorems requiring a nonempty sample assume `0 < n`. -/
def mean {n : Nat} (v : Vector n) : Real :=
  (Finset.univ.sum fun i => v i) / (n : Real)

/-- Application of the paper's centering projector to a coordinate vector. -/
def center {n : Nat} (v : Vector n) : Vector n :=
  fun i => v i - mean v

/-- The paper's centering matrix `I_n - (1/n) 1_n 1_n^T`. -/
def centeringMatrix (n : Nat) : Square n :=
  1 - ((1 / (n : Real)) • (Matrix.of fun _ _ => (1 : Real)))

/-- The centered measurement operator `T_d`. -/
def measurementT {d n : Nat} (x : Sample d n) (S : Square d) : Vector n :=
  fun i => center (measurementA x S) i / Real.sqrt (d : Real)

/-- The sample Gram sum `sum_i x_i x_i^T`. -/
def gram {d n : Nat} (x : Sample d n) : Square d :=
  Finset.univ.sum fun i => Matrix.vecMulVec (x i) (x i)

/-- The formula for `T_d^* y` when `sum_i y_i = 0`. -/
def centeredAdjoint {d n : Nat} (x : Sample d n) (y : Vector n) : Square d :=
  (1 / Real.sqrt (d : Real)) •
    (Finset.univ.sum fun i => (y i) • (Matrix.vecMulVec (x i) (x i)))

/-- Membership in the paper's feasible set `F_d`.
Mathlib's `PosSemidef` already includes symmetry over the real numbers. -/
def Feasible {d n : Nat} (x : Sample d n) (S : Square d) : Prop :=
  S.PosSemidef /\ forall i, quadratic S (x i) = (d : Real)

/-- A positive definite fit, as required in the lower-threshold conclusion. -/
def StrictlyFeasible {d n : Nat} (x : Sample d n) (S : Square d) : Prop :=
  S.PosDef /\ forall i, quadratic S (x i) = (d : Real)

/-- The positive semidefinite fitting event. -/
def HasFit {d n : Nat} (x : Sample d n) : Prop :=
  exists S : Square d, Feasible x S

/-- The positive definite fitting event. -/
def HasStrictFit {d n : Nat} (x : Sample d n) : Prop :=
  exists S : Square d, StrictlyFeasible x S

/-- Draft: positive definiteness implies positive semidefiniteness. -/
theorem StrictlyFeasible.feasible {d n : Nat} {x : Sample d n} {S : Square d}
    (h : StrictlyFeasible x S) : Feasible x S :=
  And.intro h.1.posSemidef h.2

/-- Draft: a strict fit is a fit. -/
theorem HasStrictFit.hasFit {d n : Nat} {x : Sample d n}
    (h : HasStrictFit x) : HasFit x := by
  exact Exists.elim h (fun S hS => Exists.intro S hS.feasible)

/-- Draft: selecting observations preserves each positive semidefinite fit.
The index map need not be injective; repeated observations impose no new constraint. -/
theorem Feasible.restrict {d n m : Nat} {x : Sample d n} {S : Square d}
    (h : Feasible x S) (f : Fin m -> Fin n) :
    Feasible (fun i => x (f i)) S :=
  And.intro h.1 (fun i => h.2 (f i))

/-- Draft: selecting observations preserves each positive definite fit. -/
theorem StrictlyFeasible.restrict {d n m : Nat} {x : Sample d n} {S : Square d}
    (h : StrictlyFeasible x S) (f : Fin m -> Fin n) :
    StrictlyFeasible (fun i => x (f i)) S :=
  And.intro h.1 (fun i => h.2 (f i))

/-- Draft: feasibility is monotone under discarding observations. -/
theorem HasFit.restrict {d n m : Nat} {x : Sample d n}
    (h : HasFit x) (f : Fin m -> Fin n) : HasFit (fun i => x (f i)) := by
  exact Exists.elim h (fun S hS => Exists.intro S (hS.restrict f))

/-- Draft: strict feasibility is monotone under discarding observations. -/
theorem HasStrictFit.restrict {d n m : Nat} {x : Sample d n}
    (h : HasStrictFit x) (f : Fin m -> Fin n) :
    HasStrictFit (fun i => x (f i)) := by
  exact Exists.elim h (fun S hS => Exists.intro S (hS.restrict f))

/-- Draft: a fit in positive dimension and with an observation is nonzero. -/
theorem Feasible.ne_zero {d n : Nat} {x : Sample d n} {S : Square d}
    (hd : 0 < d) (hn : 0 < n) (h : Feasible x S) : Not (S = 0) := by
  intro hzero
  have hi := h.2 (Fin.mk 0 hn)
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hd
  have hi0 : (0 : Real) = (d : Real) := by
    simpa [hzero, quadratic] using hi
  linarith

end GaussianEllipsoid
