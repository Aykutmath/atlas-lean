/-
Copyright (c) 2026 Aykut Arslan. All rights reserved.

Independent challenge restatement for the comparator (see
`gaussian_ellipsoid_comparator.json`). The definitions below restate, under
the same names, the paper-facing definitions from:

`Formalization/GaussianEllipsoid/Basic.lean`
(`GaussianEllipsoid.Vector`, `GaussianEllipsoid.Square`,
`GaussianEllipsoid.Sample`, `GaussianEllipsoid.dimensionRatio`,
`GaussianEllipsoid.quadratic`, `GaussianEllipsoid.Feasible`,
`GaussianEllipsoid.StrictlyFeasible`, `GaussianEllipsoid.HasFit`,
`GaussianEllipsoid.HasStrictFit`),
`Formalization/GaussianEllipsoid/GaussianProbability.lean`
(`GaussianEllipsoid.gaussianVectorLaw`,
`GaussianEllipsoid.gaussianSampleLaw`), and
`Formalization/GaussianEllipsoid/PaperMain.lean`
(`GaussianEllipsoid.fitEvent`, `GaussianEllipsoid.strictFitEvent`,
`GaussianEllipsoid.fitProbability`, `GaussianEllipsoid.strictFitProbability`,
`GaussianEllipsoid.BelowThresholdStatement`,
`GaussianEllipsoid.AboveThresholdStatement`,
`GaussianEllipsoid.StrictThresholdStatement`).
-/
import Mathlib

/-!
# Comparator challenge: Gaussian ellipsoid strict threshold

Challenge module for the comparator (see
`gaussian_ellipsoid_comparator.json`). The definitions below are stated
independently in this file, by design: they must NOT be imported from
the solution (`Formalization/`), otherwise changing a solution
definition would change both sides of the comparison and the
comparator would certify nothing about the definitions themselves.
They duplicate the paper-facing definitions of the solution under the
same names with the same bodies, arrived at from the mathematics of the
paper (Paper Theorem 1.1, the strict-threshold theorem: below `1/4` a
positive definite fit exists with probability tending to one; above
`1/4` no PSD fit exists with probability tending to one).

The theorem is the paper-facing result (Paper Theorem 1.1, recorded as
the conjunction `StrictThresholdStatement` of both threshold
directions), stated with these challenge definitions and proved with
`sorry` here; the comparator checks that the solution proves the same
statement (and carries definitions with the same names, types, and
full bodies) with only the permitted axioms.

Comparison semantics (see the comparator source): every name in
`definition_names` in the JSON config is a definition *HOLE* — only the
name, type signature, and safety are compared, while the body is
deliberately skipped. `definition_names` is therefore deliberately
empty here: all definitions referenced from the theorem are compared as
fixed constants with full structural equality of their bodies,
recursively. Listing any of them as a hole would weaken the check to
signatures only, so a wrong body with the right type would still pass.

`sorry` is authorized in this challenge file only (the single
placeholder for `strict_threshold_unconditional`). The solution
(`Formalization/`) contains no `sorry`, `admit`, `native_decide`,
custom axioms, or `unsafe`.
-/

set_option autoImplicit false

noncomputable section

namespace GaussianEllipsoid

/-- Challenge copy of `GaussianEllipsoid.Vector`: real coordinate vectors
in the paper's dimension `d`. -/
abbrev Vector (d : Nat) := Fin d -> Real

/-- Challenge copy of `GaussianEllipsoid.Square`: real square matrices.
Symmetry is required by the feasibility predicates. -/
abbrev Square (d : Nat) := Matrix (Fin d) (Fin d) Real

/-- Challenge copy of `GaussianEllipsoid.Sample`: the `n` observed points
in dimension `d`, with indices numbered from zero. -/
abbrev Sample (d n : Nat) := Fin n -> Vector d

/-- Challenge copy of `GaussianEllipsoid.dimensionRatio`: extended
nonnegative ratio, so unbounded sequences are not silently excluded.
The value at dimension zero does not affect an `atTop` statement. -/
def dimensionRatio (n : Nat -> Nat) (d : Nat) : ENNReal :=
  (n d : ENNReal) / (d : ENNReal) ^ 2

/-- Challenge copy of `GaussianEllipsoid.quadratic`: the literal coordinate
quadratic measurement `x^T S x`. -/
def quadratic {d : Nat} (S : Square d) (x : Vector d) : Real :=
  dotProduct x (Matrix.mulVec S x)

/-- Challenge copy of `GaussianEllipsoid.Feasible`: membership in the
paper's feasible set `F_d`. Mathlib's `PosSemidef` already includes
symmetry over the real numbers. -/
def Feasible {d n : Nat} (x : Sample d n) (S : Square d) : Prop :=
  S.PosSemidef /\ forall i, quadratic S (x i) = (d : Real)

/-- Challenge copy of `GaussianEllipsoid.StrictlyFeasible`: a positive
definite fit, as required in the lower-threshold conclusion. -/
def StrictlyFeasible {d n : Nat} (x : Sample d n) (S : Square d) : Prop :=
  S.PosDef /\ forall i, quadratic S (x i) = (d : Real)

/-- Challenge copy of `GaussianEllipsoid.HasFit`: the positive
semidefinite fitting event. -/
def HasFit {d n : Nat} (x : Sample d n) : Prop :=
  exists S : Square d, Feasible x S

/-- Challenge copy of `GaussianEllipsoid.HasStrictFit`: the positive
definite fitting event. -/
def HasStrictFit {d n : Nat} (x : Sample d n) : Prop :=
  exists S : Square d, StrictlyFeasible x S

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Challenge copy of `GaussianEllipsoid.gaussianVectorLaw`: standard
Gaussian coordinates on the actual vector space used by the paper. -/
def gaussianVectorLaw (d : Nat) : Measure (Vector d) :=
  Measure.pi (fun _ : Fin d => gaussianReal 0 1)

/-- Challenge copy of `GaussianEllipsoid.gaussianSampleLaw`: independent
Gaussian rows, with the exact finite sample indexing. -/
def gaussianSampleLaw (d n : Nat) : Measure (Sample d n) :=
  Measure.pi (fun _ : Fin n => gaussianVectorLaw d)

/-- Challenge copy of `GaussianEllipsoid.fitEvent`: the PSD feasibility
event, with no measurability assumption inserted. -/
def fitEvent (d n : Nat) : Set (Sample d n) :=
  {x | HasFit x}

/-- Challenge copy of `GaussianEllipsoid.strictFitEvent`: the PD
feasibility event. -/
def strictFitEvent (d n : Nat) : Set (Sample d n) :=
  {x | HasStrictFit x}

/-- Challenge copy of `GaussianEllipsoid.fitProbability`: real-valued
probability expression for positive semidefinite feasibility. -/
def fitProbability (d n : Nat) : Real :=
  (gaussianSampleLaw d n (fitEvent d n)).toReal

/-- Challenge copy of `GaussianEllipsoid.strictFitProbability`:
real-valued probability expression for positive definite feasibility. -/
def strictFitProbability (d n : Nat) : Real :=
  (gaussianSampleLaw d n (strictFitEvent d n)).toReal

/-- Challenge copy of `GaussianEllipsoid.BelowThresholdStatement`:
statement target for Theorem 1.1(i). This is a definition of a
proposition, not a theorem or an assumption. -/
def BelowThresholdStatement : Prop :=
  forall n : Nat -> Nat,
    (forall d : Nat, 0 < n d) ->
    Filter.limsup (dimensionRatio n) Filter.atTop < (1 / 4 : ENNReal) ->
    Filter.Tendsto (fun d => strictFitProbability d (n d))
      Filter.atTop (nhds (1 : Real))

/-- Challenge copy of `GaussianEllipsoid.AboveThresholdStatement`:
statement target for Theorem 1.1(ii). This is a definition of a
proposition, not a theorem or an assumption. -/
def AboveThresholdStatement : Prop :=
  forall n : Nat -> Nat,
    (forall d : Nat, 0 < n d) ->
    (1 / 4 : ENNReal) < Filter.liminf (dimensionRatio n) Filter.atTop ->
    Filter.Tendsto (fun d => fitProbability d (n d))
      Filter.atTop (nhds (0 : Real))

/-- Challenge copy of `GaussianEllipsoid.StrictThresholdStatement`:
conjunction corresponding to both strict-threshold directions (Paper
Theorem 1.1). No endpoint assertion is included here; the placeholder
below stands in for the proof. -/
def StrictThresholdStatement : Prop :=
  BelowThresholdStatement /\ AboveThresholdStatement

/-- Challenge copy of `GaussianEllipsoid.strict_threshold_unconditional`
(Paper Theorem 1.1): the paper's actual strict-threshold proposition,
proved with `sorry` here and checked against the solution's genuine
unconditional proof by the comparator. -/
theorem strict_threshold_unconditional : StrictThresholdStatement := by
  sorry

end GaussianEllipsoid
