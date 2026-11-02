/-
Copyright (c) 2026 Aykut Arslan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aykut Arslan

Portions of this file restate, under the same names, the definitions and the
statement from:

`Formalization/Section_1_Introduction/Core.lean`
(`HypercubeInequality.S`, `HypercubeInequality.gap`) and
`Formalization/Section_7_Approximation/Approx.lean`
(`HypercubeInequality.main_full`).
-/
import Mathlib

/-!
# Comparator challenge: hypercube inequality

Challenge module for the comparator (see
`hypercube_inequality_comparator.json`). The definitions below are stated
independently in this file, by design: they must NOT be imported from
the solution (`Formalization/`), otherwise changing a solution
definition would change both sides of the comparison and the
comparator would certify nothing about the definitions themselves.
They duplicate the paper-facing definitions of the solution under the
same names, and every one of them is enumerated in `definition_names`
in the JSON config. The theorem is the paper-facing result (Paper
Theorem 1.1, the random-simplex inequality with no moment hypothesis),
stated with these challenge definitions and proved with `sorry` here;
the comparator checks that the solution proves the same statement (and
carries definitions with the same names and signatures) with only the
permitted axioms.

`sorry` is authorized in this challenge file only. The solution
(`Formalization/`) contains no `sorry`, `admit`, `native_decide`, or
custom axioms.
-/

namespace HypercubeInequality

open MeasureTheory Measure Finset Filter
open scoped ENNReal NNReal BigOperators Nat Topology

/-- Challenge copy of `HypercubeInequality.S`: simplex functional `S_d(ν)`
(§1 Eq.(1)), the expected `d`-volume of the convex hull of `d+1`
independent samples with law `ν`, as a lower Lebesgue integral. -/
noncomputable def S (d : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ∫⁻ Z, volume (convexHull ℝ (Set.range Z))
    ∂(Measure.pi (fun _ : Fin (d + 1) => ν))

/-- Challenge copy of `HypercubeInequality.gap`: coordinate gap `D_j(ν)`
(§1 Eq.(2)), the mean absolute difference of the `j`th coordinates of
two independent samples with law `ν`. -/
noncomputable def gap {d : ℕ} (j : Fin d)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ∫⁻ p, (‖p.1 j - p.2 j‖₊ : ℝ≥0∞) ∂(ν.prod ν)

/-- Challenge copy of `HypercubeInequality.main_full` (Paper Theorem 1.1):
the random-simplex inequality with no moment hypothesis — zero gaps force
`S = 0`, infinite gaps make the RHS `∞`. -/
theorem main_full (m : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin (m + 1))))
    [IsProbabilityMeasure ν] :
    S (m + 1) ν
    ≤ ENNReal.ofReal (((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1)))
      * ∏ j : Fin (m + 1), gap j ν := by
  sorry

end HypercubeInequality
