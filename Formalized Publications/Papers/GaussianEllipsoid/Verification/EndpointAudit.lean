import GaussianEllipsoid.PaperMain
import StrictThresholdProjectFinal
import BelowThresholdProjectFinal
import UniformConicBoundUnconditional
import MixedNormProjectFinal
import BMProjectFinal
import AHHExactEquation11Unconditional

/-!
# Verification-only endpoint audit (NOT the independent challenge file)

This module inspects the solution's own endpoints with `#check` (type
audit) and `#print axioms` (axiom audit). It imports the solution
(`Formalization/`), by design: it verifies the checked-in statements
have the expected types and depend only on the standard axioms. It does
NOT independently restate the paper, so a passing run never by itself
proves the Lean sources say what the paper says — that link is carried
by `Papers/inventory.json` (all 48 assertion rows) together with
`Verification/inventory.json`, whose declaration bindings the
generator checks verbatim against `Formalization/`.

The independent Atlas-style challenge is
`../Comparator/gaussian_ellipsoid_comparator.lean` (with its
`gaussian_ellipsoid_comparator.json` config): it restates the
paper-facing definitions under the same names importing only Mathlib,
with the main theorem proved by `sorry`, and the official
`lake comparator` judges the solution against it. This file is the
complementary endpoint audit, not that challenge.

No `sorry`, `admit`, `native_decide`, custom axiom, or `unsafe` appears
here or anywhere in the solution.

Run from a scratch Lake assembly whose source root holds
`GaussianEllipsoid.lean`, `GaussianEllipsoid/` and
`GaussianEllipsoidNative/` with the pins in `../Readme.md`:

```sh
lake exe cache get && lake build
lake env lean Verification/EndpointAudit.lean
```

Expected: exit 0; every endpoint below depends only on `propext`,
`Classical.choice` and `Quot.sound`.
-/

noncomputable section

namespace GaussianEllipsoid

-- Headline: the strict-threshold theorem, unconditionally proved.
/-! The paper's Theorem 1.1 as a single unconditional proposition. -/
#check @strict_threshold_unconditional
#check (strict_threshold_unconditional : StrictThresholdStatement)
#print axioms strict_threshold_unconditional

-- Below-threshold direction (Theorem 1.1(i)).
#check (below_threshold_unconditional : BelowThresholdStatement)
#print axioms below_threshold_unconditional

-- Interface discharges feeding the endpoint.
#check (mixedNormBound_unconditional : MixedNormBound)
#print axioms mixedNormBound_unconditional
#check (bmApproximateFitting_unconditional : bmApproximateFitting)
#print axioms bmApproximateFitting_unconditional
#check (uniformConicBound_unconditional : UniformConicBound)
#print axioms uniformConicBound_unconditional

-- Supplemental AHH endpoint: the unconditional equation (11).
#check @AHHRadial.paper_equation11
#print axioms AHHRadial.paper_equation11

end GaussianEllipsoid
