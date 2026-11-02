# Comparator — independent challenge for the Gaussian Ellipsoid strict threshold

Independent Atlas-style challenge for the Gaussian Ellipsoid paper
(Paper Theorem 1.1, `GaussianEllipsoid.strict_threshold_unconditional`:
the strict-threshold conjunction of both threshold directions).

## What is checked

`gaussian_ellipsoid_comparator.lean` states the paper-facing
definitions **independently in the challenge file** — it imports only
Mathlib, never the solution in `Formalization/` — and states
`GaussianEllipsoid.strict_threshold_unconditional` with those
challenge definitions, proved with `sorry`. `sorry` is authorized in
this challenge file only (exactly one placeholder); the solution
contains no `sorry`, `admit`, `native_decide`, or custom axioms.

Restated definitions (same names, same bodies as the solution):

- From `Formalization/GaussianEllipsoid/Basic.lean`: `Vector`,
  `Square`, `Sample`, `dimensionRatio`, `quadratic`, `Feasible`,
  `StrictlyFeasible`, `HasFit`, `HasStrictFit`.
- From `Formalization/GaussianEllipsoid/GaussianProbability.lean`:
  `gaussianVectorLaw` (finite coordinate product law),
  `gaussianSampleLaw` (finite row product law).
- From `Formalization/GaussianEllipsoid/PaperMain.lean`: `fitEvent`,
  `strictFitEvent`, `fitProbability`, `strictFitProbability`,
  `BelowThresholdStatement`, `AboveThresholdStatement`,
  `StrictThresholdStatement` (the conjunction).

`gaussian_ellipsoid_comparator.json`:

- `theorem_names`: `["GaussianEllipsoid.strict_threshold_unconditional"]`
- `definition_names`: `[]` (deliberately empty — see below)
- `permitted_axioms`: `["propext", "Classical.choice", "Quot.sound"]`
  (never `sorryAx`)
- `challenge_module`: `gaussian_ellipsoid_comparator`,
  `solution_module`: `GaussianEllipsoid`

## Why `definition_names` is empty (fixed definitions, not holes)

In the comparator, every name in `definition_names` is a definition
*HOLE*: only the name, type signature, and safety are compared —
the body is deliberately skipped. Registering the restated definitions
as holes would therefore check signatures only, and a wrong body with
the right type would still pass. Since they are explicitly and
independently defined here to mean the paper's literal objects, they
must NOT be holes: with `definition_names` empty, all of them are
traversed from the theorem as ordinary fixed constants and compared by
full structural equality, bodies included, recursively.

## Toolchain route (original pin, no source port)

The solution is pinned to Lean `v4.34.0-rc2` with mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`; that toolchain has no
`leanexport`/comparator. No 771-module source port was performed.
Instead both sides are elaborated under the original pin and serialized
to NDJSON with the faithful 4.34 serializer
(`../Verification/export34.lean`, external support, never imported by
the challenge), which replicates the official 4.35 `LeanExport`
format 3.1.0 field-for-field (all `ConstantInfo` bodies, safety flags,
hints, universes, inductive/ctor/recursor structure; `unsafe` is
skipped, never trusted; anything unrepresentable is a hard refusal).
The serializer's own entry point is `unsafe` only because environment
loading is an unsafe IO operation; that unsafety lives entirely in
this external export utility — never in the challenge or the
solution — and its output is untrusted data re-parsed and
kernel-checked by the official judge.
The official 4.35 `lake comparator` (default kernel, `bwrap` sandbox)
then judges those exports as untrusted data. Nothing here is claimed
to be a 4.35 source port, and no 4.34 olean is ever loaded into a
4.35 process.

Serializer parity: a Lean-core-only fixture
(`../Verification/parity_fixture.lean`, compilable under both
toolchains with no Mathlib) is exported by the official 4.35
`leanexport` and by the 4.34 serializer: all 9 fixture-module
constants match exactly (types and full bodies), and each side's
export is accepted by the official kernel (see
`../Verification/parity.md`). The only closure-wide divergence is an
upstream 4.34 → 4.35 core change (`And.casesOn`), which the
comparator correctly flags — evidence the comparison is
body-sensitive.
One known upstream boundary, found during validation and avoided by
the fixture: a theorem whose proof needs kernel defeq through
`String.append`/ByteArray computation makes the official replay
demand `String.ofList` although no exported term references it; plain
string literals are unaffected. The Gaussian proof (pure analysis,
no string computation) does not touch that path.

## Actual runs

Pins: Lean `v4.34.0-rc2`
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0` for elaboration and both
exports; judge: Lean `v4.35.0` (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`)
with `bwrap` sandbox active and default kernels.

Export bindings (sha256; generated from the compiled sources by the
4.34 serializer commands below and verified after transfer):

- challenge source `gaussian_ellipsoid_comparator.lean`:
  `4884c3d6b5ddc5c21017c1d749ccf86c2783964a8f49faadc67a4169edb8849c`
- `challenge.ndjson`:
  `8a544feeee9c91b7221461cf349e10c8ceb3c9f11e401994ba5b263e80bdd56c`
  (2,840,156 lines; exactly one `sorryAx` axiom declaration, the
  authorized placeholder)
- solution olean set: 771 rev-matched prebuilt oleans (770 modules +
  root; read-only stage), bound to the byte-identity ledger
  `Formalization/SOURCES_SHA256.txt` (checked by
  `Formalization/check_preservation.py`)
- `solution.ndjson`:
  `4ff28fe22884a88bb75201a3d5bc2a3396cac8932d1dfdc0f737fe4b72dbdf34`
  (11,496,715 lines; zero `sorryAx`)

The real `lake comparator` ran on Linux from those exports:

```sh
lake comparator --config gaussian_ellipsoid_comparator.json \
  --challenge-from-export challenge.ndjson \
  --solution-from-export solution.ndjson
# Running Lean default kernel on solution
# Lean default kernel accepts the solution
# Your solution is okay!
# EXIT: 0
```

Strict verdict: the solution proves the challenge statement with
definitions whose full bodies match the independent challenge
bodies, on the standard axioms only, accepted by the kernel.

## Negative controls (same `lake comparator`, same Linux host)

All run from recompiled sources in isolated scratch (never in
`Formalization/`); each is expected to be REJECTED (nonzero exit).
No control edits NDJSON directly.

| Control | Tamper (recompiled from challenge source) | Result (actual) |
|---|---|---|
| N-def-fit | `fitEvent := Set.univ` (same type, different body) | REJECT, exit 1: `Const does not match between challenge and target 'GaussianEllipsoid.fitEvent'` (direct body mismatch) |
| N-def-quad | `quadratic` with swapped `dotProduct` arguments (same type, different body) | REJECT, exit 1: `Const does not match between challenge and target 'GaussianEllipsoid.quadratic'` (direct body mismatch) |
| N-thm | threshold `1/4` → `1/3` in `BelowThresholdStatement` | REJECT, exit 1: `Const does not match between challenge and target 'GaussianEllipsoid.AboveThresholdStatement'` (Below's value differs `4` vs `3` directly; elaboration reshuffles a shared aux-proof name into Above's reference, and the first traversed mismatch is reported) |
| N-sorry | sorry-proved theorem judged as the solution | REJECT, exit 1: `Illegal axiom detected: 'sorryAx'` |

N-def-fit and N-def-quad are the genuine semantic checks: same name,
same type, different body — rejected under the strict (empty-hole)
configuration. (A `quadratic := 0` variant is likewise rejected at
the first traversed mismatch, `fitEvent`, whose unfolding-height
(`regular` 28 → 26) shifts when `quadratic`'s body collapses; the
swapped-argument variant above isolates the direct hit on
`quadratic`.) Together the controls evidence sensitivity to the
statement, the required definitions' bodies, and proof admissions.

## Reproducing

Assemble a scratch 4.34 Lake project whose library `GaussianEllipsoid`
holds `GaussianEllipsoid.lean`, `GaussianEllipsoid/` and
`GaussianEllipsoidNative/` from `Formalization/` with the pins in
`../Readme.md`, then run [reproduce.sh](reproduce.sh) with that
project root and a scratch dir; on Linux+bwrap it executes the full
chain (challenge compile with exactly one `sorry`, both 4.34 exports,
official judge) and reports every step's real exit code. A
compilation, export, or comparison failure stops the script with a
nonzero exit; a platform without Linux+bwrap prints the exact command
and exits 2, not a passing verdict. Set `LEAN34` and `LAKE34` to the
original compiler tools and, on Linux, `LAKE35` and `LEAN35` to the
colocated official judge tools. The driver checks both version strings
and compiler commit hashes, validates the exact dependency manifest,
and excludes all project outputs and unlisted packages from the
challenge's search path.

`guard_inputs.py` recognizes indented and `public import` lines, masks
nested comments and strings, and requires exactly the main theorem and
its single placeholder. Names that merely start with `Mathlib` are not
accepted as external imports. Every named definition remains fixed;
no definition holes or additional permitted axioms can be introduced
through the config.

Driver error handling is tested separately with stub executables:
`python3 test_reproduce.py` (these tests are not Lean proof checks).
Failures of version commands, compilation, either export, comparison,
missing tools, changed pins, hidden project-package paths and invalid
imports all return nonzero. The end-to-end proof verdict above comes
from the actual exported environments and the official Linux judge,
not from stub tests. The portable driver is supplied for reproduction;
Lake workspace loading still fails on this particular Mac, so the
recorded compile/export run used the original pinned direct-Lean route.
