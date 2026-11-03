# Comparator — independent challenge for the Alpha-Cycle sharp classification

Independent Atlas-style challenge for the Alpha-Cycle paper
(Paper Theorem 2.4, `AlphaCycle.PaperHypergraph.paper_sharp_classification`:
the sharp-classification conjunction of both relaxations — the
distinguished-cycle relaxation and the all-cycles relaxation each equal
the completed polytope if and only if every pair-only block is a
singleton).

## What is checked

`alpha_cycle_comparator.lean` is the challenge root; the paper-facing
definitions are stated **independently in the `Challenge/` excerpt
modules** — they import only Mathlib and each other, never the solution
in `Formalization/` — and the root states
`AlphaCycle.PaperHypergraph.paper_sharp_classification` with those
challenge definitions, proved with `sorry`. `sorry` is authorized in
this challenge only (exactly one placeholder, in
`Challenge/Section_6_MainTheorem/PaperMain.lean`); the solution
contains no `sorry`, `admit`, `native_decide`, or custom axioms.

Restated definitions (same names, same bodies as the solution;
byte-identical source excerpts, elaborated file-by-file in dependency
order exactly like the solution build):

- From `Section_1_Introduction/Geometry.lean` (embedded whole):
  `blockA`, `blockB`, `blockC`, `IsCycle`, `ofThree`, `distinguishedCycle`
  and the six projection maps.
- From `Section_2_Preliminaries/FiniteLaw.lean`: `IsGLaw`, the finite law
  type and its moments interface.
- From `Section_2_Preliminaries/MomentInversion.lean`: the six-term
  inversion identities.
- From `Section_2_Preliminaries/Polytope.lean`: `IsPolytope`.
- From `Section_2_Preliminaries/Triangle.lean`: the triangle adjacency
  relation and `generalizedTriangle`.
- From `Section_2_Preliminaries/Relaxation.lean`: the distinguished and
  all-cycles cycle relaxations.
- From `Section_2_Preliminaries/DefinitionAudit.lean`: `isCycle_iff_alpha`,
  `two_le_card` (the `Fin 3` distinctness helper).
- From `Section_2_Preliminaries/PaperCoordinates.lean`: `H`, `multilinearSet`,
  `polytope`, `momentCoordinate`, `common`, `coordinateSupport`,
  `coordinateCorners`, `ofThree` (hypergraph completion), `completion`,
  `cycleCoordinates`, `cycleDistinguishedRelaxation`, `cycleAllRelaxation`.
- From `Section_2_Preliminaries/GeometryCycle.lean`: `Geometry.IsCycle`,
  `GeometryCycle`.
- From `Section_2_Preliminaries/PaperHypergraph.lean`: the hypergraph
  completion type and `paper_sharp_classification`'s supporting
  definitions.
- From `Section_6_MainTheorem/PaperMain.lean`: the main theorem statement
  with the single authorized `sorry`.

`alpha_cycle_comparator.json`:

- `theorem_names`: `["AlphaCycle.PaperHypergraph.paper_sharp_classification"]`
- `definition_names`: `[]` (deliberately empty — see below)
- `permitted_axioms`: `["propext", "Classical.choice", "Quot.sound"]`
  (never `sorryAx`)
- `challenge_module`: `alpha_cycle_comparator`,
  `solution_module`: `AlphaCycle`

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

## Provenance of the challenge excerpts

The `Challenge/` modules are excerpts of the solution sources, reviewed
line-by-line against them: prose and proof bodies not needed for typing
the main theorem's closure are dropped; every definition, structure,
and helper lemma the main theorem's transitive closure reaches is kept
with a byte-identical body. Pure-term helpers elaborate identically in
any file layout. Two layout-sensitive facts were verified empirically
against the official judge semantics and then locked in:

- The challenge mirrors the solution's multi-file structure (one excerpt
  module per solution module, compiled file-by-file in dependency order
  in a fresh process each) because auto-generated auxiliary-lemma
  numbering depends on per-file elaboration state.
- `Section_1_Introduction/Geometry.lean` is embedded whole (not
  excerpted) because the simplifier's per-declaration equation-lookup
  cache is seeded from imported oleans: excerpt-only priors under-prime
  it and renumber downstream auxiliary simp lemmas. The full embedding
  reproduces the exact numbering (verified: zero mismatches over the
  whole closure under judge semantics).

No proof of the paper is reconstructed in the challenge: the only proof
obligation is the sorry'd main theorem, and every other copied lemma is
complete. The challenge's helper-lemma copies exist only so the fixed
definitions elaborate with the same bodies the judge compares.

## Toolchain route (original pin, no source port)

The solution is pinned to Lean `v4.34.0-rc2` with mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`; that toolchain has no
`leanexport`/comparator. No source port was performed. Instead both
sides are elaborated under the original pin and serialized to NDJSON
with the faithful 4.34 serializer (`../Verification/export34.lean`,
byte-identical to the verified Gaussian serializer, external support,
never imported by the challenge), which replicates the official 4.35
`LeanExport` format 3.1.0 field-for-field (all `ConstantInfo` bodies,
safety flags, hints, universes, inductive/ctor/recursor structure;
`unsafe` is skipped, never trusted; anything unrepresentable is a hard
refusal). The serializer's own entry point is `unsafe` only because
environment loading is an unsafe IO operation; that unsafety lives
entirely in this external export utility — never in the challenge or
the solution — and its output is untrusted data re-parsed and
kernel-checked by the official judge.
The official 4.35 `lake comparator` (default kernel, `bwrap` sandbox)
then judges those exports as untrusted data. Nothing here is claimed
to be a 4.35 source port, and no 4.34 olean is ever loaded into a
4.35 process.

Serializer parity was established once for this serializer byte-stream
in the sibling Gaussian package (`../Verification/parity.md` there):
a Lean-core-only fixture exported by the official 4.35 `leanexport`
and by this 4.34 serializer matches constant-for-constant. This
package reuses those serializer bytes unchanged, so no second parity
run is claimed here.

## Actual runs

Pins: Lean `v4.34.0-rc2`
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0` (plus its eight pinned
companion packages; see the package Readme for the assembly recipe)
for elaboration and both exports; judge: Lean `v4.35.0`
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) with `bwrap` sandbox
active and default kernels.

Export bindings (sha256; generated from the compiled sources by the
4.34 serializer commands below and verified after transfer):

- challenge: `CHALLENGE_SHA256` (see `../verification.json`)
- solution: `SOLUTION_SHA256` (see `../verification.json`)

Positive (official judge, Linux, from the exports above):

```
lake comparator --config Comparator/alpha_cycle_comparator.json \
  --challenge-from-export challenge.ndjson \
  --solution-from-export solution.ndjson
```

exit 0. The judge compares the main theorem statement and every
reachable fixed definition body (8199 constants under the judge's
traversal, including all helper proofs and kernel primitives).

Negative controls (`negative_controls.sh`; each rebuilds a tampered
variant with the pinned 4.34 toolchain, re-exports it, and requires
the official judge to reject it):

- N1 incorrect-polytope: challenge `polytope` replaced by the empty set.
- N2 wrong-cycle: challenge `cycleDistinguishedRelaxation` built from the
  all-cycles relaxation instead of the distinguished cycle.
- N3 identity-relaxation: challenge `cycleAllRelaxation` replaced by empty.
- N4 sorry-solution: solution main theorem proved by `sorry`.
- N5 threshold-tamper: challenge classification threshold `= 1` weakened
  to `= 2`.

All five are rejected (nonzero judge exit); each control first asserts
its tamper changed the export, so no control is vacuous. N1–N3/N5
tamper the challenge side while holding the solution fixed, which
exercises exactly the same symmetric constant-equality check the judge
applies to solution deviations.

## Reproduce

```
sh Comparator/reproduce.sh <package-root> <work-dir>
```

with `LEAN34` pointing at the pinned 4.34.0-rc2 binary and
`EXTERNALS_LEAN_PATH` set to the colon-separated pinned external
dependency outputs (see the package Readme for the assembly recipe).
On Linux with the 4.35 toolchain (`LAKE35`, `LEAN35`,
`COMPARATOR_BWRAP`) it runs the official judge; elsewhere it stops
after producing and completeness-checking both exports (exit 2 —
never a passing verdict without the judge).

`test_reproduce.py` checks the driver's guards and failure propagation
with stubbed tools (26 cases: toolchain pins, version-command
failures, externals path hygiene, challenge/source guards, build and
export failures, export determinism, judge rejection propagation,
wrong-platform behavior). They verify the driver only — no theorem is
checked by the stub tests. The real proof verdict comes solely from
`lake comparator` on Linux.
