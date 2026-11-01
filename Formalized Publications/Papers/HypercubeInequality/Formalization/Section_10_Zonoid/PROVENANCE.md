# Source and verification provenance

## Mathematical source of truth

- File: `38_Hypercube_Inequality_Final_Draft_2026-10-29.pdf`
- Target: Section 10, Corollary 10.1, printed page 12.
- SHA256: `d25b04fdcf68216f9beb1b98cf13ff06719dd12b89a67bcbcd214254de9f1264`
- The manuscript was read but not modified.

## Recovered dependency source

- File: `hypercube_lean.zip`
- SHA256: `111c26fdb19331e042604220ff5576740940af32998fb8d87a022db207a1b147`
- Original path within archive: `hypercube_formalization/Hypercube/`.
- Reused endpoint: `Hypercube.Main.random_simplex`.
- Its finite-first-moment hypothesis is discharged explicitly by
  `Cor101.FiniteBridge.projectedLaw_first_moments`.
- No edits to the original recovered archive or manuscript were made.

## Toolchain

- Lean: `leanprover/lean4:v4.34.1`
- Official Lean commit: `5045d0056413266e57c625dcd7c365b10e377c52`
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`
- Other dependencies: pinned by `lake-manifest.json`.

## Verification interpretation

New checked theorems were elaborated and accepted by Lean locally. Audits list
their actual dependencies on axioms. The only permitted foundational axioms
are `propext`, `Classical.choice`, and `Quot.sound`; these are not new project
assumptions. No `sorry`, `admit`, custom unproved axiom, `unsafe` declaration, or
`native_decide` is used by the new source or the recovered Hypercube modules.

Mathlib was obtained at the pinned source revision with its standard compiled
cache. We do not claim to have independently rechecked every Mathlib proof or
run a second kernel. Runtime compatibility details are disclosed separately.

The all-zonoid target is now proved by `Cor101.corollary10_1`; validity and
sharpness are combined in `Cor101.corollary10_1_with_sharpness`. Both endpoints
compile and their transitive axiom sets contain only the standard three axioms.

## Completion run (October 30, 2026 UTC)

The user supplied `Corollary_10_1_Lean_Partial(2).zip`, SHA256
`1dc4ba85f3e483d717e14fea4835cdffbc1e378d84b604c13029bbb2a2a38161`.
All original archive file hashes were checked before editing. The mathematical
PDF is unchanged. Original Hypercube proof sources are unchanged.
The official Lean 4.34.1 distribution was freshly restored and its SHA256 matched
the official release digest. No compatibility wrapper, preload or kernel change
was used in this completion run. Exact environment and dependency details appear
in `verification/restored_environment.json` and `restored_dependencies.json`.

The orthogonal coordinate construction in `Cor101/ZonotopeProjection.lean` is
adapted from public OpenAI math, `lean/OAI/Geometry/ProjectionBodies/ShadowSlices.lean`,
at commit `4eaee87548250b2682affda7d05d947c05554bae`:
https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Geometry/ProjectionBodies/ShadowSlices.lean
Original source blob: `cdb038e7a916d44ffb899725cd525239617e6cda`.
The source was used with attribution and locally checked after adaptation;
no theorem was accepted merely on a repository's claim. See accompanying license.

