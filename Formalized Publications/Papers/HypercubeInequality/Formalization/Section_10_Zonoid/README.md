# Section 10 — The zonoid projection formulation

Paper §10 proves Corollary 10.1: for every zonoid `K ⊂ R^(d+1)`,

```text
vol_{d+1}(K) · vol_1(P_L K)^(d-1) ≤ ∏_j vol_2(P_{E_j} K),
```

with optimal constant `1` (for `d = 1` the zero-exponent factor is `1`).
Volumes are actual Lebesgue and intrinsic Euclidean Hausdorff volumes;
zonoids are Hausdorff limits of translated finite Minkowski sums of
segments, lower-dimensional bodies included.

The Section 10 discharge is `Cor101.corollary10_1`
(+ `corollary10_1_with_sharpness` for optimality). `Zonoid.lean` and
`ZonoidGeom.lean` are independent supporting results (reduction from
volume identities, box equality, `vol_1` identity) — they are NOT the
discharge. (Their file headers still say the identities were open; those
headers predate the October 30 discharge and were left untouched.)

## Contents

- `Cor101/` — 25 files proving Corollary 10.1 end to end.
- `Hypercube/` — 64 vendored dependency files (namespace `Hypercube`).
- `Zonoid.lean`, `ZonoidGeom.lean` — supporting results (see above).
- `PROVENANCE.md`, `COVERAGE.md` — vendored provenance and step-by-step
  statement map, kept verbatim.
- `third_party/openai_math_LICENSE` — license for the adapted orthogonal
  coordinate construction in `Cor101/ZonotopeProjection.lean`.

## Reading order

Bottom-up through `Cor101/` (see `COVERAGE.md` for the mathematical step
table; per-file dependencies mirror the import lists):

1. `Definitions`, `Normalization`, `ZonotopeExtrusion` (leaves).
2. `GeneratorGeometry`, `Images`, `Sharpness`, `Translation`,
   `VolumeContinuity`, `ZonotopeProjection`, `ZonotopeDeterminants`,
   `Perturbation`, `FiniteBridge` (the last also uses `Hypercube`).
3. `ZonotopeVolume`, `LineVolume`, `PlaneVolume`.
4. `VolumeInterface`, `DeterminantCoordinates`, `ProjectionContinuity`.
5. `LimitAssembly`.
6. `Corollary` — endpoints `corollary10_1`,
   `corollary10_1_with_sharpness`.
7. Audits (`LineVolumeAudit`, `PlaneVolumeAudit`, `SharpnessAudit`,
   `VolumeContinuityAudit`, `GeometricBridgeAudit`) alongside their
   subjects; they replay `#print axioms` over the development.

`Zonoid.lean` then `ZonoidGeom.lean` may be read independently of `Cor101/`.

## Main declarations

| Paper | Lean | File | Coverage |
|---|---|---|---|
| §10 Cor 10.1, zonoid projection inequality | `Cor101.corollary10_1` | `Cor101/Corollary.lean` | HI-ZONOID |
| §10 Cor 10.1 with sharpness | `Cor101.corollary10_1_with_sharpness` | `Cor101/Corollary.lean` | HI-ZONOID |
| §10 Cor 10.1 (reduction) | `zonoid_projection_of_identities`, `zonoid_box_equality` | `Zonoid.lean` | HI-ZONOID-RED |
| §10 Cor 10.1 (`vol_1` identity) | `liftZonotope`, `zonotope_one_dim`, `projLast_liftZonotope`, `volume_projLast_liftZonotope` | `ZonoidGeom.lean` | HI-ZONOID-VOL1 |

Intermediate steps (`fullVolume_zonotopeBody`, `planeVolume_zonotopeBody`,
`projectionInequality_zonotopeBody`, continuity and closedness lemmas,
…) are mapped in `COVERAGE.md`. The dependency on the vendored bundle is
exactly one edge: `Cor101/FiniteBridge.lean` imports
`Section_10_Zonoid.Hypercube.Main` and
`Section_10_Zonoid.Hypercube.FiniteAtomicGeneric` and applies
`Hypercube.Main.random_simplex`, discharging its finite-first-moment
hypothesis via `projectedLaw_first_moments`. No other `Cor101/` file
touches `Hypercube/`.

## Provenance (merged from the former `INTEGRATION.md`)

This section was taken verbatim from
`Corollary_10_1_Lean_COMPLETE_20261030.zip` (SHA256
`90130e3626ecb3a34deac2c993244fd2a0a468ed16dcafb0d50bebe1c240b8a2`;
the archive itself is preserved untracked at the repository root and is
not committed). It arrived as a standalone Lake project on Lean 4.34.1 /
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, with its `Hypercube/`
dependency recovered from `hypercube_lean.zip` (SHA256
`111c26fdb19331e042604220ff5576740940af32998fb8d87a022db207a1b147`;
see `PROVENANCE.md`). It was first integrated unmodified as a nested
project (the two-project toolchain split recorded in the former
`Corollary_10_1_Lean/INTEGRATION.md`), then unified into this single
project: the nested `lakefile.lean` / `lean-toolchain` split is deleted,
and one `lake build` from the repository root builds everything on
Lean 4.35.0 / Mathlib `074063781836922cb02701cd12943c9f51731afa`.

No geometric argument was rederived, replaced, or mixed with any other
proof variant. Besides the move itself (new module paths
`Section_10_Zonoid.Cor101.*` / `Section_10_Zonoid.Hypercube.*`;
namespaces and theorem names unchanged), the only source changes are the
toolchain-compatibility fixes listed below. Stale 4.34.1-only logs,
check scripts, and compatibility material from the vendored
`verification/` directory were deleted; the two replayable audit files
moved to `Comparator/Audit.lean` and `Comparator/FullCorollaryAudit.lean`.

## Port record: Lean 4.34.1 → 4.35.0 (Mathlib `d13f23b…` → `07406378…`)

Under the unified toolchain the elaborator no longer accepts a set
applied as a function (`s x` for `s : Set α` fails with "Function
expected"); membership must be written `x ∈ s`. Definitional unfolding
of `∈` (used by `change`, `exact`, and projections) still works, so each
fix below only changes elaboration, never the stated proposition or the
proof. Every fix site (14 total):

`Hypercube/Geometry/Cocycle.lean` — 6 sites, `Set.range f x` → membership:

- L112: `have hjrange : Set.range i.succAbove j` →
  `have hjrange : j ∈ Set.range i.succAbove`
- L123: `have hkrange : Set.range i.succAbove k` →
  `have hkrange : k ∈ Set.range i.succAbove`
- L138: `have hirange : Set.range k.succAbove i` →
  `have hirange : i ∈ Set.range k.succAbove`
- L142: `have hjrange : Set.range k.succAbove j` →
  `have hjrange : j ∈ Set.range k.succAbove`
- L268: `have hirange : Set.range p.succAbove i` →
  `have hirange : i ∈ Set.range p.succAbove`
- L504: `have hkr : Set.range i.succAbove k` →
  `have hkr : k ∈ Set.range i.succAbove`

`Hypercube/Geometry/VolumeBridge.lean` — 7 sites, set application →
membership (the L22 definition-body fix also resolves the follow-on
`change`/`constructor`/type-mismatch errors at L52–64, L218, L242–243,
which were caused by the broken definition body, not by new breakage):

- L22: `And (unitCube m x)` → `And (x ∈ unitCube m)` (in `orderChamber`)
- L35: `unitCube m (coordinatePermutation p x) <-> unitCube m x` →
  `(coordinatePermutation p x) ∈ unitCube m <-> x ∈ unitCube m`
- L54–56: `change And (unitCube m x) … <-> And (unitCube m …) …` →
  same shape with `x ∈ unitCube m` / `(coordinatePermutation p x) ∈ unitCube m`
- L79: `Exists (fun p => orderChamber m p x)` →
  `Exists (fun p => x ∈ orderChamber m p)`
- L154: `(hx : orderChamber m (Equiv.refl (Fin m)) x)` →
  `(hx : x ∈ orderChamber m (Equiv.refl (Fin m)))`
- L173: same binder shape → membership form
- L242: `orderChamber m (Equiv.refl (Fin m)) (chamberVertex m r)` →
  `(chamberVertex m r) ∈ orderChamber m (Equiv.refl (Fin m))`

`Cor101/LimitAssembly.lean` — 1 site. `closure_minimal hfinite …` no
longer infers the two sets by higher-order unification, so they are
given explicitly (same sets, same lemma, same conclusion):

- L42: `exact (closure_minimal hfinite (isClosed_projectionInequality d)) hK`
  → first `have hsub : {Z | IsZonotope Z} ⊆ {Z | ProjectionInequality Z} :=
  fun Z hZ => hfinite Z hZ`, then
  `exact (closure_minimal hsub (isClosed_projectionInequality d)) hK`

No other Section 10 file changed beyond the mechanical import-path
rewrite. `FiniteBridge.lean` was NOT re-pointed at the root
`HypercubeInequality` development.

## Known tech debt (follow-up, not done here)

The vendored `Hypercube/` bundle proves its own `Main.random_simplex`,
which substantially duplicates the root `HypercubeInequality`
development (Sections 1–9). Deduplicating it — re-pointing
`FiniteBridge` at the root development — is explicitly out of scope for
this unification and is left as a follow-up.
