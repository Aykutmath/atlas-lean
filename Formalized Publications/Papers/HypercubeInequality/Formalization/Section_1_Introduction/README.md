# Section 1 — Introduction

Paper §1 introduces the two protagonists of the inequality: the simplex
functional `S_d(ν)` (Eq.(1)) and the coordinate gaps `D_j(ν)` (Eq.(2)),
plus the determinant convention `det(1; …)` (§1 conventions).

## Reading order

1. `Core.lean` — all Section 1 mathematics.
2. `Basic.lean` — empty scaffold (namespace only, no mathematics).

## Main declarations

All in namespace `HypercubeInequality`, file `Core.lean`:

| Paper | Lean | Coverage |
|---|---|---|
| §1 Eq.(1), simplex functional | `S` | HI-DEF-S |
| §1 Eq.(2), coordinate gaps (+ measurability) | `gap`, `measurable_gap_integrand` | HI-DEF-D |
| §1 conventions, determinant convention | `simDet` | HI-DEF-DET |
