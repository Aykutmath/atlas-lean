/-
Copyright (c) 2026 Aykut Arslan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aykut Arslan
-/
import HypercubeInequality

/-!
# Hypercube inequality — endpoint audit helper

Local inspection helper for the unified formalization. It `#check`s the
headline declarations and `#print axioms` the transitive dependencies of
the main endpoints on the standard axioms. Every declaration below is the
actual checked proof; this file only inspects it.

This file is NOT part of the independent challenge in `Comparator/`: it
imports the solution (`HypercubeInequality`), so it cannot serve as a
challenge, and the challenge never imports it. Run from the source
project root after `lake build`:

```sh
lake env lean Verification/EndpointAudit.lean
```

Expected result: exit 0, with every endpoint below depending only on
`propext`, `Classical.choice`, and `Quot.sound`.
-/

-- Headline theorems (paper order).
#check HypercubeInequality.cocycle_alternating_sum
#check HypercubeInequality.cocycle_exactly_two_nonzero
#check HypercubeInequality.oneStep
#check HypercubeInequality.main_full
#check HypercubeInequality.weighted_cube
#check HypercubeInequality.sharp_optimal
#check HypercubeInequality.subset_ratio_mono
#check Cor101.corollary10_1
#check Cor101.corollary10_1_with_sharpness

-- Headline definitions.
#check HypercubeInequality.S
#check HypercubeInequality.gap
#check HypercubeInequality.simDet
#check HypercubeInequality.subsetRatio
#check Cor101.Space
#check Cor101.fullVolume
#check Cor101.lineVolume
#check Cor101.planeVolume
#check Cor101.IsZonotope
#check Cor101.IsZonoid
#check Cor101.ProjectionInequality
#check Cor101.Corollary10_1
#check Cor101.SharpProjectionConstant

-- Transitive dependencies of the main endpoints on the standard axioms.
#print axioms HypercubeInequality.main_full
#print axioms HypercubeInequality.weighted_cube
#print axioms HypercubeInequality.sharp_optimal
#print axioms Cor101.corollary10_1
#print axioms Cor101.corollary10_1_with_sharpness
#print axioms HypercubeInequality.subset_ratio_mono
#print axioms HypercubeInequality.cocycle_alternating_sum
