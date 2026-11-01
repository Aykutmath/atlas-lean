import HypercubeInequality

/-!
# Hypercube inequality — verification file

Checks the headline declarations of the unified formalization
(see `hypercube_inequality_comparator.json` for the monitored theorem and
definition names and the permitted standard axioms) and prints the
transitive dependencies of the main endpoints on the standard axioms.

Unlike an Atlas challenge file, this file contains no placeholder proofs:
every declaration below is the actual checked proof, and this file only
inspects it. Run from the repository root after `lake build`:

```sh
lake env lean Comparator/hypercube_inequality_comparator.lean
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
