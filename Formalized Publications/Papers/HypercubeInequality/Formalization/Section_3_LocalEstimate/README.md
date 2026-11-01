# Section 3 — Exterior-algebra Bernoulli estimate

Paper §3 proves Lemma 3.1 (local Bernoulli estimate): the signed
indicators are encoded in an exterior vector, cancellation permits
centering the binary height vector, and the Bernoulli variance
`pbar(1-pbar)` bounds the weighted absolute sum. In Lean the exterior
estimate is carried out in coordinates via an elementary Lagrange
identity with the same conclusion and constant. This section also hosts
the determinant-volume bridge used across sections, and the integrated
§4 Lemma 4.1 bound.

## Reading order

1. `Lagrange.lean` — coordinate Lagrange identity (proof device).
2. `SimplexVolume.lean` — determinant-volume bridge.
3. `Local.lean` — assembly: local estimate and weighted inequality.

## Main declarations

All in namespace `HypercubeInequality`:

| Paper | Lean | File | Coverage |
|---|---|---|---|
| §3 proof device, Lagrange identity | `wedge_pythagoras`, `wedgeSign`, `sum_powersetCard_mem`, `sum_powersetCard_sdiff`, `sum_offdiag_cancel` | `Lagrange.lean` | HI-LAGRANGE |
| Bridge, `|det(1;…)| = k! vol(conv)` | `abs_simDet_eq_volume_convexHull` | `SimplexVolume.lean` | HI-SIMPVOL |
| §3, signed-volume identities | `detOf_eq_integral`, `abs_detOf_eq_integral` | `Local.lean` | HI-SIGNEDVOL |
| §3, single null set for all T | `wedgeCoeff_baseVec_all_ae` | `Local.lean` | HI-NULLSTAR |
| §3 Lem 3.1, local Bernoulli estimate | `local_bernoulli_estimate` | `Local.lean` | HI-LOCAL |
| §3, Bernoulli variance identity | `centVec_sq_sum` | `Local.lean` | HI-BERNVAR |
| §3, coefficient identification | `wedgeCoeff_eq`, `wedgeCoeff_term` | `Local.lean` | HI-WEDGE-COEFF |
| §4 Lem 4.1, weighted Bernoulli inequality | `weighted_bernoulli_inequality` | `Local.lean` | HI-WEIGHTED |
| §4, `A_T` expansion + integral form | `detAT_eq_expansion`, `detAT_eq_integral`, `abs_detAT_le` | `Local.lean` | HI-DET-EXPAND |

Note: `SimplexVolume.lean` (`HI-SIMPVOL`) is the determinant-volume
bridge used across sections (cocycle null sets, signed volumes, cube
counting), not only in Section 3.
