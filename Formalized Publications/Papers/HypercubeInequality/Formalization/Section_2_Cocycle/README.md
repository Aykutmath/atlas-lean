# Section 2 — Signed simplex cancellation

Paper §2 proves Lemma 2.1 (alternating deletion identity): for
Lebesgue-a.e. `x`, the signed simplex indicators cancel,
`∑ σ_r 1_{T_r}(x) = 0`. Off a null set, either all signed terms vanish
or exactly two are nonzero (`+1` and `-1`).

## Reading order

1. `Cocycle.lean` — deletion identity, affine-dependency analysis,
   exceptional null set (Lemma 2.1 core).
2. `CocycleRefine.lean` — term structure and the exactly-two-nonzero
   refinement.

## Main declarations

All in namespace `HypercubeInequality`:

| Paper | Lean | File | Coverage |
|---|---|---|---|
| §2 Lem 2.1, signed cancellation a.e. | `cocycle_alternating_sum` | `Cocycle.lean` | HI-COCYCLE |
| §2 proof, d=1 base case | `cocycle_dim1` | `Cocycle.lean` | HI-COCYCLE-D1 |
| §2 proof, affine dependency identities | `cocycleLambda_sum`, `cocycleLambda_orth`, `affineDep_eq_smul_lambda`, `cocycleLambda_sign_classes`, `cocycleSigma_eq_sign_lambda` | `Cocycle.lean` | HI-AFFDEP |
| §2 proof, active-index analysis + null set | `cocycleTmin_attains`, `cocycleTmax_attains`, `cocyclePos_attainer_unique`, `cocycleNeg_attainer_unique`, `mem_cocycleNull_of_two_zeros`, `volume_cocycleNull` | `Cocycle.lean` | HI-ACTIVE |
| §2 Lem 2.1 refinement, exactly two nonzero terms | `cocycle_exactly_two_nonzero`, `cocycle_term_structure`, `cocycle_dim1_terms` | `CocycleRefine.lean` | HI-COCYCLE-TWO |
