# Section 12 — Projection monotonicity

Paper §12 proves Proposition 12.1: for nonempty coordinate sets
`J ⊆ I`, the normalized ratios satisfy
`0 ≤ R_I(ν) ≤ R_J(ν) ≤ 1`. The proof goes through a one-coordinate
deletion step, permutation invariance of the ratio via the determinant
integral, deletion at an arbitrary coordinate position, and
strong-induction iteration.

## Reading order

1. `Ratios.lean` — ratio definition, `R ≤ 1`, singleton equality,
   one-coordinate deletion step, deficit persistence.
2. `SubsetRatios.lean` — general `J ⊆ I` monotonicity.

## Main declarations

All in namespace `HypercubeInequality`:

| Paper | Lean | File | Coverage |
|---|---|---|---|
| §12, ratio definition | `subsetRatio` | `Ratios.lean` | HI-RATIO-DEF |
| §12, ratio bound `R ≤ 1` | `subsetRatio_le_one` | `Ratios.lean` | HI-RATIO-LE1 |
| §12, singleton equality | `subsetRatio_one_eq_one` | `Ratios.lean` | HI-RATIO-SINGLE |
| §12 Prop 12.1 step, deletion inequality | `subsetRatio_succ_le_proj` | `Ratios.lean` | HI-RATIO-DELETE |
| §12, deficit persistence | `subsetRatio_le_of_proj_le` | `Ratios.lean` | HI-RATIO-DEFICIT |
| §12 Prop 12.1, full subset monotonicity | `subset_ratio_mono`, `subsetRatioSet_mono`, `subsetRatioSet_le_one`, `subsetRatioSet_singleton` | `SubsetRatios.lean` | HI-RATIO-SUBSET |
