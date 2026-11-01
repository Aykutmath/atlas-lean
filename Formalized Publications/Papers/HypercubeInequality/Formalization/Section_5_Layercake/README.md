# Section 5 — From binary labels to real heights

Paper §5 extends the binary estimate to real heights by threshold
integration: each real height is an integral of binary heights,
Corollary 4.2 applies at every threshold, and the gap identity
`E|B-B'| = 2∫ q(1-q)` closes the real-height determinant inequality.

## Reading order

- `Layercake.lean` — the only file in this section.

## Main declarations

All in namespace `HypercubeInequality`, file `Layercake.lean`:

| Paper | Lean | Coverage |
|---|---|---|
| §5, threshold representation + `A_T` integral | `detAT_eq_integral_thresh`, `abs_detAT_le_integral_thresh`, `alt_detOf_sum_zero` | HI-LAYERCAKE |
| §5, per-threshold application + Tonelli | `layercake_bound` | HI-THRESH-APPLY |
| §5, gap identity | `gap_identity` | HI-GAPID |
| §5, real-height determinant inequality | `det_onestep` | HI-DET-ONESTEP |
