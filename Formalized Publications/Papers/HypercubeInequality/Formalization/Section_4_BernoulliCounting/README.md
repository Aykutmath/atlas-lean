# Section 4 — The binary determinant inequality

Paper §4 turns the local estimate into the Bernoulli determinant
inequality (Corollary 4.2) by ordered-tuple counting: repeated rows
vanish, `|det|` and the weights are permutation-invariant, and the
projected (D-side) counting uses the omission symmetry.

## Reading order

- `Counting.lean` — the only file in this section.

## Main declarations

All in namespace `HypercubeInequality`, file `Counting.lean`:

| Paper | Lean | Coverage |
|---|---|---|
| §4, ordered-tuple counting (A-side) | `count_ordered_A` | HI-COUNT1 |
| §4, projected counting + omission symmetry | `count_ordered_D`, `omitSum_eq` | HI-COUNT2 |
| §4 Cor 4.2, Bernoulli determinant inequality | `bernoulli_det_inequality` | HI-IID |
