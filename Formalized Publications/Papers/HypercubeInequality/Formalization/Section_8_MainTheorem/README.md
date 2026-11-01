# Section 8 — Induction and proof of the main theorem

Paper §8 completes Theorem 1.1 by induction on the dimension: the
base case `S_1 = D_1` plus the one-coordinate inequality applied to
the projected law give the constant `(d+1)/2^d`. This section holds
the finite-support induction; the Borel case (`main_borel`,
`main_full`) lives in `Section_7_Approximation/Approx.lean`.

## Reading order

- `Induction.lean` — the only file in this section.

## Main declarations

All in namespace `HypercubeInequality`, file `Induction.lean`:

| Paper | Lean | Coverage |
|---|---|---|
| §6+§8, main inequality for finitely supported laws | `main_fin_support` | HI-MAIN-FIN |
| §8, scalar induction step (auxiliary) | `scalar_induction` | — |
| §8, projected gaps for atomic laws (auxiliary) | `gap_proj_atomMeas` | — |
