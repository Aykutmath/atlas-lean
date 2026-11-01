# Section 9 — Hypercube specialization

Paper §9 specializes the main theorem to vertex laws on `{0,1\}^d`:
gaps evaluate to `2p(1-p)` via fiber sums, giving first the
probability-weighted form (Corollary 9.1) and then, with normalized
simplex volumes, the original arbitrary-weight Hypercube inequality
with facet form (Corollary 9.2).

## Reading order

- `Cube.lean` — the only file in this section.

## Main declarations

All in namespace `HypercubeInequality`, file `Cube.lean`:

| Paper | Lean | Coverage |
|---|---|---|
| §9 setup, `S` of vertex law as T-sum | `vertS_eq_tsum` | HI-CUBE-SETUP |
| §9, gap evaluation for vertex laws | `gap_vertMeas_eq` | HI-CUBE-GAP |
| §9 Cor 9.1, probability-weighted Hypercube | `cube_prob_weighted` | HI-CUBE |
| §9 Cor 9.2, Hypercube inequality + facet form | `weighted_cube`, `weighted_cube_facet` | HI-WCUBE |
