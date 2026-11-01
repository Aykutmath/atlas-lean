# Section 7 — Approximation by finite laws

Paper §7 settles the endpoint cases (zero gaps force `S_d = 0`;
all-positive gaps with one infinite make the bound infinite), shows
finite gaps imply finite coordinate first moments, and builds the
coordinate quantization whose gaps and simplex functionals converge.
This file also contains the Section 8 Borel induction assembly
`main_borel` / `main_full` (the main theorem endpoint).

## Reading order

- `Approx.lean` — the only file in this section. Read it in order:
  endpoint cases, finite moments, quantizer construction and
  convergence, then the Borel assembly at the end.

## Main declarations

All in namespace `HypercubeInequality`, file `Approx.lean`:

| Paper | Lean | Coverage |
|---|---|---|
| §8, main theorem for Borel laws | `main_full` | HI-MAIN |
| §8, finite-moment induction core | `main_borel` | HI-MAIN-FM, HI-INDUCTION |
| §8, one-step for finite-moment Borel laws | `onestep_finite_moment` | HI-FINMOMENT |
| §8, projected gaps equal original gaps | `gap_map_projDrop` | HI-PROJGAP |
| §7, zero-gap case | `gap_eq_zero_imp_S_eq_zero` | HI-ZERO |
| §7, infinite-gap case | `infGap_rhs` | HI-INFGAP |
| §7, finite gaps give finite moments | `finite_gap_moment` | HI-FINMOM |
| §7, quantizer + convergence | `quantFn`, `quantFn_bound`, `measurable_quantFn`, `quantFn_range_finite`, `tail_tendsto_zero`, `quant_l1_tendsto`, `quantVec`, `quantLaw`, `quantLaw_finite_support`, `atomic_of_finite_support`, `quant_moment_bound`, `gap_quant_tendsto`, `det_l1_tendsto`, `S_tendsto_quant` | HI-QUANT-A, HI-QUANT-L1, HI-QUANT-PUSH, HI-QUANT-B, HI-QUANT, HI-GAPCONV, HI-DETMONO, HI-SCONV |
