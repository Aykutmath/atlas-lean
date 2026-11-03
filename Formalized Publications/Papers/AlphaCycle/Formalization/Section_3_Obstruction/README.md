# Section 3 — The four-variable obstruction

Paper §3 builds the parity obstruction on four variables: three pairwise
consistent local laws with no global realization (Proposition 3.1),
instantiated on the running examples (the graph triangle and the parity
four-cycle, with their Venn-block data).

## Contents

- `FourVariable.lean` — the four-variable parity/independent laws and the
  obstruction (`parity_marginals_force_equality`, `no_global`).
- `Examples.lean` — the graph-triangle and parity-four instances and their
  gap data.
- `PaperObstruction.lean` — the paper-facing obstruction statements,
  including the four-vector CER gap.
- `PaperExampleDetails.lean` — Venn/reduced/cover data for the examples.

## Main declarations

| Paper | Lean | File |
|---|---|---|
| §3, Prop 3.1 (parity forces equality, no global law) | `FourVariable.parity_marginals_force_equality`, `FourVariable.no_global` | `FourVariable.lean` |
| §3, four-vector CER gap | `Examples.fourVector_CER_gap`, `PaperObstruction.fourVector_CER_gap` | `Examples.lean`, `PaperObstruction.lean` |
| §3, running examples | `Examples.graphTriangle`, `Examples.parityFour` | `Examples.lean` |

## Note on imports

`Examples.lean` (hence `PaperObstruction.lean` and `PaperExampleDetails.lean`)
imports the Section 6 endpoints to record the exactness/gap data of the
instances. Read §6 first for those files, or read `FourVariable.lean` first
for the pure obstruction; `lake build` checks all of them together.
