# Section 6 — Proof of the main theorem

Paper §6 assembles the two directions into Theorem 2.4 (sharp
classification): both cycle-based relaxations are exact if and only if the
three pair-only blocks are singletons, with a strict gap otherwise. The
graph-triangle instance of §1 is the special case $T=D_1=D_2=D_3=\emptyset$.

## Contents

- `Main.lean` — the sharp classification in relaxation coordinates
  (`sharp_classification`, `allCycle_gap_nonempty`).
- `PaperConvexCombination.lean` — convex-combination lifts into the
  polytope used by the assembly.
- `PaperMain.lean` — the paper-coordinate endpoints
  (`paper_sharp_classification`, `cycle_all_gap_nonempty`) and the
  relaxation inclusions.

## Main declarations

| Paper | Lean | File |
|---|---|---|
| §2.4/§6, Theorem 2.4 (sharp classification) | `AlphaCycle.PaperHypergraph.paper_sharp_classification` | `PaperMain.lean` |
| §2.4/§6, strict gap for large blocks | `AlphaCycle.PaperHypergraph.cycle_all_gap_nonempty` | `PaperMain.lean` |
| Relaxation-coordinate classification | `AlphaCycle.sharp_classification`, `AlphaCycle.allCycle_gap_nonempty` | `Main.lean` |

The Section 3 example files build on these endpoints to record the
instances' exactness/gap data (see `Section_3_Obstruction/README.md`).
