# Section 1 — Introduction

Paper §1 fixes the objects of the classification: for a length-three
cycle $(e_1,e_2,e_3)$ with the notation of the paper,
$T=e_1\cap e_2\cap e_3$ is the common block,
$A=(e_1\cap e_2)\setminus e_3$,
$B=(e_2\cap e_3)\setminus e_1$,
$C=(e_1\cap e_3)\setminus e_2$ are the three pair-only blocks, and the
$D_i$ are the private blocks. A triple is a cycle when all three
pair-only blocks are nonempty; the singleton case is when all three have
cardinality exactly one.

## Contents

- `Geometry.lean` — Venn blocks, core, `IsCycle`, `Singletons`.

## Main declarations

All in namespace `AlphaCycle.Geometry`, file `Geometry.lean`:

| Paper | Lean |
|---|---|
| §1, common block $T$ | `common` |
| §1, pair-only blocks $A,B,C$ | `blockA`, `blockB`, `blockC` |
| §1, private blocks $D_1,D_2,D_3$ (zero-based indices) | `privateBlock` (see `PaperGeometry.lean`, §2) |
| §1, pairwise-intersection core | `core` |
| §2.3, length-three $\alpha$-cycle condition | `IsCycle` |
| §2.4, singleton predicate | `Singletons` |

Note: Lean uses edge indices `0,1,2`; these correspond to the paper's
edges `1,2,3`.
