# Section 4 — Negative direction: lifting the obstruction

Paper §4 lifts the four-variable obstruction to the three maximal edges:
consistent local laws with no global realization (Proposition 4.1), the
structure of reduced no-private subcycles (Lemma 4.2, via
`PaperGeometry.reduced_subcycle_structure` in §2), and survival of the
witness under every switched inequality from every no-private subcycle
(Proposition 4.3).

## Contents

- `Negative.lean` — the lifted parity/independent local family and its
  consistency/non-realizability.
- `NegativeVertex.lean` — vertex-level encodings and the selected witness
  (`locals_consistent`, `locals_not_realizable`, `selected_witness_gap`).
- `NegativeSwitched.lean` — the witness lies in the all-cycle relaxation
  (`witness_in_allCycleRelaxation`).
- `NegativeTheorem.lean` — counterexamples from non-singleton blocks
  (`counterexample_of_not_singletons`, `counterexample_of_large_block`).
- `PaperEvents.lean` — switching event calculus used by the survival argument.

## Main declarations

All in namespace `AlphaCycle` unless noted:

| Paper | Lean | File |
|---|---|---|
| §4, Prop 4.1 (consistent, not realizable) | `NegativeVertex.locals_consistent`, `NegativeVertex.locals_not_realizable`, `PaperObstruction.selected_witness_gap` | `NegativeVertex.lean`, `PaperObstruction.lean` (§3) |
| §4, Lemma 4.2 (reduced-subcycle structure) | `PaperGeometry.reduced_subcycle_structure` | `PaperGeometry.lean` (§2) |
| §4, Prop 4.3 (witness in $R_{\mathrm{all}}$) | `NegativeSwitched.witness_in_allCycleRelaxation` (also `NegativeVertex.witness_in_allCycleRelaxation`) | `NegativeSwitched.lean` |
| §4, large-block counterexamples | `counterexample_of_large_block`, `counterexample_of_not_singletons` | `NegativeTheorem.lean` |
