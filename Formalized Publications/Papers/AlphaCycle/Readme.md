# Tightness of the Cycle-Based Relaxation for Completed Length-Three Alpha-Cycles

A Lean formalization of the paper's main classification theorem.

[Paper (PDF)](Papers/alpha_cycle.pdf) |
[Interactive paper (HTML)](Papers/alpha_cycle_interactive.html) |
[Lean formalization](Formalization/) |
[LaTeX](Papers/Latex/main.tex) |
[Citation](Papers/citation.bib)

## Main result

**Theorem 2.4: Sharp classification.** For a completed length-three
$\alpha$-cycle, the distinguished-cycle relaxation and the all-cycle
relaxation each equal the multilinear polytope if and only if the three
pair-only blocks $A,B,C$ are singletons. The common intersection and
private vertices may be arbitrary.

Lean theorem:
[`AlphaCycle.PaperHypergraph.paper_sharp_classification`](Formalization/Section_6_MainTheorem/PaperMain.lean#L82-L89).

## Authorship

Paper: Aykut Arslan and Meta AI, with Muse Spark assistance for formalization.
Mathematical review: Kien Le.

## Versions

- Lean source pin: `v4.34.0-rc2`.
- Mathlib: `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
- MathlibExt: not used.

## Independent comparator

The [challenge](Comparator/alpha_cycle_comparator.lean) independently restates
this theorem and its required definitions in `Comparator/Challenge/`,
importing only Mathlib and challenge-local modules, never the formalization.
Its single `sorry` is a challenge placeholder, not an unfinished solution.

The official Lean 4.35.0 comparator accepted exports compiled under the
source pin above. This is not a Lean 4.35.0 source port.

On Linux with bubblewrap and those original-pin exports, from the Atlas root:

```sh
lake comparator --config "Formalized Publications/Papers/AlphaCycle/Comparator/alpha_cycle_comparator.json" --challenge-from-export challenge.ndjson --solution-from-export solution.ndjson
```

The Atlas root's default build does not automatically include this paper.
