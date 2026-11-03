# Section 2 — Preliminaries

Paper §2 sets up the hypergraph/completion language, the multilinear
polytope and its probabilistic representation (Lemma 2.1), Boolean moment
inversion (Lemma 2.2), the complete edge relaxation with local laws,
the length-three $\alpha$-cycle definition, and the generalized triangle
inequalities with their switchings (Lemma 2.3).

## Contents

- `FiniteLaw.lean`, `Basic.lean`, `Core.lean` — finite Boolean laws and the
  pair/triple local-law language with consistency and realizability.
- `MomentInversion.lean`, `MomentConverse.lean`,
  `PaperInversionIdentities.lean`, `PaperTranscription.lean` — Boolean moment
  inversion, inverse cells, and the transcription identities (including the
  repaired singleton cells).
- `Polytope.lean`, `LocalVector.lean` — completed support, moment vectors,
  multilinear polytope, and local moment vectors in the CER.
- `Triangle.lean`, `Relaxation.lean`, `AllCycles.lean`,
  `CyclePermutation.lean`, `Reindex.lean` — no-private triples, switching,
  switched generalized triangles, distinguished/all-cycle relaxations.
- `Gluing.lean`, `SetGluing.lean`, `GeometryCycle.lean` — gluing along shared
  blocks, set-level gluing, and reduced-cycle combinatorics.
- `PaperCoordinates.lean`, `PaperHypergraph.lean`, `PaperGeometry.lean`,
  `PaperCycleCorrespondence.lean`, `PaperTriangles.lean`,
  `DefinitionAudit.lean` — paper vertex-plus-edge coordinates, completion and
  CER, Venn-block calculus, $\alpha$-cycle correspondence, triangle validity,
  and the definition audit.

## Reading order

`FiniteLaw` → `Basic`/`Core` → `MomentInversion` → `MomentConverse` →
`Polytope` → `Triangle` → `Relaxation` → `AllCycles`/`CyclePermutation` →
`Gluing`/`SetGluing` → `GeometryCycle` → `PaperCoordinates` →
`PaperHypergraph` → `PaperGeometry` → `PaperCycleCorrespondence` →
`PaperTriangles` → `DefinitionAudit`; `LocalVector`, `Reindex`,
`PaperInversionIdentities`, `PaperTranscription` alongside their subjects.

## Main declarations

| Paper | Lean | File |
|---|---|---|
| §2.1, Lemma 2.1 (probabilistic representation) | `PaperHypergraph.mem_polytope_iff_expectation` | `PaperCoordinates.lean` |
| §2.1, moment inversion (Lemma 2.2) | `mass_eq_signed_moments`, `exists_law_with_moments_iff` | `MomentInversion.lean`, `MomentConverse.lean` |
| §2.2, CER / consistent local laws | `completeEdgeRelaxation`, `mem_completeEdgeRelaxation_iff_consistent` | `PaperHypergraph.lean` |
| §2.3, $\alpha$-cycle definition | `Geometry.isCycle_iff_alpha`, `Geometry.core_not_subset_completed_iff` | `DefinitionAudit.lean` |
| §2.3, Lemma 2.3 (GT validity + switchings) | `multilinearPolytope_subset_switchedGeneralizedTriangleSet` | `PaperTriangles.lean` |
| §2.4, $R_{\mathrm{dist}}(H)$, $R_{\mathrm{all}}(H)$, inclusion chain | `cycleDistinguishedRelaxation`, `cycleAllRelaxation`, `cycle_relaxation_inclusions` | `PaperMain.lean` (§6) |

The meets/joins of the Venn-block calculus used across sections
(`privateBlock`, `vennBlock`, decompositions, `reduced_subcycle_structure`,
`singleton_private_block_reduction`) live in `PaperGeometry.lean`
(Lemma 4.2 and Lemma 5.1 use them in §§4–5).
