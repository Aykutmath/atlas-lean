# The Hypercube Inequality via Signed Simplex Cocycles

Formalization of Aykut Arslan's October 29 draft
[*The Hypercube Inequality via Signed Simplex Cocycles*](Papers/hypercube_inequality.pdf)
(the formalized, interactive edition is
[hypercube_inequality_interactive.html](Papers/hypercube_inequality_interactive.html);
BibTeX: [citation.bib](Papers/citation.bib)).

## Summary

For a Borel probability measure $\nu$ on $\mathbb{R}^d$ and
$d + 1$ independent samples, let $S_d(\nu)$ be the expected volume
of their convex hull, and let $D_j(\nu)$ be the mean absolute
pairwise difference of the $j$-th coordinate marginal. The paper
proves $S_d(\nu) \le \frac{d+1}{2^d} \prod_{j=1}^d D_j(\nu)$ with
optimal constant, recovers the Hypercube inequality of Averkov,
von Dichter, and Soprunov on $\{0,1\}^d$, the zonoid projection
inequality, sharpness of both constants, and monotonicity of the
normalized ratio under coordinate deletion. Every numbered claim
of the draft is formalized and kernel-checked in Lean; no
`sorry`, `admit`, `native_decide`, or custom axioms are used, and
all endpoints depend only on the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

## Results

| Paper claim | Lean endpoint | Source |
| --- | --- | --- |
| Theorem 1.1 (random-simplex inequality) | `HypercubeInequality.main_full` | [Section_8_MainTheorem](Formalization/Section_8_MainTheorem) via [Approx.lean](Formalization/Section_7_Approximation/Approx.lean) |
| Lemma 2.1 (alternating deletion identity) | `HypercubeInequality.cocycle_alternating_sum` | [Cocycle.lean](Formalization/Section_2_Cocycle/Cocycle.lean) |
| Lemma 2.1 refinement (exactly two nonzero terms) | `HypercubeInequality.cocycle_exactly_two_nonzero` | [Section_2_Cocycle](Formalization/Section_2_Cocycle) |
| Lemma 3.1 (local Bernoulli estimate) | `HypercubeInequality.local_bernoulli_estimate` | [Local.lean](Formalization/Section_3_LocalEstimate/Local.lean) |
| Lemma 4.1 / Corollary 4.2 (binary determinant bounds) | `HypercubeInequality.weighted_bernoulli_inequality`, `HypercubeInequality.bernoulli_det_inequality` | [Section_3_LocalEstimate](Formalization/Section_3_LocalEstimate), [Section_4_BernoulliCounting](Formalization/Section_4_BernoulliCounting) |
| §5 threshold step | `HypercubeInequality.det_onestep` | [Layercake.lean](Formalization/Section_5_Layercake/Layercake.lean) |
| Theorem 6.1 (one-coordinate inequality) | `HypercubeInequality.oneStep` | [Onestep.lean](Formalization/Section_6_OneStep/Onestep.lean) |
| Corollary 7.1 (finite-moment extension) | `HypercubeInequality.onestep_finite_moment` | [Section_7_Approximation](Formalization/Section_7_Approximation) |
| Corollaries 9.1 / 9.2 (Hypercube inequality) | `HypercubeInequality.cube_prob_weighted`, `HypercubeInequality.weighted_cube` | [Cube.lean](Formalization/Section_9_Hypercube/Cube.lean) |
| Corollary 10.1 (zonoid projection inequality) | `Cor101.corollary10_1`, `Cor101.corollary10_1_with_sharpness` | [Corollary.lean](Formalization/Section_10_Zonoid/Cor101/Corollary.lean) |
| Proposition 11.1 (sharpness, both constants) | `HypercubeInequality.sharp_optimal`, `HypercubeInequality.sharp_onestep_optimal` | [Sharp.lean](Formalization/Section_11_Sharpness/Sharp.lean), [SharpOnestep.lean](Formalization/Section_11_Sharpness/SharpOnestep.lean) |
| Proposition 12.1 (projection monotonicity) | `HypercubeInequality.subset_ratio_mono` | [SubsetRatios.lean](Formalization/Section_12_Ratios/SubsetRatios.lean) |

## Layout

- `Papers/` — the October 29 manuscript PDF, the interactive
  HTML edition (its Lean boxes carry `source` buttons linking
  into `Formalization/`), and `citation.bib`.
- `Formalization/` — the Lean development, copied as-is from the
  source project: the root module
  [HypercubeInequality.lean](Formalization/HypercubeInequality.lean)
  imports one `Section_*` folder per paper section. The
  `Section_*` folder names are kept deliberately (matching the
  paper's section structure) instead of renaming files to an
  `A_`/`B_` scheme; namespaces are unchanged, so fully-qualified
  theorem names are exactly as checked.
- `Comparator/` — the independent Atlas-style challenge
  ([hypercube_inequality_comparator.lean](Comparator/hypercube_inequality_comparator.lean)
  with [hypercube_inequality_comparator.json](Comparator/hypercube_inequality_comparator.json)
  and [README.md](Comparator/README.md)): the definitions
  `HypercubeInequality.S` / `HypercubeInequality.gap` stated
  independently (Mathlib imports only, nothing imported from
  `Formalization/`), and `HypercubeInequality.main_full` stated with
  those definitions and proved with `sorry` — the single authorized
  placeholder. The config names exactly one theorem and zero
  definition holes (`S`/`gap` are checked as fixed constants through
  the theorem, bodies included — not as holes), on the standard
  axioms (`propext`,
  `Classical.choice`, `Quot.sound`). Verified 2026-11-02 with the
  real `lake comparator` (Linux, Lean `v4.35.0`, default kernels):
  `Your solution is okay!`, exit 0 — plus negative controls
  (altered coefficient/definition/sorry-admission are all rejected).
  Full commands, export hashes, and control results: see
  [Comparator/README.md](Comparator/README.md).
- `Verification/` — the previous self-importing endpoint audit,
  kept as the local helper
  [EndpointAudit.lean](Verification/EndpointAudit.lean) (`#check` /
  `#print axioms` over the actual proofs). It imports the solution,
  so it is not part of the challenge and the challenge never imports
  it.
- LaTeX: `Papers/Latex/` contains `main.tex` (the October 29
  source, supplied by the owner), plus its required
  `stylelibrary.tex` and `flexart.sty`. The bibliography is
  inline (`thebibliography`), so no `.bib` file is needed.
  Verified 2026-11-01: `pdflatex` (three passes, TinyTeX) builds
  15 pages whose extracted text is word-for-word identical to
  `Papers/hypercube_inequality.pdf`, including all 12 sections.

## Authorship

- Paper and formalization: Aykut Arslan.
- Formalization developed with model assistance from
  **Muse Spark** (as credited in the manuscript).
- Mathematical review of the manuscript: Dinh Pham and
  Juan Torres Toral (as credited in the manuscript).

## Versions

- Lean: `v4.35.0` (`leanprover/lean4:v4.35.0`), matching the
  Atlas top-level toolchain pin.
- Mathlib: `v4.35.0` line (source project pin:
  `074063781836922cb02701cd12943c9f51731afa`).
- MathlibExt: **not used** — this formalization uses Mathlib only.

No per-folder `lakefile.toml` / `lean-toolchain` /
`lake-manifest.json` is included, per the Atlas top-level pins.
In the source project, `Formalization/` serves as the Lake source
root (`lake build` there builds the root module and all sections).
The challenge compiles standalone with a Mathlib-only search path
(exit 0 with the single expected `sorry` warning); the endpoint audit
runs there with `lake env lean Verification/EndpointAudit.lean` from
the project root.
