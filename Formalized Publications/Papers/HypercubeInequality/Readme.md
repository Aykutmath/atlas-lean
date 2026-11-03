# The Hypercube Inequality via Signed Simplex Cocycles

A Lean formalization of the October 29, 2026 paper.

[Paper (PDF)](Papers/hypercube_inequality.pdf) |
[Interactive paper (HTML)](Papers/hypercube_inequality_interactive.html) |
[Lean formalization](Formalization/) |
[Citation](Papers/citation.bib)

## Main result

**Theorem 1.1: Random-simplex inequality.** For every Borel probability law
$\nu$ on $\mathbb{R}^d$, with $d \ge 1$,

$$
S_d(\nu) \le \frac{d+1}{2^d}\prod_{j=1}^d D_j(\nu).
$$

Here $S_d$ is the expected volume of the convex hull of $d+1$ independent
samples, and $D_j$ is the mean absolute difference between two independent
samples' $j$th coordinates. No moment assumption is required.

Lean theorem:
[`HypercubeInequality.main_full`](Formalization/Section_7_Approximation/Approx.lean#L2504-L2508).

## Authorship

Paper and formalization: Aykut Arslan, with Muse Spark assistance.
Mathematical review: Dinh Pham and Juan Torres Toral.

## Versions

- Lean: `v4.35.0`.
- Mathlib: `074063781836922cb02701cd12943c9f51731afa`.
- MathlibExt: not used.

## Independent comparator

The [challenge](Comparator/hypercube_inequality_comparator.lean) restates the
main theorem and its required definitions, importing only Mathlib. Its single
`sorry` is a challenge placeholder, not a proof in the formalization.

On Linux with bubblewrap, from a Lake workspace configured to build this
paper's `HypercubeInequality` and `hypercube_inequality_comparator` modules:

```sh
lake comparator --config "Formalized Publications/Papers/HypercubeInequality/Comparator/hypercube_inequality_comparator.json"
```

The Atlas root's default build does not automatically include this paper.
