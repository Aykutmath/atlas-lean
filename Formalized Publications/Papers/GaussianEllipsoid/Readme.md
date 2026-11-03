# The Strict Threshold for Gaussian Ellipsoid Fitting

A Lean formalization of the paper's main strict-threshold theorem.

[Paper (PDF)](Papers/gaussian_ellipsoid.pdf) |
[Interactive paper (HTML)](Papers/gaussian_ellipsoid_interactive.html) |
[Lean formalization](Formalization/) |
[LaTeX](Papers/Latex/main.tex) |
[Citation](Papers/citation.bib)

## Main result

**Theorem 1.1: Strict threshold.** For independent $N(0,I_d)$ points,
if $\limsup n(d)/d^2 < 1/4$, a positive definite matrix $S$ satisfying
$x_i^T S x_i = d$ for every point exists with probability tending to one.
If $\liminf n(d)/d^2 > 1/4$, even a positive semidefinite fit exists with
probability tending to zero. No claim is made at the critical ratio.

Lean theorem:
[`GaussianEllipsoid.strict_threshold_unconditional`](Formalization/GaussianEllipsoidNative/StrictThresholdProjectFinal.lean#L11-L13).

## Authorship

Paper and formalization: Aykut Arslan, with Muse Spark assistance.
Mathematical review: Babak Modami, Alexander Roitershtein, Mark Sepanski,
and Grigory Sokolov.

## Versions

- Lean source pin: `v4.34.0-rc2`.
- Mathlib: `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
- MathlibExt: not used.

## Independent comparator

The [challenge](Comparator/gaussian_ellipsoid_comparator.lean) independently
restates the main theorem and its required definitions, importing only Mathlib.
Its single `sorry` is a challenge placeholder, not an unfinished solution.

The official Lean 4.35.0 comparator accepted exports compiled under the
source pin above. This is not a Lean 4.35.0 source port.

On Linux with bubblewrap and those original-pin exports, from the Atlas root:

```sh
lake comparator --config "Formalized Publications/Papers/GaussianEllipsoid/Comparator/gaussian_ellipsoid_comparator.json" --challenge-from-export challenge.ndjson --solution-from-export solution.ndjson
```

The Atlas root's default build does not automatically include this paper.
