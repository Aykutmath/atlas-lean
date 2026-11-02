# The Strict Threshold for Gaussian Ellipsoid Fitting

Formalization of the supplied manuscript
[*The Strict Threshold for Gaussian Ellipsoid Fitting*](Papers/gaussian_ellipsoid.pdf)
(the formalized, interactive edition is
[gaussian_ellipsoid_interactive.html](Papers/gaussian_ellipsoid_interactive.html);
BibTeX: [citation.bib](Papers/citation.bib)).

## Summary

Let $x_1,\ldots,x_n$ be independent $N(0,I_d)$ vectors. The paper studies
whether there exists a positive semidefinite matrix $S$ with
$x_i^T S x_i = d$ for every $i$, and proves a sharp threshold at
$n \sim d^2/4$: below $1/4$ a positive definite fit exists with
probability tending to one; above $1/4$ no PSD fit exists with
probability tending to one. No claim is made at the critical ratio.
The argument runs through a convex robust-loss (Huber) estimator with
residual bounds, arbitrary-center determinant small-ball estimates,
localized and multiscale uniform estimates, a bilinear-block comparison,
quotient duality, an above-threshold infeasibility chain, a leave-one-row
cavity comparison, and a diffuse-to-full-PSD passage. Every numbered
claim of the manuscript is formalized and kernel-checked in Lean; no
`sorry`, `admit`, `native_decide`, or custom axioms are used, and all
endpoints depend only on the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

## Results

| Paper claim | Lean endpoint | Source |
| --- | --- | --- |
| Theorem 1.1 (strict threshold, both directions) | `GaussianEllipsoid.strict_threshold_unconditional : GaussianEllipsoid.StrictThresholdStatement` | [StrictThresholdProjectFinal.lean](Formalization/GaussianEllipsoidNative/StrictThresholdProjectFinal.lean) |
| Theorem 1.1(i) (below threshold) | `GaussianEllipsoid.below_threshold_unconditional : GaussianEllipsoid.BelowThresholdStatement` | [BelowThresholdProjectFinal.lean](Formalization/GaussianEllipsoidNative/BelowThresholdProjectFinal.lean) |
| Theorem 1.1 statement targets | `GaussianEllipsoid.StrictThresholdStatement`, `GaussianEllipsoid.BelowThresholdStatement`, `GaussianEllipsoid.AboveThresholdStatement` | [PaperMain.lean](Formalization/GaussianEllipsoid/PaperMain.lean) |
| Mixed-norm discharge | `GaussianEllipsoid.mixedNormBound_unconditional : GaussianEllipsoid.MixedNormBound` | [MixedNormProjectFinal.lean](Formalization/GaussianEllipsoidNative/MixedNormProjectFinal.lean) |
| Robust-loss discharge | `GaussianEllipsoid.bmApproximateFitting_unconditional : GaussianEllipsoid.bmApproximateFitting` | [BMProjectFinal.lean](Formalization/GaussianEllipsoidNative/BMProjectFinal.lean) |
| Conic-bound discharge | `GaussianEllipsoid.uniformConicBound_unconditional : GaussianEllipsoid.UniformConicBound` | [UniformConicBoundUnconditional.lean](Formalization/GaussianEllipsoidNative/UniformConicBoundUnconditional.lean) |
| AHH equation (11), unconditional | `AHHRadial.paper_equation11` | [AHHExactEquation11Unconditional.lean](Formalization/GaussianEllipsoidNative/AHHExactEquation11Unconditional.lean) |

All 48 paper assertions (40 named statements + 8 supplemental AHH
displays, 167 Lean declarations) appear as Lean boxes in the
[interactive edition](Papers/gaussian_ellipsoid_interactive.html), each
with `source` buttons into `Formalization/`. The full row-to-declaration
map is [Papers/inventory.json](Papers/inventory.json) and
[Verification/inventory.json](Verification/inventory.json);
per-section module indexes live in `Formalization/Section_*/README.md`.

## Layout

- `Papers/` — the supplied manuscript PDF, the interactive HTML edition
  (its Lean boxes carry `source` buttons linking into `Formalization/`),
  `citation.bib`, `inventory.json`, and `verification.json`.
  `Papers/generate_html.py` reproducibly assembles the HTML from
  `prose_template.html`, `inventory.json`, the `Formalization/`
  sources (`python3 Papers/generate_html.py`; `--check` verifies the
  checked-in HTML is current). References is the final section; build,
  axiom and coverage records stay separately in `Papers/verification.json`
  and `Comparator/`, not in the interactive paper.
  `Papers/derive_template.py` is the one-time derivation of the prose
  template from the supplied manuscript rendering (see its header).
  KaTeX libraries and all 20 font faces are embedded, so math renders
  offline. Regression checks:
  `python3 Papers/test_html_rendering.py`; add `--browser` on a machine
  with Playwright and Chromium for a real offline rendering check.
- `Papers/Latex/` — `main.tex` (the supplied source, byte-identical to
  the authoritative manuscript), plus its required `stylelibrary.tex`,
  `flexart.sty`, `ulem.sty`, `bib.bib`/`refs.bib`, `settings.tex`,
  `readme-library.tex`, and `BUILD_PDF.md`. `Papers/gaussian_ellipsoid.pdf`
  is a byte-identical copy of the supplied 62-page PDF.
- `Formalization/` — the Lean development, moved byte-for-byte from the
  source project: the root module
  [GaussianEllipsoid.lean](Formalization/GaussianEllipsoid.lean),
  the paper-facing `GaussianEllipsoid/` folder (47 modules), and the
  backend `GaussianEllipsoidNative/` folder (723 modules).
  Namespaces are unchanged, so fully-qualified theorem names are exactly
  as checked. `Section_*/README.md` files index the modules behind each
  paper section; `FILE_MAP.md` records the move;
  `check_preservation.py` re-verifies byte identity, import closure, and
  the absence of `sorry`/`admit`/`native_decide`/custom axioms;
  `make_section_index.py` regenerates the section indexes.
- `Comparator/` — the independent Atlas-style challenge
  ([gaussian_ellipsoid_comparator.lean](Comparator/gaussian_ellipsoid_comparator.lean)
  with [gaussian_ellipsoid_comparator.json](Comparator/gaussian_ellipsoid_comparator.json)):
  the paper-facing definitions restated under the same names importing
  only Mathlib, with the main theorem (`strict_threshold_unconditional`,
  both strict-threshold directions) proved by `sorry`; the official
  `lake comparator` judges the solution against it. See
  [Comparator/README.md](Comparator/README.md); the exact procedure is
  [Comparator/reproduce.sh](Comparator/reproduce.sh).
- `Verification/` — the endpoint audit
  ([EndpointAudit.lean](Verification/EndpointAudit.lean):
  `#check`/`#print axioms` inspections of the headline endpoints above,
  importing the solution by design) with the 48-row declaration
  inventory ([inventory.json](Verification/inventory.json),
  built by [make_inventory.py](Verification/make_inventory.py)), plus
  the 4.34 NDJSON serializer ([export34.lean](Verification/export34.lean))
  and its parity record ([parity.md](Verification/parity.md),
  fixture [parity_fixture.lean](Verification/parity_fixture.lean)).

## Authorship

- Paper and formalization: Aykut Arslan, with Muse Spark (as credited in
  the manuscript).
- Mathematical review of the manuscript: Babak Modami, Alexander
  Roitershtein, Mark Sepanski, and Grigory Sokolov (reviewing authors,
  as credited in the manuscript).

## Versions

- Lean: `leanprover/lean4:v4.34.0-rc2`, matching the source project pin.
- Mathlib: source project pin `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
- Atlas toolchain gap: the Atlas default Lean (`v4.35.0`) is NEWER than
  this package's pin and no source port was performed; the independent
  comparator instead serializes original-4.34 elaborations with the
  faithful 4.34 serializer (`Verification/export34.lean`) and judges
  those exports with the official 4.35 `lake comparator` (default
  kernel, `bwrap` sandbox). See `Comparator/README.md`.

No per-folder `lakefile.toml` / `lean-toolchain` / `lake-manifest.json`
is included, per the Atlas top-level pins. To verify, assemble a scratch
Lake project whose source root holds `GaussianEllipsoid.lean`,
`GaussianEllipsoid/` and `GaussianEllipsoidNative/` with the pins above
(the source project's `lakefile.toml` / `lean-toolchain` /
`lake-manifest.json`), then from the scratch root run
`Comparator/reproduce.sh <project-root> <work-dir>` (with `Comparator/`
and `Verification/` copied alongside): it compiles the challenge with an
externals-only search path (exactly one authorized `sorry`), exports
challenge and solution with the 4.34 serializer, and — on Linux with
`bwrap` — runs the official judge. Expected: exit 0 throughout, with
the solution depending only on `propext`, `Classical.choice`, and
`Quot.sound`. (On this laptop the Lake 5.0.0-src driver in the pinned
toolchain crashes while loading any workspace with dependencies, so the
rebuild is driven by direct `lean` elaboration in topological order
against rev-matched prebuilt oleans; the `lake` recipe above stands for
machines where Lake works. See `Papers/verification.json` for the
recorded outcome.)
