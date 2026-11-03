# Alpha-Cycle — Tightness of the Cycle-Based Relaxation for Completed Length-Three Alpha-Cycles

Formalization of the paper's sharp classification (Paper Theorem 2.4):
for a completed length-three alpha-cycle, the distinguished-cycle
relaxation and the all-cycles relaxation each equal the completed
polytope if and only if every pair-only block is a singleton.
Main theorem: `AlphaCycle.PaperHypergraph.paper_sharp_classification`
in `Formalization/Section_6_MainTheorem/PaperMain.lean`.

Authors: Aykut Arslan (orchestrating author), Meta AI;
reviewing author: Kien Le (per `Papers/Latex/main.tex`).

## Layout

- `Formalization/` — the proved solution: 45 Lean modules (44 section
  modules plus the `AlphaCycle` root). Byte-identical to the verified
  source snapshot; no `sorry`, `admit`, `native_decide`, or custom
  axioms. Only the three standard axioms occur transitively
  (`propext`, `Classical.choice`, `Quot.sound`).
- `Comparator/` — the independent main-theorem challenge plus the
  strict comparator configuration and the reproduction driver. See
  `Comparator/README.md`.
- `Verification/` — build scripts (`build_solution.sh`,
  `build_challenge.sh`), the 4.34 export serializer (`export34.lean`,
  byte-identical to the verified Gaussian serializer), the export
  completeness checker (`check_exports.py`), and the proof audits
  (`CheckCoverage.lean`, `CheckAxioms.lean`).
- `Papers/` — the paper PDF with matching LaTeX sources and citation,
  the self-contained interactive HTML rendering (offline math typeset,
  statement boxes with source links), and `verification.json` with the
  recorded verification evidence.
- `LICENSE` — Apache 2.0.

## Pins (exact)

- Lean for elaboration and both exports: `v4.34.0-rc2`, commit
  `6a10ac8c22beadecabdbb0919c2b50214762f91d`
  (`leanprover/lean4:v4.34.0-rc2`), `autoImplicit false`.
- External dependencies (nine packages):
  mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`,
  plausible `d9598f07b1bc701f1e3aae163d2681c1fd978793`,
  LeanSearchClient `ba67e212be1197b84c1f1f6299488a10a3002713`,
  importGraph `d8823026ac7ef130c253089d95685f9877b95323`,
  proofwidgets `a8acbfd87375ff4abe14ce09db5b7664d383bc7f`,
  aesop `18889deb9e83ea7420ef51c160d6f88552e744e3`,
  Qq `507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3`,
  batteries `d54dddc581e08be364c278052863524bff7a99a9`,
  Cli `ab3a82db9fea14cf0fd7f5a2de650f4b534640af`.
- Official judge: Lean `v4.35.0`, commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, with `bwrap` sandbox
  (Linux only).

No per-folder lakefile/lean-toolchain/lake-manifest is included, per
the Atlas top-level pins. There is deliberately no 4.35 source port:
the solution is elaborated once under the original 4.34 pin, exported
with the 4.34 serializer (untrusted NDJSON data, never a 4.34 olean
loaded into 4.35), and judged by the official 4.35 `lake comparator`.

## Assembling the externals search path

Build each of the nine pinned external packages with the pinned 4.34
toolchain (e.g. in throwaway checkouts pinned to the revisions above
via their own lake manifests), then set `EXTERNALS_LEAN_PATH` to the
colon-separated list of their `.lake/build/lib/lean` output
directories. The reproduction driver (`Comparator/reproduce.sh`)
validates this path before use: every entry must be an absolute,
existing directory outside the package and its build outputs, and at
least one entry must contain the pinned `Mathlib.olean`. The challenge
and solution builds use externals-only search paths plus their own
scratch build outputs — the challenge build never sees the solution
sources or outputs, and the solution build never sees the challenge.

## Reproduce

```
sh Comparator/reproduce.sh <this-directory> <work-dir>
```

with `LEAN34` set to the pinned 4.34 binary and `EXTERNALS_LEAN_PATH`
as assembled above. This rebuilds the solution (expects zero `sorry`)
and the challenge (expects exactly the one authorized `sorry`),
exports both with the 4.34 serializer (completeness- and
determinism-checked), and — on Linux with `LAKE35`/`LEAN35`/`bwrap` —
runs the official `lake comparator` for the fixed strict config
(`challenge_module='alpha_cycle_comparator'`,
`solution_module='AlphaCycle'`,
`theorem_names=['AlphaCycle.PaperHypergraph.paper_sharp_classification']`,
`definition_names=[]`,
`permitted_axioms=['propext','Classical.choice','Quot.sound']`).
Off Linux it stops after the exports (exit 2, never a passing
verdict). `Comparator/negative_controls.sh` (Linux only) runs the
five semantic negative controls N1–N5 against the official judge.
`Comparator/test_reproduce.py` checks the driver's own guards with
stubbed tools (driver only; the proof verdict comes solely from the
official judge).

## Status of this package

`Papers/verification.json` records the evidence: Atlas-layout rebuild,
axiom audit, coverage audit, HTML rendering checks, export hashes, the
official positive judge run, and the five negative controls. References
are the last section of the paper, and the main prose carries no audit
section or status banner.
