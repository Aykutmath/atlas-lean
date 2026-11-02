# Comparator — verification receipt

Independent Atlas-style challenge for the Hypercube Inequality
(Paper Theorem 1.1, `HypercubeInequality.main_full`).

## What is checked

`hypercube_inequality_comparator.lean` states the paper-facing
definitions `HypercubeInequality.S` (§1 Eq.(1)) and
`HypercubeInequality.gap` (§1 Eq.(2)) **independently in the challenge
file** — it imports only Mathlib, never the solution in
`Formalization/` — and states `HypercubeInequality.main_full` with
those challenge definitions, proved with `sorry`. `sorry` is
authorized in this challenge file only; the solution contains no
`sorry`, `admit`, `native_decide`, or custom axioms.

`hypercube_inequality_comparator.json` names exactly one theorem and
two definitions, with the standard axiom basis:

- `theorem_names`: `["HypercubeInequality.main_full"]`
- `definition_names`: `["HypercubeInequality.S", "HypercubeInequality.gap"]`
- `permitted_axioms`: `["propext", "Classical.choice", "Quot.sound"]`
  (never `sorryAx`)
- `challenge_module`: `hypercube_inequality_comparator`,
  `solution_module`: `HypercubeInequality`

The challenge source declares exactly two `def`s and one `theorem`
(elaboration adds two auxiliary theorems, `S._proof_1/2`, present
identically in both exports).

## Actual runs (2026-11-02)

Pins: Lean `v4.35.0` (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`),
Mathlib `074063781836922cb02701cd12943c9f51731afa`.
Solution built from the source project at `hypercube-atlas-unified`
`fa3d175` (`lake build HypercubeInequality`, 9159 jobs, exit 0);
`Formalization/` here is byte-identical to that build
(`diff -rq` clean).

`lake comparator` sandboxes with `bwrap` (Linux-only), so it cannot
run on macOS without `--inadvisably-no-sandbox` (never used). The
challenge was compiled on macOS with a Mathlib-only search path
(no project oleans/sources):

```sh
lean -o hypercube_inequality_comparator.olean \
  hypercube_inequality_comparator.lean   # exit 0, one `sorry` warning
```

and both modules were exported with `leanexport` using exactly the
export roots `lake comparator` uses (builtins ++ theorems ++
permitted axioms ++ kernel primitives ++ definitions):

```sh
leanexport hypercube_inequality_comparator -- Quot Quot.mk ... \
  HypercubeInequality.S HypercubeInequality.gap > challenge.ndjson
leanexport HypercubeInequality -- Quot Quot.mk ... \
  HypercubeInequality.S HypercubeInequality.gap > solution.ndjson
```

Export bindings (sha256):

- challenge source `hypercube_inequality_comparator.lean`:
  `e0f752a539157be9fecfe3eb02a8035ca82973bc6f9186cf53febd1826c09da9`
- `challenge.ndjson`:
  `57f9cfcb1a3a7a1ec990e3ddd471b9792500d28765a66d781de6569327aa80ed`
  (162 MB; exactly one `sorryAx`, the authorized placeholder)
- solution `HypercubeInequality.olean`:
  `c20c7304a84df5d6eca4b19a395b9be89930a547b1ca00c795e811e6780ae93b`
- `solution.ndjson`:
  `0a52c36bff65ec45af8dabfaf689aa6a7d30b70a5ab786dd508ee2daf52fe6f0`
  (301 MB; zero `sorryAx`)

The real `lake comparator` ran on Linux (Lean 4.35.0 toolchain,
`eb6cafb...`, bwrap sandbox active, default kernels) from those
exports:

```sh
lake comparator --config hypercube_inequality_comparator.json \
  --challenge-from-export challenge.ndjson \
  --solution-from-export solution.ndjson
# Running Lean default kernel on solution
# Lean default kernel accepts the solution
# Your solution is okay!
# EXIT: 0
```

Verdict: the solution proves the challenge statement with the
challenge definitions' names and signatures, on the standard axioms
only, and is accepted by the kernel.

## Negative controls (same `lake comparator`, same Linux host)

All run in isolated scratch (never in `Formalization/`); each is
expected to be REJECTED (nonzero exit):

| Control | Tamper | Result |
|---|---|---|
| A-real | challenge recompiled with `(m + 2 : ℕ)` → `(m + 3 : ℕ)` (`6a52a3…`) | REJECT, exit 1: `Challenge and solution theorem statement do not match: 'HypercubeInequality.main_full'` |
| A-syn | Nat literal `2` → `3` in challenge export (`3fad99f8…`) | REJECT, exit 1: statement mismatch, same message |
| B-def | `S` domain `ℕ` → `ℝ` in challenge export (`95cc7f7f…`) | REJECT, exit 1: `Const does not match between challenge and target 'HypercubeInequality.S'` |
| C-sorry | sorry-proved `main_full` judged as the solution | REJECT, exit 1: `Illegal axiom detected: 'sorryAx'` |

A rejected altered control evidences the comparison is sensitive to
the statement, the required definitions, and proof admissions: a
wrong definition or coefficient cannot pass as green.

Note: flipping only the explicit/implicit binder marker on `S`
(equivalently, stating `S` with `{d : ℕ}` — verified both by a
compiled variant, `e94cbc09…`, which passes with exit 0, and by the
equivalent export edit) still passes: the comparator compares
definition types up to binder names and binder markers. That is tool
semantics, not a gap in this challenge.

## Reproducing

From-source `lake comparator` needs a Lake project wiring
`challenge_module` and `solution_module` plus a `lake-manifest.json`
(this package carries Atlas top-level pins instead). The from-export
run above is reproducible from the recorded export hashes: any
re-export from these sources with the same toolchain and pins must
reproduce the `challenge.ndjson` / `solution.ndjson` bytes, after
which the quoted `lake comparator` command applies unchanged.
