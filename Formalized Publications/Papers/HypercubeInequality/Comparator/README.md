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

`hypercube_inequality_comparator.json`:

- `theorem_names`: `["HypercubeInequality.main_full"]`
- `definition_names`: `[]` (deliberately empty — see below)
- `permitted_axioms`: `["propext", "Classical.choice", "Quot.sound"]`
  (never `sorryAx`)
- `challenge_module`: `hypercube_inequality_comparator`,
  `solution_module`: `HypercubeInequality`

The challenge source declares exactly two `def`s and one `theorem`
(elaboration adds two auxiliary theorems, `S._proof_1/2`, present
identically in both exports).

## Why `definition_names` is empty (fixed definitions, not holes)

In the comparator, every name in `definition_names` is a definition
*HOLE*: only the name, type signature, and safety are compared —
the body is deliberately skipped. Registering `S`/`gap` as holes
would therefore check signatures only, and a wrong body with the
right type would still pass. Since `S` and `gap` are explicitly and
independently defined here to mean the paper's literal expectations
(§1 Eq.(1)/(2)), they must NOT be holes: with `definition_names`
empty, both are traversed from `main_full` as ordinary fixed
constants and compared by full structural equality, bodies included,
recursively. An earlier configuration with the two names as holes
also passed, but it checked types only; the strict configuration
below is the real bar.

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
export roots `lake comparator` uses for this config (kernel
builtins ++ the named theorem ++ permitted axioms ++ kernel
primitives; the definitions are reached through the theorem, not
listed as holes). The exact working procedure is
[reproduce.sh](reproduce.sh); abbreviated root lists do not work —
the exporter needs every root the comparator traverses.

Export bindings (sha256; produced by [reproduce.sh](reproduce.sh),
verified by the strict run below):

- challenge source `hypercube_inequality_comparator.lean`:
  `e0f752a539157be9fecfe3eb02a8035ca82973bc6f9186cf53febd1826c09da9`
- `challenge.ndjson`:
  `314ee9d135f34c804dda8bcf08dd948fccd5f45cf0fbda0a1ba2aad8ed80ae97`
  (162 MB; exactly one `sorryAx`, the authorized placeholder; an
  earlier export with `S`/`gap` as explicit extra roots,
  `57f9cfcb…`, passes identically — they add no new nodes beyond
  `main_full`'s closure)
- solution `HypercubeInequality.olean`:
  `c20c7304a84df5d6eca4b19a395b9be89930a547b1ca00c795e811e6780ae93b`
- `solution.ndjson`:
  `0a52c36bff65ec45af8dabfaf689aa6a7d30b70a5ab786dd508ee2daf52fe6f0`
  (301 MB; zero `sorryAx`)

The real `lake comparator` ran on Linux (Lean 4.35.0 toolchain,
`eb6cafb...`, bwrap sandbox active, default kernels) from those
exports, under both the hole configuration (types only) and the
strict configuration (bodies included):

```sh
lake comparator --config hypercube_inequality_comparator.json \
  --challenge-from-export challenge.ndjson \
  --solution-from-export solution.ndjson
# Running Lean default kernel on solution
# Lean default kernel accepts the solution
# Your solution is okay!
# EXIT: 0
```

Strict verdict: the solution proves the challenge statement with
definitions whose full bodies match the independent challenge
bodies, on the standard axioms only, accepted by the kernel.

## Negative controls (same `lake comparator`, same Linux host)

All run in isolated scratch (never in `Formalization/`); each is
expected to be REJECTED (nonzero exit):

| Control | Tamper | Result |
|---|---|---|
| A-real | challenge recompiled with `(m + 2 : ℕ)` → `(m + 3 : ℕ)` (`6a52a3…`) | REJECT, exit 1: `Challenge and solution theorem statement do not match: 'HypercubeInequality.main_full'` |
| A-syn | Nat literal `2` → `3` in challenge export (`3fad99f8…`) | REJECT, exit 1: statement mismatch, same message |
| B-def | `S` domain `ℕ` → `ℝ` in challenge export (`95cc7f7f…`) | REJECT, exit 1: `Const does not match between challenge and target 'HypercubeInequality.S'` |
| B-body | `S` body replaced by `0` (same type), recompiled in scratch (`0a9caccd…`) | REJECT, exit 1: `Const does not match between challenge and target 'HypercubeInequality.S'` |
| C-sorry | sorry-proved `main_full` judged as the solution | REJECT, exit 1: `Illegal axiom detected: 'sorryAx'` |

Controls A-real/A-syn/B-def/C-sorry ran under the hole
configuration; B-body runs under the strict configuration and is
the genuine semantic check: same name, same type, different body —
rejected. Together they evidence the comparison is sensitive to the
statement, the required definitions' bodies, and proof admissions:
a wrong body, coefficient, or definition cannot pass as green.

Note: flipping only the explicit/implicit binder marker on `S`
(equivalently, stating `S` with `{d : ℕ}` — verified both by a
compiled variant, `e94cbc09…`, which passes with exit 0, and by the
equivalent export edit) still passes: the comparator compares
definition bodies up to binder names and binder markers. That is
tool semantics, not a gap in this challenge.

## Reproducing

From-source `lake comparator` needs a Lake project wiring
`challenge_module` and `solution_module` plus a `lake-manifest.json`
(this package carries Atlas top-level pins instead). Run
[reproduce.sh](reproduce.sh) with the source project root and a
scratch dir; on Linux+bwrap it executes the full chain and reports
every step's real exit code. A compilation, export, or comparison
failure stops the script immediately with a nonzero exit; a platform
without Linux+bwrap prints the exact command and exits 2, not a passing
verdict. Driver error handling is tested separately with stub executables:
`python3 test_reproduce.py` (this driver test is not a Lean proof check).
Re-exports from these sources with the same toolchain and pins must reproduce
`challenge.ndjson` / `solution.ndjson` bytes above.
