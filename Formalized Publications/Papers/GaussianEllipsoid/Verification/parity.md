# Serializer parity record

`export34.lean` (this directory) serializes original-pin 4.34
environments to the official 4.35 NDJSON export format 3.1.0. This
file records the practical parity evidence against the official 4.35
`leanexport`, plus one documented upstream boundary.

## Fixture

`parity_fixture.lean`: Lean-core-only declarations (plain `Nat` defs,
universe-polymorphic `ident`, `opaque` `Nat`, `Nat` literals, a
`let`-binding, separate `rfl` theorems, no conjunctions, structures,
or string computation). It compiles under both the original 4.34
toolchain and 4.35 with no Mathlib. An earlier fixture variant with a
conjunction statement and `String` append computation is discussed
under "Upstream boundary" below.

## Results

All runs below use the exact default comparator roots for their
config (kernel builtins ++ named theorems ++ permitted axioms ++
kernel primitives). Hashes are sha256 of the NDJSON exports.

- 4.34 serializer output, self-judged by the official 4.35
  `lake comparator` (default kernel, `bwrap` sandbox): exit 0,
  `Lean default kernel accepts the solution`, `Your solution is okay!`
  (proves 4.35-kernel validity of 4.34-serialized output).
- Official 4.35 `leanexport` output of the same fixture: kernel
  accepts (exit 0).
- Cross-judge (official 4.35 export as challenge, 4.34 serializer
  export as solution): every fixture-module constant matches exactly
  (9/9: 4 definitions including 1 opaque + 5 theorems, types and full
  bodies), except one upstream core constant (below).
- Determinism: repeated 4.34 serializer runs are byte-identical.

## Sole divergence: `And.casesOn` core drift (upstream, not serializer)

The cross-judge reports
`Const does not match between challenge and target 'And.casesOn'`.
Both bodies are faithfully serialized genuine elaborations:

- 4.35: `casesOn` implemented via structure projections
  (`(app (app b0 (proj b1)) (proj b1))`).
- 4.34: `casesOn` implemented via `And.rec` application.

This is a 4.34 → 4.35 core library change. It enters any `Nat`
closure through compiler-generated match splitters (e.g. under the
`Nat.div` primitives), so no cross-version closure equality is
achievable in general. The comparator catching it demonstrates the
comparison is body-sensitive: a wrong body with the right type does
not pass. The real Gaussian judge compares 4.34 against 4.34, where
no such drift exists.

## Upstream boundary: string-append defeq in replay

A fixture variant whose theorem proof needed kernel defeq through
`String.append`/ByteArray computation (`greet "yo" = "hi yo"` by
`rfl`) makes the official replay demand `String.ofList` although no
exported term references it (verified by exhaustive cross-check of
the export). Plain string literals are unaffected (a minimal string
fixture passes). The Gaussian proof is pure analysis with no string
computation and does not touch that path; the committed fixture
avoids it. This quirk lives entirely in the official
exporter/checker pair and is recorded here so future reruns are not
mystified by it.
