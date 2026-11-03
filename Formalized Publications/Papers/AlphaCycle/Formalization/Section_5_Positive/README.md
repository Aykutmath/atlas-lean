# Section 5 — Positive direction: the singleton case

Paper §5 proves exactness when $|A|=|B|=|C|=1$: conditioning on the common
block $T$ reduces to the private-free singleton case (Lemma 5.1), in every
$T$-slice a feasible interval of triple masses is nonempty (Lemma 5.2), and
slice laws glue to a global realization, with private blocks restored by
conditional sampling (Proposition 5.3).

## Contents

- `PositiveSlice.lean` — slice moments, pair bounds, conditions, interval
  endpoints, atoms (`interval_nonempty`).
- `Singleton.lean` — singleton-case assembly from slices.
- `PaperKernels.lean`, `PaperSlices.lean` — conditional kernels and the
  slice-mass calculus (`each_lower_le_each_upper`).
- `PrivateBlocks.lean` — private-block restoration
  (`restore_private_blocks`).
- `SliceBridge.lean` — bridge between slice data and singleton assembly.
- `Positive.lean` — local tables, joint construction.
- `PositiveTheorem.lean` — exactness of both relaxations in the singleton
  case (`distinguished_exact_of_singletons`,
  `allCycle_exact_of_singletons`).

## Main declarations

All in namespace `AlphaCycle` unless noted:

| Paper | Lean | File |
|---|---|---|
| §5, Lemma 5.1 (private-block reduction) | `PaperGeometry.singleton_private_block_reduction`, `restore_private_blocks` | `PaperGeometry.lean` (§2), `PrivateBlocks.lean` |
| §5, Lemma 5.2 (slice feasibility) | `PositiveSlice.interval_nonempty`, `PaperSlices.each_lower_le_each_upper` | `PositiveSlice.lean`, `PaperSlices.lean` |
| §5, Prop 5.3 (singleton exactness) | `distinguished_exact_of_singletons`, `allCycle_exact_of_singletons` | `PositiveTheorem.lean` |
