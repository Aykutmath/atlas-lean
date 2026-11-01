# Section 11 — Sharpness

Paper §11 proves Proposition 11.1: the constant `(d+1)/2^d` is optimal
in every dimension (even on `{0,1\}^d`), via the spike laws
`ν_ε = (1-dε)δ_0 + ε∑δ_{e_j}`, and so is the one-coordinate constant
`(d+1)/(2d)`. Equality holds for every law in dimension one and for
the uniform measure on the square in dimension two.

## Reading order

1. `Sharp.lean` — main-constant optimality and equality cases.
2. `SharpOnestep.lean` — one-coordinate constant optimality (needs the
   projected spike law).

## Main declarations

All in namespace `HypercubeInequality`:

| Paper | Lean | File | Coverage |
|---|---|---|---|
| §11 proof, extremizing ratio limit | `sharpRatio` | `Sharp.lean` | HI-SHARP-RATIO |
| §11 Prop 11.1, optimality of `(d+1)/2^d` | `sharp_optimal` | `Sharp.lean` | HI-SHARP |
| §11, equality cases d=1 and square | `oneDimS_eq_gap`, `squareS` | `Sharp.lean` | HI-SHARP-EQ |
| §11 Prop 11.1, one-coordinate optimality | `sharp_onestep_optimal`, `proj_spike`, `map_projDrop_vertMeas` | `SharpOnestep.lean` | HI-SHARP-ONESTEP |
