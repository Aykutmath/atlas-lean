# Section 6 — The one-coordinate inequality

Paper §6 proves Theorem 6.1: for a finitely supported law `ν` with
projection `μ` onto the first `d-1` coordinates,
`S_d(ν) ≤ (d+1)/(2d) · D_d(ν) · S_{d-1}(μ)`.

## Reading order

- `Onestep.lean` — the only file in this section.

## Main declarations

All in namespace `HypercubeInequality`, file `Onestep.lean`:

| Paper | Lean | Coverage |
|---|---|---|
| §6 Thm 6.1, one-coordinate inequality | `oneStep` | HI-ONESTEP |
| §6/§8, `S_1 = D_1` base case (+ `S_0 = 1`) | `base_eq`, `base_le`, `S0_atomMeas` | HI-BASE |
