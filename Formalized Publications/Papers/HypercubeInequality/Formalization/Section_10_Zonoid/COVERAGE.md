# Corollary 10.1 coverage

**COMPLETE: `Cor101.corollary10_1 : Cor101.Corollary10_1`.**

`Cor101.corollary10_1_with_sharpness` combines validity in every `d ≥ 1` with
optimality of coefficient one. All theorem names below have prefix `Cor101.`.

| Mathematical step | Checked declaration |
|---|---|
| Ambient Euclidean sets; genuine projected intrinsic measures | `Space`, `fullVolume`, `lineVolume`, `planeVolume` (definitions) |
| Geometric zonoids as Hausdorff closure of translated zonotopes | `IsZonoid`; `isZonoid_iff_exists_zonotope_sequence` |
| Finite-law consequence of the supplied main theorem | `FiniteBridge.all_generators_determinant_inequality` |
| Segment extrusion, including degenerate sets | `Zonotope.volume_add_segment` |
| Arbitrary-generator geometric volume decomposition | `Zonotope.volume_finiteZonotope_subsets` |
| Ordered maximal-minor formula and factorial | `volume_parallelepiped_ordered` |
| Full zonotope volume required by the finite-law bridge | `fullVolume_zonotopeBody` |
| Genuine intrinsic line length | `lineVolume_zonotopeBody` |
| Planar area with the ordered-pair factor two | `planeVolume_zonotopeBody` |
| Finite geometric inequality, without extra assumptions | `projectionInequality_zonotopeBody` |
| Translation and arbitrary translated zonotopes | `projectionInequality_of_isZonotope` |
| Volume continuity, including lower-dimensional limits | `continuous_volume_convexBody`, `fullVolume_continuous` |
| Intrinsic line and plane continuity | `lineVolume_continuous`, `planeVolume_continuous` |
| Closedness and Hausdorff-limit assembly | `isClosed_projectionInequality`, `zonoid_projection_of_zonotope` |
| Full all-zonoid inequality | `corollary10_1` |
| d = 1 and zero-exponent convention | `projectionInequality_one` |
| Unit-box equality and optimality | `unitBox_projectionEquality`, `sharpProjectionConstant` |
| Validity and optimality together | `corollary10_1_with_sharpness` |

## Fidelity

- The final theorem assumes only `d ≥ 1` and the geometric zonoid property.
- `ConvexBody` includes lower-dimensional nonempty compact convex sets.
- The first d coordinates are indexed by `Fin d`; the common axis is `Fin.last d`.
- Projected measures use normalized Euclidean Hausdorff measure, proved equal to
  ordinary volumes in their one- and two-dimensional coordinate models.
- ENNReal-valued measures preserve ordinary volume, including its finiteness.
  Finiteness is proved before using real-valued closedness arguments.
- All generator labels, including zero, repeated and horizontal generators, are
  permitted. No rank or sign assumptions are hidden in the final theorem.
- The preserved earlier `zonotope_projection_of_volume_formulas` is an intermediate
  conditional theorem; its hypotheses are now discharged by the new actual-volume
  proofs. The main endpoint has none of those hypotheses.
- The proof is a deduction from the supplied checked Hypercube theorem; no new
  mathematical discovery or independent novelty claim is made.

## Verification scope

The new source and supplied project are compiled with pinned Lean/Mathlib.
The full theorem's transitive axiom set is exactly the three standard foundational
axioms. The library's official cache is used; this is not an independently rebuilt
Mathlib library or a second proof kernel. See verification logs and provenance.
