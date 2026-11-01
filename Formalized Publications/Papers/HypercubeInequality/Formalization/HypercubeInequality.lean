/-
# Hypercube Inequality formalization — library root

Single-project Atlas-style layout: `Formalization/` is the Lake source root
and this file imports every section module in paper order (Sections 1-12).
Paper correspondence and build instructions: see `../Readme.md`; the
interactive paper rendering is `../Papers/hypercube_inequality_interactive.html`.

Namespaces inside the section files are unchanged (`HypercubeInequality`,
`Cor101`, `Hypercube`), so fully-qualified theorem names are unchanged;
only the module import paths reflect the new layout.
-/

-- Section 1 — Introduction (core definitions)
import Section_1_Introduction.Core
import Section_1_Introduction.Basic

-- Section 2 — Signed simplex cancellation
import Section_2_Cocycle.Cocycle
import Section_2_Cocycle.CocycleRefine

-- Section 3 — Exterior-algebra Bernoulli estimate
import Section_3_LocalEstimate.Local
import Section_3_LocalEstimate.Lagrange
import Section_3_LocalEstimate.SimplexVolume

-- Section 4 — The binary determinant inequality
import Section_4_BernoulliCounting.Counting

-- Section 5 — From binary labels to real heights
import Section_5_Layercake.Layercake

-- Section 6 — The one-coordinate inequality
import Section_6_OneStep.Onestep

-- Section 7 — Approximation by finite laws
import Section_7_Approximation.Approx

-- Section 8 — Induction and proof of the main theorem
import Section_8_MainTheorem.Induction

-- Section 9 — Hypercube specialization
import Section_9_Hypercube.Cube

-- Section 10 — The zonoid projection formulation
-- Independent supporting results (not the Section 10 discharge)
import Section_10_Zonoid.Zonoid
import Section_10_Zonoid.ZonoidGeom
-- Section 10 discharge: Corollary 10.1 (`Cor101.corollary10_1`)
import Section_10_Zonoid.Cor101.Corollary
import Section_10_Zonoid.Cor101.Definitions
import Section_10_Zonoid.Cor101.Normalization
import Section_10_Zonoid.Cor101.GeneratorGeometry
import Section_10_Zonoid.Cor101.Images
import Section_10_Zonoid.Cor101.FiniteBridge
import Section_10_Zonoid.Cor101.Translation
import Section_10_Zonoid.Cor101.Perturbation
import Section_10_Zonoid.Cor101.Sharpness
import Section_10_Zonoid.Cor101.LineVolume
import Section_10_Zonoid.Cor101.VolumeInterface
import Section_10_Zonoid.Cor101.PlaneVolume
import Section_10_Zonoid.Cor101.DeterminantCoordinates
import Section_10_Zonoid.Cor101.GeometricBridgeAudit
import Section_10_Zonoid.Cor101.LimitAssembly
import Section_10_Zonoid.Cor101.LineVolumeAudit
import Section_10_Zonoid.Cor101.PlaneVolumeAudit
import Section_10_Zonoid.Cor101.ProjectionContinuity
import Section_10_Zonoid.Cor101.SharpnessAudit
import Section_10_Zonoid.Cor101.VolumeContinuity
import Section_10_Zonoid.Cor101.VolumeContinuityAudit
import Section_10_Zonoid.Cor101.ZonotopeDeterminants
import Section_10_Zonoid.Cor101.ZonotopeExtrusion
import Section_10_Zonoid.Cor101.ZonotopeProjection
import Section_10_Zonoid.Cor101.ZonotopeVolume
-- Vendored dependency development (`Hypercube.Main.random_simplex`)
import Section_10_Zonoid.Hypercube.Main
import Section_10_Zonoid.Hypercube.Algebra.Basic
import Section_10_Zonoid.Hypercube.Algebra.BinaryCocycle
import Section_10_Zonoid.Hypercube.Algebra.Counting
import Section_10_Zonoid.Hypercube.Algebra.OrthogonalExterior
import Section_10_Zonoid.Hypercube.Algebra.Signs
import Section_10_Zonoid.Hypercube.Approximation
import Section_10_Zonoid.Hypercube.Bernoulli
import Section_10_Zonoid.Hypercube.BernoulliGeometry
import Section_10_Zonoid.Hypercube.BernoulliGeometryAudit
import Section_10_Zonoid.Hypercube.BinaryLift
import Section_10_Zonoid.Hypercube.Constants
import Section_10_Zonoid.Hypercube.CubeEndpoint
import Section_10_Zonoid.Hypercube.CubeNormalization
import Section_10_Zonoid.Hypercube.CubeRepresentation
import Section_10_Zonoid.Hypercube.EndpointAssembly
import Section_10_Zonoid.Hypercube.Examples
import Section_10_Zonoid.Hypercube.ExteriorBridge
import Section_10_Zonoid.Hypercube.FiniteAtomic
import Section_10_Zonoid.Hypercube.FiniteAtomicGeneric
import Section_10_Zonoid.Hypercube.FiniteProjectedHeight
import Section_10_Zonoid.Hypercube.FiniteProjectedHeightAudit
import Section_10_Zonoid.Hypercube.FiniteThreshold
import Section_10_Zonoid.Hypercube.FiniteThresholdAudit
import Section_10_Zonoid.Hypercube.GapZero
import Section_10_Zonoid.Hypercube.GapZeroAudit
import Section_10_Zonoid.Hypercube.Geometry
import Section_10_Zonoid.Hypercube.Geometry.AffineDeterminant
import Section_10_Zonoid.Hypercube.Geometry.AffineRankBridge
import Section_10_Zonoid.Hypercube.Geometry.AffineVolume
import Section_10_Zonoid.Hypercube.Geometry.AffineVolumeAudit
import Section_10_Zonoid.Hypercube.Geometry.BoundaryNull
import Section_10_Zonoid.Hypercube.Geometry.Cocycle
import Section_10_Zonoid.Hypercube.Geometry.FiberStep
import Section_10_Zonoid.Hypercube.Geometry.FiberStructure
import Section_10_Zonoid.Hypercube.Geometry.FiniteCocycle
import Section_10_Zonoid.Hypercube.Geometry.NullFaces
import Section_10_Zonoid.Hypercube.Geometry.OrientationBridge
import Section_10_Zonoid.Hypercube.Geometry.RadonMass
import Section_10_Zonoid.Hypercube.Geometry.TestFunctionBridge
import Section_10_Zonoid.Hypercube.Geometry.VolumeBridge
import Section_10_Zonoid.Hypercube.Moments
import Section_10_Zonoid.Hypercube.MomentsAudit
import Section_10_Zonoid.Hypercube.Optimality
import Section_10_Zonoid.Hypercube.OwnRowIndependence
import Section_10_Zonoid.Hypercube.OwnRowIndependenceAudit
import Section_10_Zonoid.Hypercube.PaperIntegrability
import Section_10_Zonoid.Hypercube.PaperLawBridge
import Section_10_Zonoid.Hypercube.PaperTheorems
import Section_10_Zonoid.Hypercube.Regressions
import Section_10_Zonoid.Hypercube.RegressionsAudit
import Section_10_Zonoid.Hypercube.Representation
import Section_10_Zonoid.Hypercube.Sampling
import Section_10_Zonoid.Hypercube.Sharpness
import Section_10_Zonoid.Hypercube.SpikeCounting
import Section_10_Zonoid.Hypercube.SpikeLaw.Basic
import Section_10_Zonoid.Hypercube.SpikeLaw.Cube
import Section_10_Zonoid.Hypercube.SpikeLaw.Gaps
import Section_10_Zonoid.Hypercube.SpikeLaw.Optimality
import Section_10_Zonoid.Hypercube.SpikeLaw.Projection
import Section_10_Zonoid.Hypercube.SpikeLaw.Volume
import Section_10_Zonoid.Hypercube.Statements
import Section_10_Zonoid.Hypercube.Thresholds
import Section_10_Zonoid.Hypercube.ThresholdsAudit

-- Section 11 — Sharpness
import Section_11_Sharpness.Sharp
import Section_11_Sharpness.SharpOnestep

-- Section 12 — Projection monotonicity
import Section_12_Ratios.Ratios
import Section_12_Ratios.SubsetRatios
