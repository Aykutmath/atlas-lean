import MixedNormProjectFinal
import BMProjectFinal
import GaussianEllipsoid.BelowFinal

/-!
# Exact below-threshold assembly for the authoritative current project

Both formerly external below-threshold inputs are supplied by the actual
proved Gaussian engines. The current project's own BelowFinal theorem then
uses its already discharged Huber, selector, quotient, Hanson-Wright and
Davidson-Szarek chains. No original project definition or import is replaced.
-/
noncomputable section
open scoped BigOperators ENNReal
namespace GaussianEllipsoid

/-- The actual current below-threshold proposition, with no remaining
MixedNorm, BM, Huber, concentration, selector or quotient premise. -/
theorem below_threshold_unconditional : BelowThresholdStatement :=
  below_threshold_of_discharged_HWDS mixedNormBound_unconditional bmApproximateFitting_unconditional

/-- Explicit record of the sole remaining input for the two-sided theorem.
This is intentionally conditional; it makes no claim to discharge Section 16. -/
theorem strict_threshold_of_uniformConicBound (hConic : UniformConicBound) :
    StrictThresholdStatement :=
  strict_threshold_of_discharged_HWDS mixedNormBound_unconditional
    bmApproximateFitting_unconditional hConic

end GaussianEllipsoid
