import BelowThresholdProjectFinal
import UniformConicBoundUnconditional

/-! The unchanged current project's strict-threshold theorem, with all
project-specific mathematical premises discharged by kernel-checked proofs. -/
noncomputable section
set_option autoImplicit false
namespace GaussianEllipsoid

/-- The paper's actual strict-threshold proposition, unconditionally proved. -/
theorem strict_threshold_unconditional : StrictThresholdStatement :=
  strict_threshold_of_discharged_HWDS mixedNormBound_unconditional
    bmApproximateFitting_unconditional uniformConicBound_unconditional

#print strict_threshold_unconditional
#print axioms mixedNormBound_unconditional
#print axioms bmApproximateFitting_unconditional
#print axioms uniformConicBound_unconditional
#print axioms below_threshold_unconditional
#print axioms strict_threshold_unconditional
end GaussianEllipsoid
