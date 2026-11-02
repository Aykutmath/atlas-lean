import BMProjectLawBridge
import GaussianEllipsoid.BelowObjects

/-!
# Unconditional BM for the authoritative current project

This module imports the actual complete BelowObjects interface. It packages
the independently proved original-coordinate Gaussian BM formula into exactly
that interface, preserving the common positive spectral box before every
real exponent 1 <= r < 4/3. No interface replacement or analytic input is used.
-/
noncomputable section
open scoped BigOperators ENNReal
namespace GaussianEllipsoid

/-- The proved original-coordinate BM formula is the exact named proposition
in the current BelowObjects file, with one positive box before every r. -/
theorem bmApproximateFitting_unconditional : bmApproximateFitting := by
  intro n hn hr
  obtain ⟨lo,hi,hlo,hlohi,hfit⟩ := bmApproximateFitting_coordinate_formula n hn hr
  refine ⟨lo,hi,hlo,hlohi,?_⟩
  intro r hr1 hr43 ε hε
  simpa only [bmMinRisk, spectralBox, Set.mem_ofPred_eq, exists_prop, and_assoc] using
    hfit r hr1 hr43 ε hε

end GaussianEllipsoid
