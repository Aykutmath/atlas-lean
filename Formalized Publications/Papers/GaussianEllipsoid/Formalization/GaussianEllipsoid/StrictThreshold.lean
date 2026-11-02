/-
The strict-threshold theorem (paper Theorem 1.1), conditional on the
five interface premises: the four below-threshold premises (Sections 4,
11, 12, and Bandeira-Maillard) plus the Section 16 uniform conic bound.
Both directions are proved assemblies; this file only conjoins them.
Mathematical source: paper.tex, Theorem 1.1.
-/
import GaussianEllipsoid.BelowAssembly
import GaussianEllipsoid.AboveAssembly

noncomputable section

namespace GaussianEllipsoid

/-- Theorem 1.1, both strict-threshold directions, conditional on the
five interface premises. -/
theorem strict_threshold_conditional
    (hMixed : MixedNormBound) (hHuber : HuberResiduals)
    (hQuot : QuotientBridge)
    (hBM : bmApproximateFitting) (hConic : UniformConicBound) :
    StrictThresholdStatement :=
  ⟨below_threshold_conditional hMixed hHuber hQuot hBM,
    above_threshold_conditional hConic⟩

end GaussianEllipsoid
