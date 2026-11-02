/-
Below-threshold final assembly: the conditional theorem with the
Section 4 Huber residuals, the deleted-selector measurability, and the
Section 12 quotient bridge discharged by their proved theorems.

- `huberResiduals_theorem` (`HuberDischarge`, Section 4) replaces the
  `HuberResiduals` premise, conditional on the two remaining Section 4
  externals (`davidsonSzarekCovariance`, `hansonWrightChaos`) as `Prop`
  premises.
- `deletedSelectorMeasurable_theorem` (`SelectorMeasurable`, Section 4)
  discharges the deleted-selector premise unconditionally (no Berge
  theorem needed: constant compact box + joint continuity + ridge
  uniqueness give selector continuity via a cluster-point argument).
- `quotientBridge_theorem` (`QuotientDischarge`, Section 12) replaces
  the `QuotientBridge` premise unconditionally.

`hansonWrightChaos_theorem` (`HansonWright`) discharges the chaos
premise, giving the 4-premise variants `below_threshold_of_discharged_HW`
and `strict_threshold_of_discharged_HW`.

`huberResiduals_unconditional` (`DSABThread`) discharges Section 4 fully:
the exact `(4,4)` premise is bypassed via the `(A,B)`-generalized route
(`davidsonSzarekCovariance_gen` at `(450/97, 900/97)`, proved from
`dsPerCenterTail_theorem`), giving the 3-premise variants
`below_threshold_of_discharged_HWDS` and
`strict_threshold_of_discharged_HWDS`.

Remaining premises: `MixedNormBound` (Section 11), `bmApproximateFitting`
(Bandeira-Maillard), `UniformConicBound` (Section 16).
`below_threshold_conditional` itself is unchanged.
Mathematical source: paper.tex, Sections 2, 4, and 12.
-/
import GaussianEllipsoid.StrictThreshold
import GaussianEllipsoid.HuberDischarge
import GaussianEllipsoid.SelectorMeasurable
import GaussianEllipsoid.QuotientDischarge
import GaussianEllipsoid.HansonWright
import GaussianEllipsoid.DSABThread

noncomputable section

namespace GaussianEllipsoid

/-- Below-threshold direction with `HuberResiduals`,
`deletedSelectorMeasurable`, and `QuotientBridge` discharged. -/
theorem below_threshold_of_discharged (hMixed : MixedNormBound)
    (hBM : bmApproximateFitting) (hDS : davidsonSzarekCovariance)
    (hHW : hansonWrightChaos) :
    BelowThresholdStatement :=
  below_threshold_conditional hMixed
    (huberResiduals_theorem hDS deletedSelectorMeasurable_theorem hHW)
    quotientBridge_theorem hBM

/-- Theorem 1.1 with `HuberResiduals`, `deletedSelectorMeasurable`, and
`QuotientBridge` discharged. -/
theorem strict_threshold_of_discharged (hMixed : MixedNormBound)
    (hBM : bmApproximateFitting) (hConic : UniformConicBound)
    (hDS : davidsonSzarekCovariance)
    (hHW : hansonWrightChaos) : StrictThresholdStatement :=
  strict_threshold_conditional hMixed
    (huberResiduals_theorem hDS deletedSelectorMeasurable_theorem hHW)
    quotientBridge_theorem hBM hConic

/-- Below-threshold direction with `hansonWrightChaos` discharged by
`HansonWright.hansonWrightChaos_theorem` (4 premises remain). -/
theorem below_threshold_of_discharged_HW (hMixed : MixedNormBound)
    (hBM : bmApproximateFitting) (hDS : davidsonSzarekCovariance) :
    BelowThresholdStatement :=
  below_threshold_of_discharged hMixed hBM hDS hansonWrightChaos_theorem

/-- Theorem 1.1 with `hansonWrightChaos` discharged by
`HansonWright.hansonWrightChaos_theorem` (4 premises remain:
`MixedNormBound`, `bmApproximateFitting`, `UniformConicBound`,
`davidsonSzarekCovariance`). -/
theorem strict_threshold_of_discharged_HW (hMixed : MixedNormBound)
    (hBM : bmApproximateFitting) (hConic : UniformConicBound)
    (hDS : davidsonSzarekCovariance) : StrictThresholdStatement :=
  strict_threshold_of_discharged hMixed hBM hConic hDS
    hansonWrightChaos_theorem

/-- Below-threshold direction with Section 4 fully discharged
(`huberResiduals_unconditional`: 3 premises remain). -/
theorem below_threshold_of_discharged_HWDS (hMixed : MixedNormBound)
    (hBM : bmApproximateFitting) :
    BelowThresholdStatement :=
  below_threshold_conditional hMixed
    huberResiduals_unconditional
    quotientBridge_theorem hBM

/-- Theorem 1.1 with Section 4 fully discharged
(`huberResiduals_unconditional`: 3 premises remain:
`MixedNormBound`, `bmApproximateFitting`, `UniformConicBound`). -/
theorem strict_threshold_of_discharged_HWDS (hMixed : MixedNormBound)
    (hBM : bmApproximateFitting) (hConic : UniformConicBound) :
    StrictThresholdStatement :=
  strict_threshold_conditional hMixed
    huberResiduals_unconditional
    quotientBridge_theorem hBM hConic

end GaussianEllipsoid
