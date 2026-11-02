import MixedNormProjectLiteral
import GaussianEllipsoid.MixedNormAsm

/-!
# Unconditional MixedNormBound for the authoritative current project

This module imports the actual complete BelowObjects/MixedNormAsm interface,
not an extracted or replacement statement. The Gaussian estimates used by
MixedNormProjectLiteral are the proved decoupled rectangular bilinear estimates
on independent coordinate blocks, followed by the proved nuclear compression
and exact current-project law/norm identifications. No legacy symmetric-T*
continuity or per-support small-ball premise is used.

The independent proof uses the even half-dimension 2*floor(d/4); its actual
orthogonal block extraction and all-dimension finite-prefix handling are
already proved. The final event is allowed by the existential MixedNormBound
statement and does not assume the project's overbroad bhatAdaptEngine.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace GaussianEllipsoid

/-- The authoritative mixed norm is exactly the literal infimal mixed cost
already proved in the decoupled Gaussian engine. l1Size is the actual definition
from the current Centering.lean, rather than an assumed coordinate identity. -/
theorem mixedNorm_eq_literal_coordinate_cost (η : ℝ) (d n : ℕ) (y : Vector n) :
    mixedNorm η d n y =
      sInf {w : ℝ | ∃ u v : Vector n, y = u+v ∧
        w = η*Real.sqrt (d:ℝ)*(∑ i, |u i|) + (d:ℝ)*euclidNorm v} := rfl

/-- Concrete good events for the exact current body, with measurability also
established. All mathematical inputs are discharged by proved theorems. -/
theorem mixedNormBody_unconditional_measurable
    (n : ℕ → ℕ) (hn : ∀ d, 0 < n d)
    (hr : Filter.limsup (dimensionRatio n) Filter.atTop < (1/4:ℝ≥0∞))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η c : ℝ, ∃ G : ∀ d, Set (Sample d (n d)),
      MixedNormBody n δ η c G ∧ (∀ d, MeasurableSet (G d)) := by
  obtain ⟨η,c,G,hη,hη1,hc,hG,hProb,hPoint⟩ :=
    GaussianEllipsoidCoordinateBridge.project_literal_mixedNormBound n hn hr δ hδ
  refine ⟨η,c,G,?_,hG⟩
  apply mnasM_body_of_parts hη hη1 hc hProb
  intro d x hx y hy
  rw [mixedNorm_eq_literal_coordinate_cost]
  exact hPoint d x hx y hy

/-- Section 11's exact current-project proposition, now with no analytic,
probabilistic, comparison, clipping, norm-identification or assembly premise. -/
theorem mixedNormBound_unconditional : MixedNormBound := by
  intro n hn hr δ hδ
  obtain ⟨η,c,G,hBody,_⟩ := mixedNormBody_unconditional_measurable n hn hr δ hδ
  exact ⟨η,c,G,hBody⟩

end GaussianEllipsoid
