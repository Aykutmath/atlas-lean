import MixedNormNuclearBridge
import GaussianEllipsoid.GaussianProbability

/-!
Current-project law/nuclear/Basic names with the literal mixed-cost formula.
The supplied NormBridges and GaussianProbability are imported through explicitly
named complete Lean4.19 compatibility modules. This is not an assertion that
the unchanged full active-project import graph compiles on that toolchain.
-/
noncomputable section
set_option synthInstance.maxSize 1000
open MeasureTheory Filter GaussianEllipsoid
open scoped BigOperators ENNReal Topology
namespace GaussianEllipsoidCoordinateBridge

/-- The actual current project Gaussian law is definitionally the exact
ordinary-coordinate iid Gaussian law used in the proved coordinate theorem. -/
theorem project_gaussianSampleLaw_eq_coordinate (d n : ℕ) :
    GaussianEllipsoid.gaussianSampleLaw d n = BMBoxRiskAssembly.coordinateSampleLaw d n := rfl

/-- Exact actual-project source-law transport to the proved Euclidean law. -/
theorem project_gaussianSampleLaw_measurePreserving (d n : ℕ) :
    MeasurePreserving (BMBoxRiskAssembly.sampleEuclideanEquiv d n)
      (GaussianEllipsoid.gaussianSampleLaw d n)
      (GaussianEllipsoidStandalone.gaussianSampleLaw d n) := by
  rw [project_gaussianSampleLaw_eq_coordinate]
  exact coordinateSampleLaw_measurePreserving d n

/-- Unconditional literal mixed-norm estimate using the actual current project
Gaussian law, aspect ratio, coordinate types, Euclidean norm, centered adjoint,
and variational nuclear norm. No analytic/probabilistic input remains. -/
theorem project_literal_mixedNormBound :
    ∀ n : ℕ → ℕ, (∀ d, 0 < n d) →
      limsup (GaussianEllipsoid.dimensionRatio n) atTop < (1/4:ℝ≥0∞) →
      ∀ δ > 0, ∃ η c : ℝ, ∃ G : ∀ d, Set (GaussianEllipsoid.Sample d (n d)),
        0 < η ∧ η < 1 ∧ 0 < c ∧
        (∀ d, MeasurableSet (G d)) ∧
        limsup (fun d => ((GaussianEllipsoid.gaussianSampleLaw d (n d)) (G d)ᶜ).toReal)
          atTop ≤ δ ∧
        ∀ d, ∀ x ∈ G d, ∀ y : GaussianEllipsoid.Vector (n d), (∑ i, y i) = 0 →
          c*(sInf {w : ℝ | ∃ u v : GaussianEllipsoid.Vector (n d), y = u+v ∧
            w = η*Real.sqrt (d:ℝ)*(∑ i, |u i|) + (d:ℝ)*GaussianEllipsoid.euclidNorm v}) ≤
            GaussianEllipsoid.nuclearNorm (GaussianEllipsoid.centeredAdjoint x y) := by
  intro n hn haspect δ hδ
  obtain ⟨η,c,G,hη,hη1,hc,hG,hlim,hb⟩ := basic_coordinate_mixedNormBound n hn haspect δ hδ
  refine ⟨η,c,G,hη,hη1,hc,hG,?_,?_⟩
  · exact hlim
  · intro d x hx y hy
    rw [project_nuclearNorm_eq_coordinate]
    exact hb d x hx y hy

end GaussianEllipsoidCoordinateBridge
