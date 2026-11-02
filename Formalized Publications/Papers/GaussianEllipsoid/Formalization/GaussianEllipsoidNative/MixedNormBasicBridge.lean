import MixedNormCoordinateBridge
import GaussianEllipsoid.Basic

/-!
This module imports the user's current Basic.lean verbatim from a temporary
GaussianEllipsoid/Basic.lean module path. It does not import a replacement
BelowObjects or MixedNormAsm. The remaining names are visibly qualified as
coordinate law/norm until their exact current project definitions arrive.
-/
noncomputable section
set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000
open MeasureTheory Filter GaussianEllipsoid GaussianEllipsoidCandidate
open BMBoxRiskAssembly GaussianEllipsoidFinalPassage
open scoped BigOperators ENNReal Topology
namespace GaussianEllipsoidCoordinateBridge

/-- The actual current Basic.lean adjoint is exactly the literal ordinary
quadratic matrix. No zero-sum hypothesis is needed for this coordinate identity. -/
theorem basic_centeredAdjoint_eq_coordinate {d n : ℕ} (x : GaussianEllipsoid.Sample d n)
    (y : GaussianEllipsoid.Vector n) :
    GaussianEllipsoid.centeredAdjoint x y = coordinateQuadraticSynthesis x y := by
  ext a b
  simp only [GaussianEllipsoid.centeredAdjoint, coordinateQuadraticSynthesis,
    Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec, Matrix.of_apply,
    smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The centered Euclidean synthesis already proved by the decoupled argument
is the actual project's current adjoint on the required zero-sum subspace. -/
theorem standalone_centeredAdjoint_eq_basic {d n : ℕ} (x : GaussianEllipsoid.Sample d n)
    (y : GaussianEllipsoid.Vector n) (hy : (∑ i, y i) = 0) :
    frobeniusToMatrix (GaussianEllipsoidStandalone.centeredAdjoint
      (sampleEuclideanEquiv d n x) y) = GaussianEllipsoid.centeredAdjoint x y := by
  rw [centeredAdjoint_coordinate_matrix x y hy, basic_centeredAdjoint_eq_coordinate]

/-- Exact genuine nuclear correspondence for the actual current Basic adjoint.
The project's still-unseen nuclearNorm is not postulated or replaced here. -/
theorem basic_centeredAdjoint_nuclear {d n : ℕ} (x : GaussianEllipsoid.Sample d n)
    (y : GaussianEllipsoid.Vector n) (hy : (∑ i, y i) = 0) :
    coordinateNuclearNorm (GaussianEllipsoid.centeredAdjoint x y) =
      spectralNuclearNorm (GaussianEllipsoidStandalone.centeredAdjoint
        (sampleEuclideanEquiv d n x) y) := by
  rw [basic_centeredAdjoint_eq_coordinate, coordinateQuadraticSynthesis_nuclear x y hy]

/-- Exact actual-project aspect-ratio identity, including dimension zero. -/
theorem basic_dimensionRatio_eq (n : ℕ → ℕ) : GaussianEllipsoid.dimensionRatio n =
    fun d => (n d:ℝ≥0∞)/(d:ℝ≥0∞)^2 := rfl

/-- Unconditional current-Basic adjoint estimate, with literal mixed cost and
actual ordinary Gaussian source. This leaves no mathematical assumption;
identification of the remaining project names awaits their current sources. -/
theorem basic_coordinate_mixedNormBound :
    ∀ n : ℕ → ℕ, (∀ d, 0 < n d) →
      limsup (GaussianEllipsoid.dimensionRatio n) atTop < (1/4:ℝ≥0∞) →
      ∀ δ > 0, ∃ η c : ℝ, ∃ G : ∀ d, Set (GaussianEllipsoid.Sample d (n d)),
        0 < η ∧ η < 1 ∧ 0 < c ∧
        (∀ d, MeasurableSet (G d)) ∧
        limsup (fun d => (coordinateSampleLaw d (n d)).real (G d)ᶜ) atTop ≤ δ ∧
        ∀ d, ∀ x ∈ G d, ∀ y : GaussianEllipsoid.Vector (n d), (∑ i, y i) = 0 →
          c*(sInf {w : ℝ | ∃ u v : GaussianEllipsoid.Vector (n d), y = u+v ∧
            w = η*Real.sqrt (d:ℝ)*(∑ i, |u i|) + (d:ℝ)*Real.sqrt (∑ i, v i^2)}) ≤
            coordinateNuclearNorm (GaussianEllipsoid.centeredAdjoint x y) := by
  intro n hn haspect δ hδ
  obtain ⟨η,c,G,hη,hη1,hc,hG,hlim,hb⟩ := coordinate_mixedNormBound n hn haspect δ hδ
  refine ⟨η,c,G,hη,hη1,hc,hG,hlim,?_⟩
  intro d x hx y hy
  rw [basic_centeredAdjoint_eq_coordinate]
  exact hb d x hx y hy

end GaussianEllipsoidCoordinateBridge
