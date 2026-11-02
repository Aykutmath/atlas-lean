import MixedNormBasicBridge
import GaussianEllipsoid.NormBridges

/-!
Exact equality with the variational nuclearNorm from the supplied NormBridges.
NormBridgesLean419 is an explicitly recorded full API/syntax port of that
source; all definitions and mathematical theorem statements are unchanged.
-/
noncomputable section
set_option synthInstance.maxSize 1000
set_option maxHeartbeats 600000
open GaussianEllipsoid GaussianEllipsoidCandidate
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoidCoordinateBridge

/-- The supplied Euclidean norm is literally sqrt(sum of squares). -/
theorem project_euclidNorm_eq {n : ℕ} (y : GaussianEllipsoid.Vector n) :
    GaussianEllipsoid.euclidNorm y = Real.sqrt (∑ i, y i^2) := rfl

/-- The actual project operator norm is the norm of the Euclidean matrix map. -/
theorem project_matrixOpNorm_eq {d : ℕ} (A : GaussianEllipsoid.Square d) :
    GaussianEllipsoid.matrixOpNorm A = ‖GaussianEllipsoid.SmallBall.matrixCLM A‖ := rfl

/-- Ordinary matrix conversion is inverse to Euclidean matrix realization. -/
theorem frobeniusToMatrix_operatorFrobenius_matrixCLM {r q : ℕ}
    (A : Matrix (Fin r) (Fin q) ℝ) :
    frobeniusToMatrix (operatorFrobenius (GaussianEllipsoid.SmallBall.matrixCLM A)) = A := by
  ext a b
  change (Matrix.toEuclideanLin A (EuclideanSpace.basisFun (Fin q) ℝ b)) a = A a b
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    EuclideanSpace.basisFun_apply]

/-- The actual Frobenius pairing is exactly the coordinate pairing used in the
project's variational definition, with both index orders accounted for. -/
theorem frobenius_inner_eq_coordinate {r q : ℕ} (A B : FrobeniusMatrix r q) :
    ⟪A,B⟫_ℝ = ∑ i, ∑ j, frobeniusToMatrix B i j * frobeniusToMatrix A i j := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_comm

/-- Matrix-form version of the exact pairing identity. -/
theorem matrixCLM_frobenius_inner {d : ℕ} (A U : GaussianEllipsoid.Square d) :
    ⟪operatorFrobenius (GaussianEllipsoid.SmallBall.matrixCLM A),
      operatorFrobenius (GaussianEllipsoid.SmallBall.matrixCLM U)⟫_ℝ =
      ∑ i, ∑ j, U i j * A i j := by
  rw [frobenius_inner_eq_coordinate,
    frobeniusToMatrix_operatorFrobenius_matrixCLM,
    frobeniusToMatrix_operatorFrobenius_matrixCLM]

/-- Exact spectral/variational equality. The reverse inequality is certified
by the actual proved polar witness, not by a spectral-duality assumption. -/
theorem project_nuclearNorm_eq_coordinate {d : ℕ} (A : GaussianEllipsoid.Square d) :
    GaussianEllipsoid.nuclearNorm A = coordinateNuclearNorm A := by
  let F := operatorFrobenius (GaussianEllipsoid.SmallBall.matrixCLM A)
  have hF : spectralNuclearNorm F = coordinateNuclearNorm A := by
    unfold spectralNuclearNorm coordinateNuclearNorm F
    rw [frobeniusOperator_operatorFrobenius]
  apply le_antisymm
  · unfold GaussianEllipsoid.nuclearNorm
    apply csSup_le (GaussianEllipsoid.nuclearNorm_nonempty A)
    rintro t ⟨U,hU,rfl⟩
    rw [← matrixCLM_frobenius_inner A U, ← hF]
    exact inner_operator_le_nuclear F (GaussianEllipsoid.SmallBall.matrixCLM U)
      (by rwa [← project_matrixOpNorm_eq])
  · let W := polarWitness (GaussianEllipsoid.SmallBall.matrixCLM A)
    let U := frobeniusToMatrix (operatorFrobenius W)
    have hWU : GaussianEllipsoid.SmallBall.matrixCLM U = W := by
      dsimp [U]
      rw [matrixCLM_frobeniusToMatrix, frobeniusOperator_operatorFrobenius]
    have hU : GaussianEllipsoid.matrixOpNorm U ≤ 1 := by
      rw [project_matrixOpNorm_eq, hWU]
      exact norm_polarWitness_le _
    have hp : coordinateNuclearNorm A = ∑ i, ∑ j, U i j*A i j := by
      rw [← matrixCLM_frobenius_inner A U, hWU, ← hF]
      symm
      change ⟪F,operatorFrobenius (polarWitness
        (GaussianEllipsoid.SmallBall.matrixCLM A))⟫_ℝ = spectralNuclearNorm F
      have he : frobeniusOperator F = GaussianEllipsoid.SmallBall.matrixCLM A :=
        frobeniusOperator_operatorFrobenius _
      rw [← he]
      exact inner_polarWitness_eq_nuclear F
    rw [hp]
    exact GaussianEllipsoid.nuclearNorm_lower A U hU

/-- The actual current Basic adjoint and actual variational project nuclear
norm agree exactly with the independently proved standalone spectral bound. -/
theorem project_centeredAdjoint_nuclear {d n : ℕ} (x : GaussianEllipsoid.Sample d n)
    (y : GaussianEllipsoid.Vector n) (hy : (∑ i, y i) = 0) :
    GaussianEllipsoid.nuclearNorm (GaussianEllipsoid.centeredAdjoint x y) =
      spectralNuclearNorm (GaussianEllipsoidStandalone.centeredAdjoint
        (BMBoxRiskAssembly.sampleEuclideanEquiv d n x) y) := by
  rw [project_nuclearNorm_eq_coordinate, basic_centeredAdjoint_nuclear x y hy]

end GaussianEllipsoidCoordinateBridge
