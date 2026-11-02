import BMSymmetricFiniteUniversality
import BMNetGroundExtension
import GOEUniformL1

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMFiniteGibbsTest BMFiniteGibbsHessian
open BMFiniteUniversality BMGaussianEquivalent BMUniformMoment BMGOEUniform
open BMSymmetricFiniteUniversality BMNetGroundExtension GaussianMixedNormHelpers Filter
open scoped BigOperators BoundedContinuousFunction

namespace BMContinuumExpectations
local instance {d : ℕ} : DecidableEq (SymOp d) := Classical.decEq _
local instance {d : ℕ} : NormedAddCommGroup (SymOp d) :=
  Submodule.normedAddCommGroup (symmetricOperators d)
local instance {d : ℕ} : NormedSpace ℝ (SymOp d) :=
  Submodule.normedSpace (symmetricOperators d)

/-- Continuum minimum potential under actual iid rank-one Gaussian rows. -/
def quadraticContinuumExpectation (P : Data2 Unit) (d n : ℕ) (B : Set (SymOp d)) : ℝ :=
  ∫ x : Fin (n+1) → BMQuadraticSpectral.Euclid d,
    ground B (energy d (fun i => quadraticRow (x i)) P.potential)
      ∂gaussianSampleLaw d (n+1)

/-- Continuum minimum potential under actual iid symmetric Gaussian rows. -/
def goeContinuumExpectation (P : Data2 Unit) (d n : ℕ) (B : Set (SymOp d)) : ℝ :=
  ∫ z : Fin (n+1) → (Fin (d*d) → ℝ),
    ground B (energy d (fun i => goeRow (z i)) P.potential)
      ∂goeSampleLaw d (n+1)

def quadraticNetExpectation (P : Data2 Unit) (d n : ℕ)
    (t : Finset (SymOp d)) (ht : t.Nonempty) : ℝ :=
  ∫ x : Fin (n+1) → BMQuadraticSpectral.Euclid d,
    netGround t ht (energy d (fun i => quadraticRow (x i)) P.potential)
      ∂gaussianSampleLaw d (n+1)

def goeNetExpectation (P : Data2 Unit) (d n : ℕ)
    (t : Finset (SymOp d)) (ht : t.Nonempty) : ℝ :=
  ∫ z : Fin (n+1) → (Fin (d*d) → ℝ),
    netGround t ht (energy d (fun i => goeRow (z i)) P.potential)
      ∂goeSampleLaw d (n+1)

theorem quadraticNetExpectation_eq_finite (P : Data2 Unit) (d n : ℕ)
    (t : Finset (SymOp d)) (ht : t.Nonempty) :
    letI : Nonempty {T // T ∈ t} := ht.to_subtype
    quadraticNetExpectation P d n t ht =
      euclideanQuadraticGroundExpectation P d n (fun T : {T // T ∈ t} => T.val) := by
  letI : Nonempty {T // T ∈ t} := ht.to_subtype
  unfold quadraticNetExpectation euclideanQuadraticGroundExpectation
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [netGround_eq_finite_ground]
    rfl

theorem goeNetExpectation_eq_finite (P : Data2 Unit) (d n : ℕ)
    (t : Finset (SymOp d)) (ht : t.Nonempty) :
    letI : Nonempty {T // T ∈ t} := ht.to_subtype
    goeNetExpectation P d n t ht =
      goeGroundExpectation P d n (fun T : {T // T ∈ t} => matrixOf T.val) := by
  letI : Nonempty {T // T ∈ t} := ht.to_subtype
  unfold goeNetExpectation goeGroundExpectation
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [netGround_eq_finite_ground]
    rfl

/-- Actual net comparison inherited from the source-law finite-state theorem. -/
theorem net_expectation_universality (P : Data2 Unit) (n : ℕ → ℕ)
    (t : (d : ℕ) → Finset (SymOp d)) (ht : ∀ d, (t d).Nonempty)
    {K α C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hT : ∀ d T, T ∈ t d → ‖T‖ ≤ K)
    (hn : ∀ d, 0 < d → (n d+1 : ℕ) ≤ α*(d:ℝ)^2)
    (hcard : ∀ d, 0 < d → Real.log ((t d).card : ℝ) ≤ C*(d:ℝ)^2) :
    Tendsto (fun d => |quadraticNetExpectation P d (n d) (t d) (ht d)-
      goeNetExpectation P d (n d) (t d) (ht d)|) atTop (nhds 0) := by
  let κ := fun d => {T // T ∈ t d}
  letI (d : ℕ) : Nonempty (κ d) := (ht d).to_subtype
  have h := finite_symmetric_ground_expectation_universality κ P n
    (fun d (T : κ d) => T.val) hK hC (fun d T => hT d T.val T.property) hn
    (fun d hd => by simpa only [κ,Fintype.card_coe] using hcard d hd)
  simpa only [quadraticNetExpectation_eq_finite,goeNetExpectation_eq_finite] using h

#print axioms quadraticNetExpectation_eq_finite
#print axioms goeNetExpectation_eq_finite
#print axioms net_expectation_universality
end BMContinuumExpectations
