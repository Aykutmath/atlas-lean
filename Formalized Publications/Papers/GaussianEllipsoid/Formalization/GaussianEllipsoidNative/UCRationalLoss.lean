import UCFreeEnergyBridge
import BMRationalLossData

/-! Fixed bounded C² rational loss for the UC argument. No new smoothing
hypothesis is needed: the literal potential and derivatives are constructed. -/
noncomputable section
open BMFiniteGibbsTest BMFiniteGibbsHessian BMProductLogPartition BMClippedL1Bridge
open scoped BigOperators BoundedContinuousFunction
namespace GaussianEllipsoid.UCRationalLoss

/-- The unshifted rational loss is 1-Lipschitz. -/
theorem smoothLoss_lipschitz : LipschitzWith 1 smoothLoss := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (smoothLoss_hasDerivAt t).differentiableAt)
  intro t
  exact_mod_cast smoothLoss_abs_deriv_le_one t

 theorem smoothLoss_abs_sub (x y : ℝ) : |smoothLoss x-smoothLoss y| ≤ |x-y| := by
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using smoothLoss_lipschitz.dist_le_mul x y

 theorem smoothLoss_le_abs (x : ℝ) : smoothLoss x ≤ |x| := by
  have h := smoothLoss_abs_sub x 0
  simpa only [smoothLoss_zero, sub_zero, abs_of_nonneg (smoothLoss_nonneg x)] using h

variable {κ : Type*} [Fintype κ] [Nonempty κ]

def uniformData (β : ℝ) (hβ : 0 ≤ β) : Data2 κ :=
  BMRationalLossData.data2 (fun _ => (Fintype.card κ:ℝ)⁻¹)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by simp [ne_of_gt (Fintype.card_pos (α := κ))]) β hβ

@[simp] theorem uniformData_weight (β : ℝ) (hβ : 0 ≤ β) (a : κ) :
    (uniformData (κ := κ) β hβ).weight a = (Fintype.card κ:ℝ)⁻¹ := rfl
@[simp] theorem uniformData_beta (β : ℝ) (hβ : 0 ≤ β) :
    (uniformData (κ := κ) β hβ).beta = β := rfl
@[simp] theorem uniformData_potential (β : ℝ) (hβ : 0 ≤ β) (x : ℝ) :
    (uniformData (κ := κ) β hβ).potential x = smoothLoss (x-1) := rfl

 theorem uniformData_loss_bounds (β : ℝ) (hβ : 0 ≤ β) (x : ℝ) :
    0 ≤ (uniformData (κ := κ) β hβ).potential x ∧
      (uniformData (κ := κ) β hβ).potential x ≤ 1 :=
  ⟨smoothLoss_nonneg _, (smoothLoss_lt_one _).le⟩

/-- The normalized comparison constant is independent of the candidate type,
its cardinality, its prior support, and the sample dimension. -/
def normalizedComparisonConstant (β : ℝ) (hβ : 0 ≤ β) : ℝ :=
  UCActualFreeEnergy.comparisonConstant (BMRationalLossData.unitData2 β hβ)/β

 theorem uniformData_comparisonConstant (β : ℝ) (hβ : 0 ≤ β) :
    UCActualFreeEnergy.comparisonConstant (uniformData (κ := κ) β hβ)/β =
      normalizedComparisonConstant β hβ := rfl

 theorem normalizedComparisonConstant_nonneg (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ normalizedComparisonConstant β hβ := by
  have h1 := diagonalPriorConstant_nonneg (BMRationalLossData.unitData2 β hβ)
  have h2 := pairPriorConstant_nonneg (BMRationalLossData.unitData2 β hβ)
  unfold normalizedComparisonConstant UCActualFreeEnergy.comparisonConstant
  positivity

/-- Exact alignment of the rational residual loss with the existing uniform
candidate free energy, via the harmless deterministic +1 row shift. -/
theorem uniformData_freeEnergy [DecidableEq κ] (β : ℝ) (hβ : 0 ≤ β) {n : ℕ}
    (q v : Fin n → κ → ℝ) :
    UCActualFreeEnergy.freeEnergy (uniformData (κ := κ) β hβ).toData
      (fun i a => q i a + (1-v i a)) =
    FiniteFreeEnergy.freeEnergy β n
      (FiniteFreeEnergy.totalLoss (fun i a => smoothLoss (q i a-v i a))) := by
  rw [UCFreeEnergyBridge.freeEnergy_eq_project _ (fun a => rfl)]
  congr 1
  funext a
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [uniformData_potential]
  congr 1
  ring

#print axioms smoothLoss_lipschitz
#print axioms uniformData_freeEnergy
end GaussianEllipsoid.UCRationalLoss
