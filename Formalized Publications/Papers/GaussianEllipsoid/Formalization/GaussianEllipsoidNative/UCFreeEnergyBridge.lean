import UCActualFreeEnergy

/-! Exact compatibility between the actual-law Gibbs comparison and the
project's existing finite uniform free-energy algebra. -/
noncomputable section
open MeasureTheory BMFiniteGibbsTest BMFiniteGibbsHessian BMProductLogPartition
open scoped BigOperators BoundedContinuousFunction
namespace GaussianEllipsoid.UCFreeEnergyBridge
variable {κ : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ]

/-- The BM weighted partition specializes exactly to the project's uniform
candidate partition, including the normalization 1/|κ|. -/
theorem freeEnergy_eq_project (D : Data κ)
    (hweight : ∀ a, D.weight a = (Fintype.card κ : ℝ)⁻¹)
    {n : ℕ} (y : Fin n → κ → ℝ) :
    UCActualFreeEnergy.freeEnergy D y =
      FiniteFreeEnergy.freeEnergy D.beta n
        (FiniteFreeEnergy.totalLoss (fun i a => D.potential (y i a))) := by
  unfold UCActualFreeEnergy.freeEnergy fullLogPartition fullPartition
    FiniteFreeEnergy.freeEnergy FiniteFreeEnergy.partitionAverage
    FiniteFreeEnergy.partitionSum FiniteFreeEnergy.totalLoss rowSum
  simp only [hweight, ← Finset.mul_sum, div_eq_mul_inv, mul_comm]

/-- Uniform-prior free energy stays in the unit interval for bounded losses. -/
theorem freeEnergy_mem_unit_interval (D : Data κ)
    (hweight : ∀ a, D.weight a = (Fintype.card κ : ℝ)⁻¹)
    (hβ : 0 < D.beta) {n : ℕ} (hn : 0 < n)
    (hloss : ∀ t, 0 ≤ D.potential t ∧ D.potential t ≤ 1)
    (y : Fin n → κ → ℝ) :
    0 ≤ UCActualFreeEnergy.freeEnergy D y ∧ UCActualFreeEnergy.freeEnergy D y ≤ 1 := by
  rw [freeEnergy_eq_project D hweight]
  exact FiniteFreeEnergy.freeEnergy_of_bounded_rows_mem_unit_interval D.beta n hβ hn _
    (fun i a => hloss (y i a))

/-- One input-row replacement changes the exact normalized free energy by
at most 1/n, regardless of the quadratic measurement or deterministic shift. -/
theorem freeEnergy_row_difference {X : Type*} (D : Data κ)
    (hweight : ∀ a, D.weight a = (Fintype.card κ : ℝ)⁻¹)
    (hβ : 0 < D.beta) {n : ℕ} (hn : 0 < n)
    (hloss : ∀ t, 0 ≤ D.potential t ∧ D.potential t ≤ 1)
    (q : X → κ → ℝ) (c : Fin n → κ → ℝ)
    (x : Fin n → X) (i : Fin n) (z : X) :
    |UCActualFreeEnergy.freeEnergy D (fun j => q ((Function.update x i z) j)+c j) -
      UCActualFreeEnergy.freeEnergy D (fun j => q (x j)+c j)| ≤ 1/(n:ℝ) := by
  simp_rw [freeEnergy_eq_project D hweight]
  apply FiniteFreeEnergy.freeEnergy_row_replacement D.beta n hβ hn _ _ i
  · intro j hji a
    simp [Function.update_of_ne hji]
  · intro a
    exact hloss _
  · intro a
    exact hloss _

#print axioms freeEnergy_eq_project
#print axioms freeEnergy_row_difference
end GaussianEllipsoid.UCFreeEnergyBridge
