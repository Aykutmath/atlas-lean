import BMGordonFiniteCoordinates
import BMGordonFiniteAffine
import BMGordonExpectationBridge
import BMSaddleFeasibilityAssembly

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory GaussianEllipsoid BMGeometry BMSaddle
namespace BMGordon

/-- Actual finite affine comparison for every pair of finite restrictions of the concrete BM processes. -/
theorem finite_affine_comparison {n d : ℕ} {κ : ℝ} (R : ℝ)
    (I J : Type) [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (u : I → UnitSample n) (S : J → UnitCone d κ) :
    (∫ ω, finiteValue (fun i j => affineAuxiliary R (u i,S j)) ω ∂law n d) ≤
      ∫ ω, finiteValue (fun i j => affinePrimary R (u i,S j)) ω ∂law n d := by
  classical
  let A : I × J → Space n d := fun a => auxiliaryCoefficient (u a.1 : Euclid n) (S a.2 : HMat d)
  let B : I × J → Space n d := fun a => primaryCoefficient (u a.1 : Euclid n) (S a.2 : HMat d)
  let v : I × J → ℝ := fun a => rowDrift R (u a.1)
  change (∫ ω, finiteValue (fun i j ω => ⟪A (i,j),ω⟫_ℝ+v (i,j)) ω ∂law n d) ≤
    ∫ ω, finiteValue (fun i j ω => ⟪B (i,j),ω⟫_ℝ+v (i,j)) ω ∂law n d
  rw [finite_integral_eq_flat,finite_integral_eq_flat]
  apply BMGordonFiniteAffine.minMax_expectation_le_linear
    (fun a => flatCoefficient (A a)) (fun a => flatCoefficient (B a)) v
  · intro a b hab
    rw [flatCoefficient_inner,flatCoefficient_inner]
    rcases a with ⟨i,j⟩
    rcases b with ⟨k,l⟩
    change i=k at hab
    subst k
    exact (coefficient_covariance_same_row (u i) (S j) (S l)).symm
  · intro a b
    rw [flatCoefficient_inner,flatCoefficient_inner]
    exact coefficient_covariance_comparison (u a.1) (u b.1) (S a.2) (S b.2)

/-- The genuine Gaussian expected comparison, including its deterministic row drift. -/
theorem expectedGordonComparison {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {κ : ℝ} (hκ : 1 ≤ κ) (R : ℝ) : BMSaddle.ExpectedGordonComparison n d κ R := by
  apply expectedGordonComparison_of_compact hn hd hκ
  exact compact_affine_comparison_of_finite hn hd hκ R (finite_affine_comparison R)

/-- Discharges the last comparison premise of the frozen BM feasibility/risk chain. -/
theorem expectedGordonPrinciple : BMSaddle.ExpectedGordonPrinciple := by
  intro n d hn hd κ R hκ _hR
  exact expectedGordonComparison hn hd hκ R

#print axioms finite_affine_comparison
#print axioms expectedGordonComparison
#print axioms expectedGordonPrinciple
end BMGordon
