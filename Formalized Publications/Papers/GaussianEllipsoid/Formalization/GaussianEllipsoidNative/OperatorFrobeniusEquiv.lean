import PolarDuality

noncomputable section
namespace GaussianEllipsoid

/-- The algebraic coordinate equivalence, retaining operator and Frobenius norms
on their respective spaces. -/
def operatorFrobeniusLinearEquiv (r q : ℕ) :
    (Euclid q →L[ℝ] Euclid r) ≃ₗ[ℝ] FrobeniusMatrix r q where
  toFun := operatorFrobenius
  invFun := frobeniusOperator
  left_inv := frobeniusOperator_operatorFrobenius
  right_inv := operatorFrobenius_frobeniusOperator
  map_add' := operatorFrobenius_add
  map_smul' c T := by ext j i; rfl

/-- The representation bridge is continuous in both directions. It is not
claimed to preserve the operator norm and Frobenius norm. -/
def operatorFrobeniusContinuousLinearEquiv (r q : ℕ) :
    (Euclid q →L[ℝ] Euclid r) ≃L[ℝ] FrobeniusMatrix r q :=
  (operatorFrobeniusLinearEquiv r q).toContinuousLinearEquiv

theorem continuous_operatorFrobenius (r q : ℕ) :
    Continuous (operatorFrobenius : (Euclid q →L[ℝ] Euclid r) → FrobeniusMatrix r q) :=
  (operatorFrobeniusContinuousLinearEquiv r q).continuous

theorem continuous_frobeniusOperator (r q : ℕ) :
    Continuous (frobeniusOperator : FrobeniusMatrix r q → (Euclid q →L[ℝ] Euclid r)) :=
  (operatorFrobeniusContinuousLinearEquiv r q).symm.continuous

end GaussianEllipsoid
#print axioms GaussianEllipsoid.continuous_operatorFrobenius
#print axioms GaussianEllipsoid.continuous_frobeniusOperator
