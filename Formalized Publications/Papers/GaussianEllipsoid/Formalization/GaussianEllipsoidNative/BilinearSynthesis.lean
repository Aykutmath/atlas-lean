import MeasurableHalfPolar
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

open MeasureTheory
open scoped InnerProductSpace

namespace GaussianEllipsoid

/-- One bilinear rank-one row, ordered (b,a) to match the Gaussian MGF law. -/
noncomputable def bilinearRowOperator {r q : ℕ} (p : Euclid q × Euclid r) :
    Euclid q →L[ℝ] Euclid r := (innerSL ℝ p.1).smulRight p.2

@[simp] theorem bilinearRowOperator_apply {r q : ℕ} (p : Euclid q × Euclid r) (x : Euclid q) :
    bilinearRowOperator p x = ⟪p.1,x⟫_ℝ • p.2 := rfl

/-- Canonical unscaled coefficient synthesis. The paper's factor d^(-1/2)
can be put in the coefficients, or applied as an outer scalar. -/
noncomputable def bilinearSynthesis {ι : Type*} [Fintype ι] {r q : ℕ}
    (u : ι → ℝ) (X : ι → Euclid q × Euclid r) : Euclid q →L[ℝ] Euclid r :=
  ∑ i, u i • bilinearRowOperator (X i)

/-- Exact coordinate form of the canonical rank-one row. -/
theorem bilinearRowOperator_entry {r q : ℕ} (p : Euclid q × Euclid r)
    (i : Fin r) (j : Fin q) :
    operatorFrobenius (bilinearRowOperator p) j i = p.2 i * p.1 j := by
  change (⟪p.1,EuclideanSpace.basisFun (Fin q) ℝ j⟫_ℝ • p.2) i = _
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right, mul_comm]

/-- Coordinates of the canonical finite bilinear synthesis. -/
theorem bilinearSynthesis_entry {ι : Type*} [Fintype ι] {r q : ℕ}
    (u : ι → ℝ) (X : ι → Euclid q × Euclid r) (i : Fin r) (j : Fin q) :
    operatorFrobenius (bilinearSynthesis u X) j i =
      ∑ k, u k * ((X k).2 i * (X k).1 j) := by
  change ((∑ k, u k • bilinearRowOperator (X k)) (EuclideanSpace.basisFun (Fin q) ℝ j)) i = _
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  change ((WithLp.linearEquiv 2 ℝ (Fin r → ℝ))
    (∑ k, u k • bilinearRowOperator (X k) (EuclideanSpace.basisFun (Fin q) ℝ j))) i = _
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  change u k * (operatorFrobenius (bilinearRowOperator (X k)) j i) = _
  rw [bilinearRowOperator_entry]

/-- Joint continuity of the rank-one row as an actual Euclidean operator. -/
theorem continuous_bilinearRowOperator (r q : ℕ) :
    Continuous (bilinearRowOperator : Euclid q × Euclid r → (Euclid q →L[ℝ] Euclid r)) :=
  (ContinuousLinearMap.smulRightL ℝ (Euclid q) (Euclid r)).continuous₂.comp₂
    ((innerSL ℝ).continuous.comp continuous_fst) continuous_snd

/-- Measurability of synthesis for every fixed coefficient vector. -/
theorem measurable_bilinearSynthesis {ι : Type*} [Fintype ι] {r q : ℕ} (u : ι → ℝ) :
    Measurable (bilinearSynthesis u : (ι → Euclid q × Euclid r) → (Euclid q →L[ℝ] Euclid r)) := by
  unfold bilinearSynthesis
  apply Finset.measurable_sum
  intro i _
  exact ((continuous_bilinearRowOperator r q).measurable.comp (measurable_pi_apply i)).const_smul (u i)

#print axioms bilinearRowOperator_apply
#print axioms bilinearRowOperator_entry
#print axioms bilinearSynthesis_entry
#print axioms continuous_bilinearRowOperator
#print axioms measurable_bilinearSynthesis

end GaussianEllipsoid
