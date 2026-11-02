import BMWidthExpectation

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid GaussianTensorMoments MeasureTheory
namespace BMGeometry

theorem transposeFrob_pairing {d : ℕ} (A B : HMat d) :
    ⟪transposeFrob A,B⟫_ℝ = ⟪A,transposeFrob B⟫_ℝ := by
  change (∑ j, ∑ i, B j i * A i j) = ∑ j, ∑ i, B i j * A j i
  rw [Finset.sum_comm]

theorem symmetric_transposeFrob {d : ℕ} (S : Op d) (hS : S.toLinearMap.IsSymmetric) :
    transposeFrob (operatorFrobenius S) = operatorFrobenius S := by
  rw [← operatorFrobenius_adjoint,
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hS).adjoint_eq]

/-- Orthogonal symmetrization leaves every symmetric test pairing unchanged. -/
theorem symmetrization_pairing {d : ℕ} (A : HMat d) (S : Op d)
    (hS : S.toLinearMap.IsSymmetric) :
    ⟪symmetricFrobLM d A,operatorFrobenius S⟫_ℝ = ⟪A,operatorFrobenius S⟫_ℝ := by
  change ⟪(1/2:ℝ) • (A+transposeFrob A),operatorFrobenius S⟫_ℝ = _
  rw [real_inner_smul_left, inner_add_left, transposeFrob_pairing, symmetric_transposeFrob S hS]
  ring

/-- The cone width can be computed in the full d²-coordinate Euclidean ambient space. -/
theorem conditionedSupport_symmetrization {d : ℕ} (κ : ℝ) (A : HMat d) :
    conditionedSupport d κ (symmetricFrobLM d A) = conditionedSupport d κ A := by
  unfold conditionedSupport
  congr 1
  ext z
  constructor
  · rintro ⟨S,hS,hz⟩
    exact ⟨S,hS,hz.trans (symmetrization_pairing A S hS.1.1.1)⟩
  · rintro ⟨S,hS,hz⟩
    exact ⟨S,hS,hz.trans (symmetrization_pairing A S hS.1.1.1).symm⟩

theorem gaussianConditionedSupportRaw_eq_fullEntry (d : ℕ) (κ : ℝ) (x : (Fin d × Fin d) → ℝ) :
    gaussianConditionedSupportRaw d κ x =
      conditionedSupport d κ ((frobeniusEquivEuclidean d d).symm ((WithLp.equiv 2 _).symm x)) := by
  rw [gaussianConditionedSupportRaw, isotropicSymmetricOp_frobenius, conditionedSupport_symmetrization]

theorem conditionedWidth_eq_fullEntry (d : ℕ) (κ : ℝ) :
    conditionedWidth d κ =
      ∫ x, conditionedSupport d κ ((frobeniusEquivEuclidean d d).symm ((WithLp.equiv 2 _).symm x))
        ∂gaussianProductLaw (Fin d × Fin d) := by
  unfold conditionedWidth
  apply integral_congr_ae
  exact ae_of_all _ (gaussianConditionedSupportRaw_eq_fullEntry d κ)

end BMGeometry
