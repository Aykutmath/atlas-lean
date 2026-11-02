import PolarDuality

noncomputable section
open Set Module
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid

theorem operatorFrobenius_adjoint_entry {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (i : Fin r) (j : Fin q) :
    operatorFrobenius (ContinuousLinearMap.adjoint T) i j = operatorFrobenius T j i := by
  change (ContinuousLinearMap.adjoint T (EuclideanSpace.basisFun (Fin r) ℝ i)) j =
    (T (EuclideanSpace.basisFun (Fin q) ℝ j)) i
  simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, map_one, one_mul, conj_trivial] using
      ContinuousLinearMap.adjoint_inner_right T (EuclideanSpace.basisFun (Fin q) ℝ j)
        (EuclideanSpace.basisFun (Fin r) ℝ i)

theorem inner_operatorFrobenius_adjoint {r q : ℕ}
    (S T : Euclid q →L[ℝ] Euclid r) :
    ⟪operatorFrobenius (ContinuousLinearMap.adjoint S),
      operatorFrobenius (ContinuousLinearMap.adjoint T)⟫_ℝ =
      ⟪operatorFrobenius S, operatorFrobenius T⟫_ℝ := by
  simp only [PiLp.inner_apply, operatorFrobenius_adjoint_entry]
  rw [Finset.sum_comm]

theorem inner_operator_comp_left {r q h : ℕ} (P : Euclid r →L[ℝ] Euclid h)
    (T : Euclid q →L[ℝ] Euclid r) (W : Euclid q →L[ℝ] Euclid h) :
    ⟪operatorFrobenius (P ∘L T), operatorFrobenius W⟫_ℝ =
      ⟪operatorFrobenius T, operatorFrobenius (ContinuousLinearMap.adjoint P ∘L W)⟫_ℝ := by
  change (∑ j, ⟪P (T (EuclideanSpace.basisFun (Fin q) ℝ j)),
      W (EuclideanSpace.basisFun (Fin q) ℝ j)⟫_ℝ) =
    ∑ j, ⟪T (EuclideanSpace.basisFun (Fin q) ℝ j),
      ContinuousLinearMap.adjoint P (W (EuclideanSpace.basisFun (Fin q) ℝ j))⟫_ℝ
  exact Finset.sum_congr rfl (fun j _ => (ContinuousLinearMap.adjoint_inner_right P _ _).symm)

theorem inner_operator_comp_right {r q k : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (Q : Euclid k →L[ℝ] Euclid q) (W : Euclid k →L[ℝ] Euclid r) :
    ⟪operatorFrobenius (T ∘L Q), operatorFrobenius W⟫_ℝ =
      ⟪operatorFrobenius T, operatorFrobenius (W ∘L ContinuousLinearMap.adjoint Q)⟫_ℝ := by
  rw [← inner_operatorFrobenius_adjoint (T ∘L Q) W, ContinuousLinearMap.adjoint_comp,
    inner_operator_comp_left, ContinuousLinearMap.adjoint_adjoint]
  have h := inner_operatorFrobenius_adjoint T (W ∘L ContinuousLinearMap.adjoint Q)
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] using h

theorem norm_comp_le_one {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (S : F →L[ℝ] G) (T : E →L[ℝ] F) (hS : ‖S‖ ≤ 1) (hT : ‖T‖ ≤ 1) :
    ‖S ∘L T‖ ≤ 1 := by
  exact (ContinuousLinearMap.opNorm_comp_le S T).trans
    (by simpa using mul_le_mul hS hT (norm_nonneg T) zero_le_one)

/-- Nuclear norm is contractive under arbitrary Euclidean operator contractions
on both sides. In particular, orthogonal compression cannot increase it. -/
theorem spectralNuclear_compression_le {r q h k : ℕ}
    (P : Euclid r →L[ℝ] Euclid h) (T : Euclid q →L[ℝ] Euclid r)
    (Q : Euclid k →L[ℝ] Euclid q) (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    spectralNuclearNorm (operatorFrobenius (P ∘L T ∘L Q)) ≤
      spectralNuclearNorm (operatorFrobenius T) := by
  apply (spectralNuclear_le_iff _ _).mpr
  intro W hW
  rw [inner_operator_comp_left, inner_operator_comp_right]
  apply inner_operator_le_nuclear
  apply norm_comp_le_one _ _
  · apply norm_comp_le_one _ _ _ hW
    simpa using hP
  · simpa using hQ

/-- Nuclear norm is invariant under transpose/adjoint. -/
theorem spectralNuclear_adjoint {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) :
    spectralNuclearNorm (operatorFrobenius (ContinuousLinearMap.adjoint T)) =
      spectralNuclearNorm (operatorFrobenius T) := by
  have hbound {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) :
      spectralNuclearNorm (operatorFrobenius (ContinuousLinearMap.adjoint T)) ≤
        spectralNuclearNorm (operatorFrobenius T) := by
    apply (spectralNuclear_le_iff _ _).mpr
    intro W hW
    have hi := inner_operatorFrobenius_adjoint T (ContinuousLinearMap.adjoint W)
    rw [ContinuousLinearMap.adjoint_adjoint] at hi
    rw [hi]
    exact inner_operator_le_nuclear _ _ (by simpa using hW)
  exact le_antisymm (hbound T)
    (by simpa only [ContinuousLinearMap.adjoint_adjoint] using hbound (ContinuousLinearMap.adjoint T))

end GaussianEllipsoid
#print axioms GaussianEllipsoid.spectralNuclear_compression_le
#print axioms GaussianEllipsoid.spectralNuclear_adjoint
