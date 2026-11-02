import AdaptedPrefixWitness

open MeasureTheory
open scoped InnerProductSpace

namespace GaussianEllipsoid

/-- Exact rank-one pairing, in the same row order used by the Gaussian law. -/
theorem inner_bilinearRowOperator {r q : ℕ} (p : Euclid q × Euclid r)
    (W : Euclid q →L[ℝ] Euclid r) :
    ⟪operatorFrobenius (bilinearRowOperator p), operatorFrobenius W⟫_ℝ = ⟪W p.1,p.2⟫_ℝ := by
  let e := EuclideanSpace.basisFun (Fin q) ℝ
  rw [← sum_inner_operator_basis _ _ e]
  simp only [bilinearRowOperator_apply, real_inner_smul_left]
  calc
    ∑ i, ⟪p.1,e i⟫_ℝ * ⟪p.2,W (e i)⟫_ℝ =
        ∑ i, ⟪p.1,e i⟫_ℝ * ⟪e i,ContinuousLinearMap.adjoint W p.2⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← ContinuousLinearMap.adjoint_inner_left, real_inner_comm (ContinuousLinearMap.adjoint W p.2)]
    _ = ⟪p.1,ContinuousLinearMap.adjoint W p.2⟫_ℝ := e.sum_inner_mul_inner _ _
    _ = ⟪W p.1,p.2⟫_ℝ := ContinuousLinearMap.adjoint_inner_right W _ _

@[simp] theorem operatorFrobenius_real_smul {r q : ℕ} (c : ℝ)
    (T : Euclid q →L[ℝ] Euclid r) : operatorFrobenius (c • T) = c • operatorFrobenius T := by
  ext j i
  rfl

theorem inner_bilinearSynthesis {ι : Type*} [Fintype ι] {r q : ℕ}
    (u : ι → ℝ) (X : ι → Euclid q × Euclid r) (W : Euclid q →L[ℝ] Euclid r) :
    ⟪operatorFrobenius (bilinearSynthesis u X),operatorFrobenius W⟫_ℝ =
      ∑ i, u i * ⟪W (X i).1,(X i).2⟫_ℝ := by
  simp only [bilinearSynthesis, operatorFrobenius_sum, sum_inner,
    operatorFrobenius_real_smul, real_inner_smul_left, inner_bilinearRowOperator]

noncomputable def prefixFuturePairing {N r q : ℕ} (u : Fin N → ℝ)
    (X : Fin N → Euclid q × Euclid r) (K : ℕ) (W : Euclid q →L[ℝ] Euclid r) : ℝ :=
  ∑ i, if K ≤ i.val then u i * ⟪W (X i).1,(X i).2⟫_ℝ else 0

theorem synthesis_pairing_prefix_future {N r q : ℕ} (u : Fin N → ℝ)
    (X : Fin N → Euclid q × Euclid r) (K : ℕ) (W : Euclid q →L[ℝ] Euclid r) :
    ⟪operatorFrobenius (bilinearSynthesis u X),operatorFrobenius W⟫_ℝ =
      ⟪operatorFrobenius (prefixBilinearSynthesis u X K),operatorFrobenius W⟫_ℝ +
        prefixFuturePairing u X K W := by
  simp only [prefixBilinearSynthesis, inner_bilinearSynthesis, prefixFuturePairing,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < K
  · simp [hi, Nat.not_le.mpr hi]
  · simp [hi, Nat.le_of_not_gt hi]

theorem prefixWitnessCross_eq_future_sum {ι : Type*} [Fintype ι]
    {N r q : ℕ} (u : Fin N → ℝ) (lo hi : ι → ℕ)
    (X : Fin N → Euclid q × Euclid r) :
    prefixWitnessCross u u lo hi X =
      ∑ j, prefixFuturePairing u X (hi j) (prefixBlockWitness u X (lo j) (hi j)) := by
  unfold prefixWitnessCross completedPrefixWitness prefixFuturePairing
  simp only [ContinuousLinearMap.sum_apply, sum_inner, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- Pointwise diagonal-plus-adapted-cross lower bound from the actual constructed
witnesses. No good-event hypotheses, witness choices, or stochastic assumptions
are hidden in this algebraic identity. -/
theorem nuclear_lower_from_prefix_blocks {ι : Type*} [Fintype ι]
    {N r q : ℕ} (u : Fin N → ℝ) (lo hi : ι → ℕ)
    (hlo : ∀ j, lo j ≤ hi j) (hhi : ∀ j, hi j ≤ N)
    (hsep : ∀ i j, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (X : Fin N → Euclid q × Euclid r) :
    (∑ j, spectralNuclearNorm (operatorFrobenius (projectedPrefixBlock u X (lo j) (hi j)))) / 2 +
        prefixWitnessCross u u lo hi X ≤ spectralNuclearNorm (operatorFrobenius (bilinearSynthesis u X)) := by
  let Z := fun j => prefixBlockWitness u X (lo j) (hi j)
  have hnorm : ‖∑ j, Z j‖ ≤ 1 := by
    have h := norm_completedPrefixWitness_le_one u lo hi hlo hsep X N
    simpa only [completedPrefixWitness, hhi, if_true] using h
  have hdiag (j : ι) :
      spectralNuclearNorm (operatorFrobenius (projectedPrefixBlock u X (lo j) (hi j))) / 2 ≤
        ⟪operatorFrobenius (prefixBilinearSynthesis u X (hi j)),operatorFrobenius (Z j)⟫_ℝ := by
    have hp := prefixBlockWitness_properties u X (hlo j)
    rw [inner_supported_eq_compressed (leftIncrement X (lo j) (hi j))
      (rightIncrement X (lo j) (hi j)) _ (Z j)
      (prefixSpanProjector_increment_selfAdjoint _ _ _)
      (prefixSpanProjector_increment_selfAdjoint _ _ _) hp.2.1]
    exact hp.2.2
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hdiag j)
  have heq : (∑ j, ⟪operatorFrobenius (prefixBilinearSynthesis u X (hi j)),operatorFrobenius (Z j)⟫_ℝ) +
      prefixWitnessCross u u lo hi X =
      ⟪operatorFrobenius (bilinearSynthesis u X),operatorFrobenius (∑ j, Z j)⟫_ℝ := by
    rw [prefixWitnessCross_eq_future_sum, operatorFrobenius_sum, inner_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact (synthesis_pairing_prefix_future u X (hi j) (Z j)).symm
  have hdual := inner_operator_le_nuclear (operatorFrobenius (bilinearSynthesis u X)) (∑ j, Z j) hnorm
  rw [Finset.sum_div] 
  linarith

/-- Before the first completed block, the constructed predictable witness is zero. -/
theorem completedPrefixWitness_eq_zero_before {ι : Type*} [Fintype ι]
    {N r q : ℕ} (u : Fin N → ℝ) (lo hi : ι → ℕ)
    (X : Fin N → Euclid q × Euclid r) {p t : ℕ}
    (hfirst : ∀ j, p ≤ hi j) (ht : t < p) : completedPrefixWitness u lo hi X t = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have h : ¬ hi j ≤ t := by have := hfirst j; omega
  simp only [h, if_false]

/-- Prefix coefficients can be set to zero in the cross sum; their witnesses
vanish identically. This removes the possibly large sparse-prefix coefficients
from the MGF radius and variance budget. -/
theorem prefixWitnessCross_mask_prefix {ι : Type*} [Fintype ι]
    {N r q : ℕ} (u : Fin N → ℝ) (lo hi : ι → ℕ) (p : ℕ)
    (hfirst : ∀ j, p ≤ hi j) (X : Fin N → Euclid q × Euclid r) :
    prefixWitnessCross u (fun i => if i.val < p then 0 else u i) lo hi X =
      prefixWitnessCross u u lo hi X := by
  unfold prefixWitnessCross
  apply Finset.sum_congr rfl
  intro i _
  by_cases hip : i.val < p
  · rw [completedPrefixWitness_eq_zero_before u lo hi X hfirst hip]
    simp
  · simp only [hip, if_false]

#print axioms inner_bilinearRowOperator
#print axioms operatorFrobenius_real_smul
#print axioms inner_bilinearSynthesis
#print axioms synthesis_pairing_prefix_future
#print axioms prefixWitnessCross_eq_future_sum
#print axioms nuclear_lower_from_prefix_blocks
#print axioms completedPrefixWitness_eq_zero_before
#print axioms prefixWitnessCross_mask_prefix
end GaussianEllipsoid
