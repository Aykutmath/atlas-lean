/- Newly reconstructed source, 2026-10-03. Not recovered original bytes.
   Native verification pending; literal full-half singular constants retained. -/
import PaperSparseSingular
import ActualSparseBlock

noncomputable section
open Finset MeasureTheory GaussianEllipsoid GaussianEllipsoid.SparseSupport
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoidCandidate

theorem norm_lower_of_unit_lower {s h : ℕ} (A : Euclid s →L[ℝ] Euclid h)
    (c : ℝ) (hA : ∀ v, ‖v‖ = 1 → c ≤ ‖A v‖) (v : Euclid s) :
    c * ‖v‖ ≤ ‖A v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hunit : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvp), inv_mul_cancel₀ hvp.ne']
  have hh := hA (‖v‖⁻¹ • v) hunit
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvp)] at hh
  apply (le_div_iff₀ hvp).mp
  simpa only [div_eq_mul_inv, mul_comm] using hh

theorem paperSparseSingularGood_supported_nuclear_lower {d n h : ℕ}
    {X : Fin n → Euclid h × Euclid h} (hX : X ∈ paperSparseSingularGood d n h)
    (I : Finset (Fin n)) (hI : I.card ≤ sparseSupportSize d)
    (u : Fin n → ℝ) (hu : ∀ i, i ∉ I → u i = 0) :
    (1/4194304:ℝ) * Real.sqrt d * coefficientMass u ≤
      spectralNuclearNorm (operatorFrobenius
        ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u X)) := by
  by_cases hd : d = 0
  · subst d
    simp [Real.sqrt_zero]
  by_cases hIe : I = ∅
  · have huz : u = 0 := by ext i; exact hu i (by simp [hIe])
    subst u
    simp [coefficientMass, bilinearSynthesis]
  have hIp : 1 ≤ I.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hIe)
  have hsp := hX I hIp hI
  have hspos : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd))
  let c : ℝ := ((1/2048:ℝ)*Real.sqrt d)^2
  have hc : 0 < c := sq_pos_of_pos (mul_pos (by norm_num) hspos)
  have hA := (paperLeastSingularValue_ge_iff _ _).mp hsp.1
  have hB := (paperLeastSingularValue_ge_iff _ _).mp hsp.2
  have hquad (A : Euclid I.card →L[ℝ] Euclid h)
      (hA : ∀ v, ‖v‖ = 1 → (1/2048:ℝ)*Real.sqrt d ≤ ‖A v‖) :
      ∀ v, c * ‖v‖^2 ≤ ‖A v‖^2 := by
    intro v
    have hv := norm_lower_of_unit_lower A _ hA v
    have hz : 0 ≤ ((1/2048:ℝ)*Real.sqrt d)*‖v‖ := by positivity
    have hh := (sq_le_sq₀ hz (norm_nonneg _)).mpr hv
    simpa only [c, mul_pow] using hh
  let a : Fin I.card → ℝ := fun j => u (I.equivFin.symm j).val
  have hn := spectralNuclear_multiplication_lower
    (supportOperator h n I (rowsToMatrixPair h n X).1)
    (supportOperator h n I (rowsToMatrixPair h n X).2)
    (coefficientDiagonal a) hc (hquad _ hA) (hquad _ hB)
  have hl := (mul_le_mul_of_nonneg_left (l1_le_coefficientDiagonal_nuclear a) hc.le).trans hn
  have he : supportOperator h n I (rowsToMatrixPair h n X).1 ∘L coefficientDiagonal a ∘L
      (supportOperator h n I (rowsToMatrixPair h n X).2).adjoint = bilinearSynthesis u X := by
    apply_fun operatorFrobenius using fun S T hh => by
      have hh' := congrArg frobeniusOperator hh
      simpa only [frobeniusOperator_operatorFrobenius] using hh'
    ext j i
    change (supportOperator h n I (rowsToMatrixPair h n X).1
      (coefficientDiagonal a ((supportOperator h n I (rowsToMatrixPair h n X).2).adjoint
        (EuclideanSpace.basisFun (Fin h) ℝ j)))) i = _
    rw [supportOperator_apply, bilinearSynthesis_entry]
    simp only [coefficientDiagonal_apply, supportOperator_adjoint_basis_entry]
    change (∑ b : Fin I.card, (X (I.equivFin.symm b).val).2 i *
      (u (I.equivFin.symm b).val * (X (I.equivFin.symm b).val).1 j)) = _
    rw [sum_support_enumeration I (fun k => (X k).2 i * (u k * (X k).1 j))]
    calc
      _ = ∑ k, (X k).2 i * (u k * (X k).1 j) := by
        apply Finset.sum_subset (Finset.subset_univ I)
        intro k _ hk
        simp [hu k hk]
      _ = _ := Finset.sum_congr rfl (fun k _ => by ring)
  rw [he, l1_support_enumeration I u hu] at hl
  have hscaled := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hspos.le)
  rw [operatorFrobenius_smul_eq, spectralNuclear_smul,
    abs_of_nonneg (inv_nonneg.mpr hspos.le)]
  have hcscale : (Real.sqrt (d:ℝ))⁻¹ * c = (1/4194304:ℝ)*Real.sqrt d := by
    dsimp [c]
    field_simp [hspos.ne']
    <;> ring
  simpa only [← mul_assoc, hcscale, coefficientMass] using hscaled

theorem paper_actual_sparse_first_block_lower {n d h : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (hp : p ≤ groups.length)
    (hbudget : supportCut (dyadicGroupSupport u amp groups T) p ≤ sparseSupportSize d)
    (X : Fin n → Euclid h × Euclid h) (hX : X ∈ paperSparseSingularGood d n h) :
    (1/4194304:ℝ)*Real.sqrt d*(∑ r ∈ range p, dyadicGroupMass u amp groups T r) ≤
      spectralNuclearNorm (operatorFrobenius
        (projectedPrefixBlock (orderedRetainedCoefficients u amp ha groups T d hreg hflat)
          (permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat) X)
          0 (supportCut (dyadicGroupSupport u amp groups T) p))) := by
  classical
  rw [projectedPrefixBlock_zero_left, ordered_sparse_prefix_synthesis u amp ha groups T d p hreg hflat hp]
  have hcard : (indexedGroupUnion u amp groups T p).card ≤ sparseSupportSize d := by
    rw [indexedGroupUnion_eq_biUnion, support_prefix_card _
      (actual_group_supports_pairwise u amp ha groups T hreg hflat groups.length le_rfl) p hp]
    exact hbudget
  have hl := paperSparseSingularGood_supported_nuclear_lower hX
    (indexedGroupUnion u amp groups T p) hcard (retainedPrefixVector u amp groups T p)
    (fun i hi => by simp [retainedPrefixVector, hi])
  rw [actual_prefix_mass_sum u amp ha groups T p hreg hflat hp] at hl
  exact hl

end GaussianEllipsoidCandidate
