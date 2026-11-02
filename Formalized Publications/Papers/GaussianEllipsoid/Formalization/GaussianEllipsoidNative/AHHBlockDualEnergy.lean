import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Exact dual-energy decomposition for finite Euclidean products of real Hilbert spaces. -/
noncomputable section
open scoped BigOperators
namespace AHHRadial

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The continuous linear inclusion of one block into its Euclidean product. -/
def blockInclude (j : ι) : E →L[ℝ] PiLp 2 (fun _ : ι => E) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : ι => E) j)

@[simp] theorem blockInclude_apply (j : ι) (x : E) :
    blockInclude j x = PiLp.single 2 j x := rfl

/-- The restriction of a real functional to a single block. -/
def blockPartial (L : PiLp 2 (fun _ : ι => E) →L[ℝ] ℝ) (j : ι) : E →L[ℝ] ℝ :=
  L.comp (blockInclude j)

@[simp] theorem blockPartial_apply (L : PiLp 2 (fun _ : ι => E) →L[ℝ] ℝ)
    (j : ι) (x : E) : blockPartial L j x = L (PiLp.single 2 j x) := rfl

@[simp] theorem inner_blockInclude (g : PiLp 2 (fun _ : ι => E)) (j : ι) (x : E) :
    inner ℝ g (blockInclude j x) = inner ℝ (g j) x := by
  simp [PiLp.inner_apply, PiLp.single_apply, apply_ite]

variable [CompleteSpace E]

theorem blockPartial_eq_toDual (L : PiLp 2 (fun _ : ι => E) →L[ℝ] ℝ) (j : ι) :
    blockPartial L j = InnerProductSpace.toDual ℝ E
      (((InnerProductSpace.toDual ℝ (PiLp 2 (fun _ : ι => E))).symm L) j) := by
  ext x
  change L (blockInclude j x) = inner ℝ
    (((InnerProductSpace.toDual ℝ (PiLp 2 (fun _ : ι => E))).symm L) j) x
  rw [← inner_blockInclude]
  exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
    (E := PiLp 2 (fun _ : ι => E)) (y := L) (x := blockInclude j x)).symm

/-- A functional's squared dual norm is the sum of its squared block dual norms. -/
theorem norm_sq_eq_sum_blockPartial (L : PiLp 2 (fun _ : ι => E) →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = ∑ j, ‖blockPartial L j‖ ^ 2 := by
  simp_rw [blockPartial_eq_toDual, LinearIsometryEquiv.norm_map]
  rw [← PiLp.norm_sq_eq_of_L2]
  rw [LinearIsometryEquiv.norm_map]

/-- Apply a separate continuous real linear map in each Euclidean block. -/
def blockMap (A : ι → E →L[ℝ] E) : PiLp 2 (fun _ : ι => E) →L[ℝ] PiLp 2 (fun _ : ι => E) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.piMap A).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).toContinuousLinearMap)

@[simp] theorem blockMap_apply (A : ι → E →L[ℝ] E)
    (x : PiLp 2 (fun _ : ι => E)) (j : ι) :
    blockMap A x j = A j (x j) := rfl

@[simp] theorem blockMap_single (A : ι → E →L[ℝ] E) (j : ι) (x : E) :
    blockMap A (PiLp.single 2 j x) = PiLp.single 2 j (A j x) := by
  ext k
  by_cases h : k = j
  · subst k
    simp
  · simp [h]

@[simp] theorem blockPartial_comp_blockMap
    (L : PiLp 2 (fun _ : ι => E) →L[ℝ] ℝ) (A : ι → E →L[ℝ] E) (j : ι) :
    blockPartial (L.comp (blockMap A)) j = (blockPartial L j).comp (A j) := by
  ext x
  simp

/-- Blockwise operator-norm bounds preserve the sum of individual dual energies. -/
theorem norm_sq_comp_blockMap_le
    (L : PiLp 2 (fun _ : ι => E) →L[ℝ] ℝ) (A : ι → E →L[ℝ] E) :
    ‖L.comp (blockMap A)‖ ^ 2 ≤ ∑ j, ‖blockPartial L j‖ ^ 2 * ‖A j‖ ^ 2 := by
  rw [norm_sq_eq_sum_blockPartial]
  apply Finset.sum_le_sum
  intro j _
  rw [blockPartial_comp_blockMap, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((blockPartial L j).opNorm_comp_le (A j)) 2

/-- Use separate nonnegative bounds for the block maps, without taking their maximum. -/
theorem norm_sq_comp_blockMap_le_of_norm_le
    (L : PiLp 2 (fun _ : ι => E) →L[ℝ] ℝ) (A : ι → E →L[ℝ] E)
    (a : ι → ℝ) (ha : ∀ j, ‖A j‖ ≤ a j) :
    ‖L.comp (blockMap A)‖ ^ 2 ≤ ∑ j, ‖blockPartial L j‖ ^ 2 * (a j) ^ 2 := by
  apply (norm_sq_comp_blockMap_le L A).trans
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (ha j) 2) (sq_nonneg _)

/-- Diagonal scalar multiplication of the blocks, as a continuous linear map. -/
def blockScale (r : ι → ℝ) : PiLp 2 (fun _ : ι => E) →L[ℝ] PiLp 2 (fun _ : ι => E) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.piMap (fun j => r j • ContinuousLinearMap.id ℝ E)).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).toContinuousLinearMap)

@[simp] theorem blockScale_apply (r : ι → ℝ) (x : PiLp 2 (fun _ : ι => E)) (j : ι) :
    blockScale r x j = r j • x j := rfl

@[simp] theorem blockScale_single (r : ι → ℝ) (j : ι) (x : E) :
    blockScale r (PiLp.single 2 j x) = PiLp.single 2 j (r j • x) := by
  ext k
  by_cases h : k = j
  · subst k
    simp
  · simp [h]

@[simp] theorem blockPartial_comp_blockScale
    (L : PiLp 2 (fun _ : ι => E) →L[ℝ] ℝ) (r : ι → ℝ) (j : ι) :
    blockPartial (L.comp (blockScale r)) j = r j • blockPartial L j := by
  ext x
  simp only [blockPartial_apply, ContinuousLinearMap.comp_apply, blockScale_single,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  change (blockPartial L j) (r j • x) = r j • (blockPartial L j) x
  exact (blockPartial L j).map_smul (r j) x

/-- The exact dual energy after a diagonal scaling of the input blocks. -/
theorem norm_sq_comp_blockScale
    (L : PiLp 2 (fun _ : ι => E) →L[ℝ] ℝ) (r : ι → ℝ) :
    ‖L.comp (blockScale r)‖ ^ 2 = ∑ j, (r j) ^ 2 * ‖blockPartial L j‖ ^ 2 := by
  rw [norm_sq_eq_sum_blockPartial]
  simp_rw [blockPartial_comp_blockScale, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Inverse-radius weights retain one reciprocal square for each individual block. -/
theorem norm_sq_comp_blockScale_inv
    (L : PiLp 2 (fun _ : ι => E) →L[ℝ] ℝ) (r : ι → ℝ) :
    ‖L.comp (blockScale (fun j => (r j)⁻¹))‖ ^ 2 =
      ∑ j, ‖blockPartial L j‖ ^ 2 / (r j) ^ 2 := by
  rw [norm_sq_comp_blockScale]
  simp_rw [inv_pow, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

#print axioms norm_sq_eq_sum_blockPartial
#print axioms norm_sq_comp_blockScale_inv
#print axioms norm_sq_comp_blockMap_le_of_norm_le
end AHHRadial
