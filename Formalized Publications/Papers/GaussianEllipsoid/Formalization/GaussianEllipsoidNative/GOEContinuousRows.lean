import GaussianLinearAbsMoment
import BMSymmetricFiniteUniversality

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000
noncomputable section
open MeasureTheory Real BMUniformMoment BMSymmetricFiniteUniversality BMGaussianEquivalent
open GaussianTensorMoments
open scoped BigOperators ENNReal
namespace BMGOEUniform

local instance {d : ℕ} : NormedAddCommGroup (SymOp d) :=
  Submodule.normedAddCommGroup (symmetricOperators d)
local instance {d : ℕ} : NormedSpace ℝ (SymOp d) :=
  Submodule.normedSpace (symmetricOperators d)

/-- Literal GOE trace measurement as a continuous linear form on genuine
symmetric operators. Its Gaussian source has d² independent scalar entries. -/
def goeRow {d : ℕ} (z : Fin (d*d) → ℝ) : SymOp d →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := SymOp d) (F' := ℝ)
    { toFun := fun T => Matrix.trace (symmetrizedGaussianMatrix d z * matrixOf T)
      map_add' := by
        intro T U
        simp [matrixOf, Matrix.mul_add, Matrix.trace_add]
      map_smul' := by
        intro c T
        simp [matrixOf, Matrix.mul_smul, Matrix.trace_smul] }

@[simp] theorem goeRow_apply {d : ℕ} (z : Fin (d*d) → ℝ) (T : SymOp d) :
    goeRow z T = Matrix.trace (symmetrizedGaussianMatrix d z*matrixOf T) := rfl

/-- The actual source dependence is continuous; ground-state integrability and
measurability can therefore use this row with no continuity premise. -/
theorem continuous_goeRow {d : ℕ} (T : SymOp d) :
    Continuous (fun z : Fin (d*d) → ℝ => goeRow z T) := by
  simp only [goeRow_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    symmetrizedGaussianMatrix]
  fun_prop

/-- Actual GOE row absolute moments under its correct full-entry Gaussian law. -/
theorem goeRow_factorial_moment {d : ℕ} (hd : 0 < d) (T : SymOp d)
    (hT : ‖T‖ ≤ 1) (k : ℕ) :
    Integrable (fun z => |goeRow z T|^k) (gaussianProductLaw (Fin (d*d))) ∧
    (∫ z, |goeRow z T|^k ∂gaussianProductLaw (Fin (d*d))) ≤
      (k.factorial:ℝ)*(2*exp 1)^k := by
  exact goe_trace_factorial_moment hd (matrixOf T) (matrixOf_transpose T)
    (by simpa only [spectralNorm_matrixOf] using hT) k

/-- Actual independent full-entry GOE sample law. -/
abbrev goeSampleLaw (d n : ℕ) : Measure (Fin n → (Fin (d*d) → ℝ)) :=
  Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))

/-- Fixed-state empirical L1 tail under the actual independent GOE source. -/
theorem goeRow_empirical_tail {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (T : SymOp d) (hT : ‖T‖ ≤ 1) (t : ℝ) (ht : 0 < t) :
    (goeSampleLaw d n).real {z | t*n < ∑ i, |goeRow (z i) T|} ≤ (8*exp 1/t)^n := by
  have hI (i : Fin n) (k : ℕ) (_hk : k ≤ n) := (goeRow_factorial_moment hd T hT k).1
  have hM (i : Fin n) (k : ℕ) (_hk : k ≤ n) := (goeRow_factorial_moment hd T hT k).2
  convert independent_sum_tail_le (gaussianProductLaw (Fin (d*d))) n hn
    (fun _ z => |goeRow z T|) (2*exp 1) t (fun _ _ => abs_nonneg _)
    (by positivity) ht hI hM using 1 <;> congr 1 <;> ring

abbrev L1Samples (n : ℕ) := PiLp 1 (fun _ : Fin n => ℝ)

/-- The actual GOE sample map into finite l1. -/
def goeEmpiricalLinear {d n : ℕ} (z : Fin n → (Fin (d*d) → ℝ)) :
    SymOp d →ₗ[ℝ] L1Samples n :=
  (WithLp.linearEquiv 1 ℝ (Fin n → ℝ)).symm.toLinearMap.comp
    (LinearMap.pi (fun i => (goeRow (z i)).toLinearMap))

def goeEmpiricalOperator {d n : ℕ} (z : Fin n → (Fin (d*d) → ℝ)) :
    SymOp d →L[ℝ] L1Samples n :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := SymOp d) (F' := L1Samples n))
    (goeEmpiricalLinear z)

theorem goeEmpiricalOperator_norm {d n : ℕ} (z : Fin n → (Fin (d*d) → ℝ)) (T : SymOp d) :
    ‖goeEmpiricalOperator z T‖ = ∑ i, |goeRow (z i) T| := by
  rw [PiLp.norm_eq_sum (by norm_num : (0:ℝ) < (1:ℝ≥0∞).toReal)]
  simp [goeEmpiricalOperator, goeEmpiricalLinear, Real.norm_eq_abs]

/-- General homogeneous form of half-net transfer. -/
lemma image_norm_le_half_net_mul_norm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (s : Finset E)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x-y‖ < (1:ℝ)/2)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y ∈ s, ‖L y‖ ≤ B)
    (x : E) : ‖L x‖ ≤ 2*B*‖x‖ :=
  L.le_of_opNorm_le (operator_norm_le_twice_half_net L s hnet B hB hb) x

/-- Actual GOE l1 half-net transfer, already in the homogeneous form used by
continuum ground-state net extension. -/
theorem goe_empirical_sum_le_of_half_net {d n : ℕ}
    (z : Fin n → (Fin (d*d) → ℝ)) (s : Finset (SymOp d))
    (hnet : ∀ T : SymOp d, ‖T‖ = 1 → ∃ U ∈ s, ‖T-U‖ < (1:ℝ)/2)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ U ∈ s, (∑ i, |goeRow (z i) U|) ≤ B)
    (T : SymOp d) : (∑ i, |goeRow (z i) T|) ≤ 2*B*‖T‖ := by
  have h := image_norm_le_half_net_mul_norm (E := SymOp d) (goeEmpiricalOperator z) s hnet B hB
    (by intro U hU; rw [goeEmpiricalOperator_norm]; exact hb U hU) T
  simpa only [goeEmpiricalOperator_norm] using h

#print axioms goeRow
#print axioms continuous_goeRow
#print axioms goeRow_factorial_moment
#print axioms goeRow_empirical_tail
#print axioms goeEmpiricalOperator_norm
#print axioms goe_empirical_sum_le_of_half_net
end BMGOEUniform
