import FourThirdQuadraticMoment
import OperatorFractionalNet

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Real GaussianTensorMoments GaussianMixedNormHelpers BMQuadraticSpectral Module BMUniformMoment
open scoped BigOperators ENNReal InnerProductSpace
namespace BMFourThirdMoment

local instance {d : ℕ} : NormedAddCommGroup (SymOp d) := Submodule.normedAddCommGroup (symmetricOperators d)
local instance {d : ℕ} : NormedSpace ℝ (SymOp d) := Submodule.normedSpace (symmetricOperators d)

instance q_ge_one : Fact (1 ≤ (4:ℝ≥0∞)/3) := ⟨by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  norm_num⟩
abbrev FractionalSamples (n : ℕ) := PiLp ((4:ℝ≥0∞)/3) (fun _ : Fin n => ℝ)

/-- For fixed actual samples, their centered quadratic measurements form a
linear operator into the finite-dimensional l^(4/3) space. -/
def empiricalQuadraticLinear {d n : ℕ} (x : Fin n → BMQuadraticSpectral.Euclid d) :
    SymOp d →ₗ[ℝ] FractionalSamples n where
  toFun T := (WithLp.linearEquiv ((4:ℝ≥0∞)/3) ℝ (Fin n → ℝ)).symm
    (fun i => normalizedQuadratic T.val (x i))
  map_add' T U := by
    ext i
    simp [normalizedQuadratic, inner_add_right, add_div, add_sub_add_comm]
  map_smul' c T := by
    ext i
    simp [normalizedQuadratic, inner_smul_right, mul_sub, mul_div_assoc]
    ring

def empiricalQuadraticOperator {d n : ℕ} (x : Fin n → BMQuadraticSpectral.Euclid d) :
    SymOp d →L[ℝ] FractionalSamples n :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := SymOp d) (F' := FractionalSamples n))
    (empiricalQuadraticLinear x)

theorem empiricalQuadraticOperator_norm {d n : ℕ} (x : Fin n → BMQuadraticSpectral.Euclid d)
    (T : SymOp d) :
    ‖empiricalQuadraticOperator x T‖ =
      (∑ i, |normalizedQuadratic T.val (x i)|^((4:ℝ)/3))^((3:ℝ)/4) := by
  rw [PiLp.norm_eq_sum (by norm_num : 0 < ((4:ℝ≥0∞)/3).toReal)]
  norm_num [empiricalQuadraticOperator, empiricalQuadraticLinear, Real.norm_eq_abs]

/-- Minkowski's half-net transfer with the exact fractional power handled
through the genuine l^(4/3) norm. -/
theorem empirical_quadratic_sum_le_of_half_net {d n : ℕ}
    (x : Fin n → BMQuadraticSpectral.Euclid d) (s : Finset (SymOp d))
    (hnet : ∀ T : SymOp d, ‖T‖ = 1 → ∃ U ∈ s, ‖T-U‖ < (1:ℝ)/2)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ U ∈ s, (∑ i, |normalizedQuadratic U.val (x i)|^((4:ℝ)/3)) ≤ B)
    (T : SymOp d) (hT : ‖T‖ ≤ 1) :
    (∑ i, |normalizedQuadratic T.val (x i)|^((4:ℝ)/3)) ≤ 4*B := by
  have hval : ‖empiricalQuadraticOperator x T‖ ≤ 2*B^((3:ℝ)/4) :=
    image_norm_le_twice_half_net (empiricalQuadraticOperator x) s hnet
      (B^((3:ℝ)/4)) (Real.rpow_nonneg hB _) (by
        intro U hU
        rw [empiricalQuadraticOperator_norm]
        exact Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _))
          (hb U hU) (by norm_num)) T hT
  have hp := Real.rpow_le_rpow (norm_nonneg _) hval (by norm_num : 0 ≤ (4:ℝ)/3)
  rw [empiricalQuadraticOperator_norm, ← Real.rpow_mul (Finset.sum_nonneg
    (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _))] at hp
  norm_num at hp
  have hr : (2*B^((3:ℝ)/4))^((4:ℝ)/3) ≤ 4*B := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hB _), ← Real.rpow_mul hB]
    norm_num
    have hh : (2:ℝ)^((4:ℝ)/3) ≤ 4 := by
      calc
        _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 4 := by norm_num
    exact mul_le_mul_of_nonneg_right hh hB
  exact hp.trans hr

#print axioms empiricalQuadraticOperator_norm
#print axioms empirical_quadratic_sum_le_of_half_net
end BMFourThirdMoment
