import GaussianQuadraticFractional
import VolumetricNets
import Mathlib.Analysis.Normed.Lp.PiLp

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Real GaussianTensorMoments GaussianMixedNormHelpers BMQuadraticSpectral Module
open scoped BigOperators ENNReal InnerProductSpace
namespace BMUniformMoment

/-- Symmetric operators with their genuine operator norm. -/
def symmetricOperators (d : ℕ) : Submodule ℝ
    (BMQuadraticSpectral.Euclid d →L[ℝ] BMQuadraticSpectral.Euclid d) where
  carrier := {T | T.toLinearMap.IsSymmetric}
  zero_mem' := LinearMap.IsSymmetric.zero
  add_mem' := fun hT hU => hT.add hU
  smul_mem' := fun c T hT => hT.smul (by simp)

abbrev SymOp (d : ℕ) : Type := ↥(symmetricOperators d)

theorem symmetricOperators_finrank_le (d : ℕ) : finrank ℝ (SymOp d) ≤ d*d := by
  exact (symmetricOperators d).finrank_le.trans_eq (GaussianEllipsoid.finrank_euclidean_operator d d)

/-- A genuine operator-norm half-net with at most 5^(d²) centers. -/
theorem exists_symmetric_operator_half_net (d : ℕ) :
    ∃ s : Finset (SymOp d), (∀ T ∈ s, ‖T‖ = 1) ∧
      (s.card:ℝ) ≤ (5:ℝ)^(d*d) ∧
      ∀ T : SymOp d, ‖T‖ = 1 → ∃ U ∈ s, ‖T-U‖ < (1:ℝ)/2 := by
  obtain ⟨s, hs, hc, hn, _⟩ := GaussianEllipsoid.exists_internal_net
    {T : SymOp d | ‖T‖ = 1} (R := 1) (ε := 1/2) (by norm_num) (by norm_num)
    (fun T hT => hT.le)
  refine ⟨s, hs, ?_, ?_⟩
  · norm_num at hc
    exact hc.trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤5) (symmetricOperators_finrank_le d))
  · intro T hT
    simpa only [dist_eq_norm] using hn T hT

lemma operator_norm_le_twice_half_net {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (s : Finset E)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x-y‖ < (1:ℝ)/2)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y ∈ s, ‖L y‖ ≤ B) : ‖L‖ ≤ 2*B := by
  have h : ‖L‖ ≤ B+‖L‖/2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    calc
      ‖L x‖ ≤ ‖L y‖ + ‖L (x-y)‖ := by
        rw [map_sub]
        exact norm_le_insert' (L x) (L y)
      _ ≤ B+‖L‖*‖x-y‖ := add_le_add (hb y hy) (L.le_opNorm _)
      _ ≤ B+‖L‖/2 := by nlinarith [norm_nonneg L]
  linarith

lemma image_norm_le_twice_half_net {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (s : Finset E)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x-y‖ < (1:ℝ)/2)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y ∈ s, ‖L y‖ ≤ B)
    (x : E) (hx : ‖x‖ ≤ 1) : ‖L x‖ ≤ 2*B := by
  have hL := operator_norm_le_twice_half_net L s hnet B hB hb
  simpa only [mul_one] using L.le_of_opNorm_le_of_le hL hx

instance q_ge_one : Fact (1 ≤ (6:ℝ≥0∞)/5) := ⟨by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  norm_num⟩
abbrev FractionalSamples (n : ℕ) := PiLp ((6:ℝ≥0∞)/5) (fun _ : Fin n => ℝ)

/-- For fixed actual samples, their centered quadratic measurements form a
linear operator into the finite-dimensional l^(6/5) space. -/
def empiricalQuadraticLinear {d n : ℕ} (x : Fin n → BMQuadraticSpectral.Euclid d) :
    SymOp d →ₗ[ℝ] FractionalSamples n where
  toFun T := (WithLp.linearEquiv ((6:ℝ≥0∞)/5) ℝ (Fin n → ℝ)).symm
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
      (∑ i, |normalizedQuadratic T.val (x i)|^((6:ℝ)/5))^((5:ℝ)/6) := by
  rw [PiLp.norm_eq_sum (by norm_num : 0 < ((6:ℝ≥0∞)/5).toReal)]
  norm_num [empiricalQuadraticOperator, empiricalQuadraticLinear, Real.norm_eq_abs]

/-- Minkowski's half-net transfer with the exact fractional power handled
through the genuine l^(6/5) norm. -/
theorem empirical_quadratic_sum_le_of_half_net {d n : ℕ}
    (x : Fin n → BMQuadraticSpectral.Euclid d) (s : Finset (SymOp d))
    (hnet : ∀ T : SymOp d, ‖T‖ = 1 → ∃ U ∈ s, ‖T-U‖ < (1:ℝ)/2)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ U ∈ s, (∑ i, |normalizedQuadratic U.val (x i)|^((6:ℝ)/5)) ≤ B)
    (T : SymOp d) (hT : ‖T‖ ≤ 1) :
    (∑ i, |normalizedQuadratic T.val (x i)|^((6:ℝ)/5)) ≤ 4*B := by
  have hval : ‖empiricalQuadraticOperator x T‖ ≤ 2*B^((5:ℝ)/6) :=
    image_norm_le_twice_half_net (empiricalQuadraticOperator x) s hnet
      (B^((5:ℝ)/6)) (Real.rpow_nonneg hB _) (by
        intro U hU
        rw [empiricalQuadraticOperator_norm]
        exact Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _))
          (hb U hU) (by norm_num)) T hT
  have hp := Real.rpow_le_rpow (norm_nonneg _) hval (by norm_num : 0 ≤ (6:ℝ)/5)
  rw [empiricalQuadraticOperator_norm, ← Real.rpow_mul (Finset.sum_nonneg
    (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _))] at hp
  norm_num at hp
  have hr : (2*B^((5:ℝ)/6))^((6:ℝ)/5) ≤ 4*B := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hB _), ← Real.rpow_mul hB]
    norm_num
    have hh : (2:ℝ)^((6:ℝ)/5) ≤ 4 := by
      calc
        _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 4 := by norm_num
    exact mul_le_mul_of_nonneg_right hh hB
  exact hp.trans hr

#print axioms exists_symmetric_operator_half_net
#print axioms operator_norm_le_twice_half_net
#print axioms empiricalQuadraticOperator_norm
#print axioms empirical_quadratic_sum_le_of_half_net
end BMUniformMoment
