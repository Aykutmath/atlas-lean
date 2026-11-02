import AHHSphereEuclideanGeometry
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Sharp normalization derivatives in real Hilbert geometry. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace AHHRadial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Radial normalization, with the canonical zero value at the origin. -/
def radialNormalize (x : E) : E := ‖x‖⁻¹ • x

/-- Differential of radial normalization away from the origin. -/
def normalizationDerivative (x : E) : E →L[ℝ] E :=
  ‖x‖⁻¹ • (ContinuousLinearMap.id ℝ E -
    InnerProductSpace.rankOne ℝ (radialNormalize x) (radialNormalize x))

theorem norm_radialNormalize {x : E} (hx : x ≠ 0) : ‖radialNormalize x‖ = 1 := by
  rw [radialNormalize, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem norm_id_sub_rankOne_le {u : E} (hu : ‖u‖ = 1) :
    ‖ContinuousLinearMap.id ℝ E - InnerProductSpace.rankOne ℝ u u‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    InnerProductSpace.rankOne_apply, one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hu,
    inner_smul_right, real_inner_comm]
  nlinarith [sq_nonneg (inner ℝ u v)]

theorem norm_normalizationDerivative_le {x : E} (hx : x ≠ 0) :
    ‖normalizationDerivative x‖ ≤ ‖x‖⁻¹ := by
  rw [normalizationDerivative, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (norm_id_sub_rankOne_le (norm_radialNormalize hx)) (inv_nonneg.mpr (norm_nonneg x))

theorem hasFDerivAt_radialNormalize {x : E} (hx : x ≠ 0) :
    HasFDerivAt radialNormalize (normalizationDerivative x) x := by
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hn : HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
    have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hxnorm)
    simp only [Real.sqrt_sq (norm_nonneg _)] at hn
    convert hn using 1
    ext v
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply]
    field_simp
    simp [two_smul, mul_two]
  have hi := (hasDerivAt_inv hxnorm).comp_hasFDerivAt x hn
  have hm := hi.smul (hasFDerivAt_id x)
  change HasFDerivAt (fun y : E => ‖y‖⁻¹ • y) (normalizationDerivative x) x
  convert hm using 1
  · rfl
  · ext v
    simp only [normalizationDerivative, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      InnerProductSpace.rankOne_apply, radialNormalize,
      inner_smul_left, inner_smul_right, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
      RCLike.conj_to_real, smul_eq_mul, Function.comp_def, id_eq]
    module

#print axioms norm_normalizationDerivative_le
#print axioms hasFDerivAt_radialNormalize
end AHHRadial
