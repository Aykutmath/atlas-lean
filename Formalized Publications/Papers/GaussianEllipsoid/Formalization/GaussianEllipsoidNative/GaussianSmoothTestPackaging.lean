/- Newly reconstructed analytic support, 2026-10-03. Not recovered original bytes.
   Convert genuine Euclidean Lipschitz smooth functions to coordinate tests,
   preserving the squared Euclidean gradient bound exactly. -/
import GaussianCovarianceRotation

noncomputable section
open BMSmoothQuadraticComposition GaussianCovarianceRotation
open scoped BigOperators BoundedContinuousFunction ContDiff

namespace GaussianSmoothTestPackaging
variable {d : ℕ}
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

def toEuclid : Raw d ≃L[ℝ] E d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm

theorem toEuclid_eq_sum (z : Raw d) :
    toEuclid z = ∑ i, z i • (PiLp.single 2 i (1 : ℝ) : E d) := by
  ext j
  simp [toEuclid, PiLp.single_apply, Pi.single_apply, mul_ite]

def coord (L : E d →L[ℝ] ℝ) (i : Fin d) : ℝ := L (PiLp.single 2 i 1)

theorem apply_eq_sum (L : E d →L[ℝ] ℝ) (z : Raw d) :
    L (toEuclid z) = ∑ i, coord L i * z i := by
  rw [toEuclid_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [coord, mul_comm]

theorem sum_coord_sq_le_one (L : E d →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    ∑ i, (coord L i)^2 ≤ 1 := by
  let v : E d := toEuclid (coord L)
  have hv : ‖v‖^2 = ∑ i, (coord L i)^2 := by
    simp [v, toEuclid, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  have he : L v = ‖v‖^2 := by
    rw [hv]
    simpa only [v, apply_eq_sum, pow_two]
  have hb : ‖L v‖ ≤ ‖v‖ := by
    exact (L.le_opNorm v).trans (by nlinarith [norm_nonneg v])
  rw [he, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hb
  have hn := norm_nonneg v
  nlinarith

theorem coord_fderiv_bound (f : E d → ℝ) (hf : LipschitzWith 1 f) (x : E d) (i : Fin d) :
    ‖coord (fderiv ℝ f x) i‖ ≤ 1 := by
  have hh := norm_fderiv_le_of_lipschitz ℝ hf (x₀ := x)
  have h := (fderiv ℝ f x).le_opNorm (PiLp.single 2 i (1 : ℝ))
  simpa only [coord, PiLp.norm_single, norm_one, mul_one, NNReal.coe_one] using h.trans
    (mul_le_mul_of_nonneg_right hh (norm_nonneg (PiLp.single 2 i (1 : ℝ) : E d)))

def ofSmooth (f : E d → ℝ) (hc : ContDiff ℝ ∞ f) (hf : LipschitzWith 1 f)
    (B : ℝ) (hb : ∀ x, ‖f x‖ ≤ B) : SmoothTest (Fin d) where
  value := BoundedContinuousFunction.ofNormedAddCommGroup (fun x => f (toEuclid x))
    (hc.continuous.comp toEuclid.continuous) B (fun x => hb _)
  gradient i := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => coord (fderiv ℝ f (toEuclid x)) i)
    (((hc.continuous_fderiv (by simp)).comp toEuclid.continuous).clm_apply continuous_const)
    1 (fun x => coord_fderiv_bound f hf _ i)
  hasFDeriv x := by
    have hh := ((hc.differentiable (by simp)) (toEuclid x)).hasFDerivAt.comp x
      toEuclid.hasFDerivAt
    convert! hh using 1
    ext z
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.comp_apply,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup, smul_eq_mul]
    exact (apply_eq_sum _ z).symm

@[simp] theorem ofSmooth_value (f : E d → ℝ) (hc : ContDiff ℝ ∞ f) (hf : LipschitzWith 1 f)
    (B : ℝ) (hb : ∀ x, ‖f x‖ ≤ B) (x : Raw d) :
    (ofSmooth f hc hf B hb).value x = f (toEuclid x) := rfl

theorem ofSmooth_gradient_bound (f : E d → ℝ) (hc : ContDiff ℝ ∞ f) (hf : LipschitzWith 1 f)
    (B : ℝ) (hb : ∀ x, ‖f x‖ ≤ B) (x : Raw d) :
    ∑ i, ((ofSmooth f hc hf B hb).gradient i x)^2 ≤ 1 := by
  apply sum_coord_sq_le_one
  exact norm_fderiv_le_of_lipschitz ℝ hf

#print axioms ofSmooth
#print axioms ofSmooth_gradient_bound
end GaussianSmoothTestPackaging
