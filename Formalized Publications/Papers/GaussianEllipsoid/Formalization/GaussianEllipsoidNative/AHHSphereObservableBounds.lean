import AHHCovarianceJensen
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Unconditional pointwise bounds for the actual product-sphere observable. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers AHHAlgebraBridges
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace AHHRadial

def productVector (h : ℕ) (x y : CE h) : ProductSpace h :=
  WithLp.toLp 2 (fun p : Fin h × Fin h => x p.1 * y p.2)

theorem productVector_norm (h : ℕ) (x y : CE h) :
    ‖productVector h x y‖ = ‖x‖ * ‖y‖ := by
  have hs : ‖productVector h x y‖^2 = (‖x‖ * ‖y‖)^2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow,
      PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [productVector, norm_mul, mul_pow,
      Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  nlinarith [norm_nonneg (productVector h x y), norm_nonneg x, norm_nonneg y,
    mul_nonneg (norm_nonneg x) (norm_nonneg y)]

theorem cMatrixCLM_projector_eq_rankOne {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) :
    cMatrixCLM (projector (fun i => v i)) = InnerProductSpace.rankOne ℂ v v := by
  ext z i
  change (Matrix.mulVec (projector (fun i => v i)) z.ofLp) i =
    (inner ℂ v z • v) i
  simp only [Matrix.mulVec, dotProduct, projector, PiLp.smul_apply,
    PiLp.inner_apply, RCLike.inner_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [starRingEnd_apply]
  ring

theorem productProjector_eq_rankOne (h : ℕ) (x y : CE h) :
    productProjector h x y = InnerProductSpace.rankOne ℂ
      (productVector h x y) (productVector h x y) :=
  cMatrixCLM_projector_eq_rankOne (productVector h x y)

theorem unit_productVector_norm (h : ℕ) (x y : UnitDirection h) :
    ‖productVector h x y‖ = 1 := by
  rw [productVector_norm]
  have hx : ‖(x : CE h)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hy : ‖(y : CE h)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using y.property
  rw [hx, hy, one_mul]

theorem unit_productProjector_norm (h : ℕ) (x y : UnitDirection h) :
    ‖productProjector h x y‖ = 1 := by
  rw [productProjector_eq_rankOne, InnerProductSpace.norm_rankOne,
    unit_productVector_norm, one_mul]

theorem unitCovarianceNorm_le (n h : ℕ) (d : Directions n h) :
    unitCovarianceNorm n h d ≤ n := by
  unfold unitCovarianceNorm unitCovariance
  calc
    ‖∑ i, productProjector h (d i).1 (d i).2‖ ≤
        ∑ i, ‖productProjector h (d i).1 (d i).2‖ := norm_sum_le _ _
    _ = n := by simp only [unit_productProjector_norm, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem one_le_unitCovarianceNorm (n h : ℕ) (hn : 0 < n) (d : Directions n h) :
    1 ≤ unitCovarianceNorm n h d := by
  let A := fun i : Fin n => projector (fun p : Fin h × Fin h =>
    ((d i).1 : CE h) p.1 * ((d i).2 : CE h) p.2)
  let i : Fin n := ⟨0, hn⟩
  have hA : ∀ j, 0 ≤ A j := fun j => (projector_posSemidef _).nonneg
  have hm : ‖A i‖ ≤ ‖∑ j, A j‖ :=
    CStarAlgebra.norm_le_norm_of_le_of_nonneg
      (Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)) (hA i)
  have hi : ‖A i‖ = 1 := by
    rw [← cMatrixCLM_norm]
    exact unit_productProjector_norm h (d i).1 (d i).2
  have he : cMatrixCLM (∑ j, A j) = unitCovariance n h d := by
    unfold cMatrixCLM unitCovariance
    rw [map_sum]
    rfl
  rw [hi, ← cMatrixCLM_norm, he] at hm
  exact hm

#print axioms productVector_norm
#print axioms unitCovarianceNorm_le
#print axioms one_le_unitCovarianceNorm
end AHHRadial
