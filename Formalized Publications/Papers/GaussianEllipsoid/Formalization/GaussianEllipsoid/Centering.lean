/-
Kernel-checked finite-coordinate centering, its matrix bridge, orthogonality, and norm bounds.
Source: paper.tex, Sections 2 and 4, especially lines 318-322 and 677-688.
-/
import GaussianEllipsoid.Coordinates
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace GaussianEllipsoid

/-- The coordinate definition of `center` is exactly multiplication by Pi_n.
This identity also holds for the empty coordinate space. -/
theorem centeringMatrix_mulVec {n : Nat} (v : Vector n) :
    Matrix.mulVec (centeringMatrix n) v = center v := by
  rw [centeringMatrix, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  funext i
  simp [center, mean, Matrix.mulVec, dotProduct, div_eq_mul_inv, mul_comm]

/-- The arithmetic mean is additive. -/
theorem mean_add {n : Nat} (u v : Vector n) :
    mean (u + v) = mean u + mean v := by
  simp [mean, Finset.sum_add_distrib, add_div]

/-- The arithmetic mean is homogeneous over the real numbers. -/
theorem mean_smul {n : Nat} (c : Real) (v : Vector n) :
    mean (c • v) = c * mean v := by
  simp only [mean, Pi.smul_apply, smul_eq_mul]
  rw [<- Finset.mul_sum]
  ring

/-- Centering is a linear operation: additivity. -/
theorem center_add {n : Nat} (u v : Vector n) :
    center (u + v) = center u + center v := by
  funext i
  simp only [center, mean_add, Pi.add_apply]
  ring

/-- Centering is a linear operation: homogeneity. -/
theorem center_smul {n : Nat} (c : Real) (v : Vector n) :
    center (c • v) = c • center v := by
  funext i
  simp only [center, mean_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- The sum of the coordinates is the sample size times their mean. -/
theorem card_mul_mean {n : Nat} (hn : 0 < n) (v : Vector n) :
    (n : Real) * mean v = Finset.univ.sum (fun i => v i) := by
  have hnR : Not ((n : Real) = 0) := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold mean
  field_simp [hnR]

/-- Every centered vector has zero coordinate sum. -/
theorem sum_center {n : Nat} (hn : 0 < n) (v : Vector n) :
    Finset.univ.sum (fun i => center v i) = 0 := by
  simp only [center, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [card_mul_mean hn]
  exact sub_self _

/-- Every centered vector has zero mean. -/
theorem mean_center {n : Nat} (hn : 0 < n) (v : Vector n) :
    mean (center v) = 0 := by
  simp only [mean, sum_center hn, zero_div]

/-- Centering is the identity on vectors of zero mean. -/
theorem center_eq_self_of_mean_zero {n : Nat} (v : Vector n)
    (hv : mean v = 0) : center v = v := by
  funext i
  simp only [center, hv, sub_zero]

/-- A second application of centering changes nothing. -/
theorem center_idempotent {n : Nat} (hn : 0 < n) (v : Vector n) :
    center (center v) = center v :=
  center_eq_self_of_mean_zero (center v) (mean_center hn v)

/-- The centering matrix is idempotent. -/
theorem centeringMatrix_idempotent {n : Nat} (hn : 0 < n) :
    centeringMatrix n * centeringMatrix n = centeringMatrix n := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  calc
    Matrix.mulVec (centeringMatrix n * centeringMatrix n) v =
        Matrix.mulVec (centeringMatrix n) (Matrix.mulVec (centeringMatrix n) v) :=
      (Matrix.mulVec_mulVec v (centeringMatrix n) (centeringMatrix n)).symm
    _ = center (center v) := by rw [centeringMatrix_mulVec, centeringMatrix_mulVec]
    _ = center v := center_idempotent hn v
    _ = Matrix.mulVec (centeringMatrix n) v := (centeringMatrix_mulVec v).symm

/-- The centering matrix is symmetric, so the idempotent is orthogonal. -/
theorem centeringMatrix_isSymm (n : Nat) : (centeringMatrix n).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp [centeringMatrix, Matrix.one_apply, eq_comm]

/-- A constant vector is killed by centering. -/
theorem center_const {n : Nat} (hn : 0 < n) (c : Real) :
    center (fun _ : Fin n => c) = 0 := by
  funext i
  simp only [center, mean_const hn, sub_self, Pi.zero_apply]

/-- The kernel of centering is exactly the space of constant vectors. -/
theorem center_eq_zero_iff_constant {n : Nat} (hn : 0 < n) (v : Vector n) :
    center v = 0 <-> exists c : Real, forall i : Fin n, v i = c := by
  constructor
  case mp =>
    intro h
    exact Exists.intro (mean v) ((center_eq_zero_iff_mean v).mp h)
  case mpr =>
    intro h
    apply Exists.elim h
    intro c hc
    have he : v = fun _ : Fin n => c := funext hc
    rw [he]
    exact center_const hn c

/-- Centering is the identity on the hyperplane whose coordinates sum to zero. -/
theorem center_eq_self_of_sum_zero {n : Nat} (v : Vector n)
    (hv : Finset.univ.sum (fun i => v i) = 0) : center v = v := by
  apply center_eq_self_of_mean_zero
  simp only [mean, hv, zero_div]

/-- Expanding the left centered factor in the coordinate inner product. -/
theorem dotProduct_center_left {n : Nat} (u v : Vector n) :
    dotProduct (center u) v = dotProduct u v -
      mean u * Finset.univ.sum (fun i => v i) := by
  simp only [dotProduct, center, sub_mul, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]

/-- Expanding the right centered factor in the coordinate inner product. -/
theorem dotProduct_center_right {n : Nat} (u v : Vector n) :
    dotProduct u (center v) = dotProduct u v -
      mean v * Finset.univ.sum (fun i => u i) := by
  rw [dotProduct_comm u (center v), dotProduct_center_left, dotProduct_comm v u]

/-- The centering operator is self-adjoint for the Euclidean coordinate inner product. -/
theorem center_selfAdjoint {n : Nat} (u v : Vector n) :
    dotProduct (center u) v = dotProduct u (center v) := by
  rw [dotProduct_center_left, dotProduct_center_right]
  unfold mean
  ring

/-- A centered vector is perpendicular to every constant vector. -/
theorem dotProduct_center_const {n : Nat} (hn : 0 < n) (v : Vector n) (c : Real) :
    dotProduct (center v) (fun _ : Fin n => c) = 0 := by
  unfold dotProduct
  rw [<- Finset.sum_mul, sum_center hn, zero_mul]

/-- The mean absolute value controls the absolute value of the mean. -/
theorem abs_mean_le_mean_abs {n : Nat} (hn : 0 < n) (v : Vector n) :
    abs (mean v) <= mean (fun i => abs (v i)) := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  unfold mean
  rw [abs_div, abs_of_pos hnR]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs v Finset.univ) hnR.le

/-- A uniform coordinate bound also bounds the absolute value of the mean. -/
theorem abs_mean_le_of_bound {n : Nat} (hn : 0 < n) (v : Vector n) (M : Real)
    (hv : forall i : Fin n, abs (v i) <= M) : abs (mean v) <= M := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hs : Finset.univ.sum (fun i => abs (v i)) <= (n : Real) * M := by
    calc
      Finset.univ.sum (fun i => abs (v i)) <=
          Finset.univ.sum (fun _ : Fin n => M) :=
        Finset.sum_le_sum (fun i _ => hv i)
      _ = (n : Real) * M := by simp
  calc
    abs (mean v) <= mean (fun i => abs (v i)) := abs_mean_le_mean_abs hn v
    _ = (Finset.univ.sum (fun i => abs (v i))) / (n : Real) := rfl
    _ <= ((n : Real) * M) / (n : Real) := div_le_div_of_nonneg_right hs hnR.le
    _ = M := by field_simp [ne_of_gt hnR]

/-- A centered coordinate is at most the original coordinate plus the mean in absolute value. -/
theorem abs_center_le {n : Nat} (v : Vector n) (i : Fin n) :
    abs (center v i) <= abs (v i) + abs (mean v) := by
  simpa only [center, sub_eq_add_neg, abs_neg] using abs_add_le (v i) (-mean v)

/-- Pointwise form of the manuscript's factor-two infinity-norm bound. -/
theorem abs_center_le_two_mul {n : Nat} (hn : 0 < n) (v : Vector n) (M : Real)
    (hv : forall i : Fin n, abs (v i) <= M) (i : Fin n) :
    abs (center v i) <= 2 * M := by
  have hm := abs_mean_le_of_bound hn v M hv
  have hi := abs_center_le v i
  linarith [hv i]

/-- The standard function-space norm on `Vector n` is the infinity norm.
This is not the Euclidean norm; the latter is modeled separately below. -/
theorem center_infinityNorm_le {n : Nat} (hn : 0 < n) (v : Vector n) :
    Norm.norm (center v) <= 2 * Norm.norm v := by
  apply (pi_norm_le_iff_of_nonneg (show (0 : Real) <= 2 * Norm.norm v by positivity)).mpr
  intro i
  have hv : forall j : Fin n, abs (v j) <= Norm.norm v := by
    intro j
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j
  simpa only [Real.norm_eq_abs] using abs_center_le_two_mul hn v (Norm.norm v) hv i

/-- The coordinate l1 norm, kept separate from the function-space infinity norm. -/
def l1Size {n : Nat} (v : Vector n) : Real :=
  Finset.univ.sum (fun i => abs (v i))

/-- The l1 norm of a centered vector is at most twice the original l1 norm. -/
theorem center_l1Size_le {n : Nat} (hn : 0 < n) (v : Vector n) :
    l1Size (center v) <= 2 * l1Size v := by
  have hnR : (0 : Real) <= (n : Real) := by positivity
  have hm := mul_le_mul_of_nonneg_left (abs_mean_le_mean_abs hn v) hnR
  rw [card_mul_mean hn] at hm
  calc
    l1Size (center v) <= Finset.univ.sum (fun i => abs (v i) + abs (mean v)) :=
      Finset.sum_le_sum (fun i _ => abs_center_le v i)
    _ = l1Size v + (n : Real) * abs (mean v) := by
      simp [l1Size, Finset.sum_add_distrib]
    _ <= 2 * l1Size v := by unfold l1Size; linarith

/-- The exact squared Euclidean norm in coordinates. -/
def squaredL2 {n : Nat} (v : Vector n) : Real :=
  Finset.univ.sum (fun i => (v i) ^ 2)

/-- The squared Euclidean norm is the coordinate self-inner-product. -/
theorem squaredL2_eq_dotProduct {n : Nat} (v : Vector n) :
    squaredL2 v = dotProduct v v := by
  simp only [squaredL2, dotProduct, pow_two]

/-- Pythagoras for decomposition into centered and constant components. -/
theorem squaredL2_center_identity {n : Nat} (hn : 0 < n) (v : Vector n) :
    squaredL2 (center v) + (n : Real) * (mean v) ^ 2 = squaredL2 v := by
  have hc : squaredL2 (center v) = squaredL2 v -
      mean v * Finset.univ.sum (fun i => v i) := by
    rw [squaredL2_eq_dotProduct, center_selfAdjoint, center_idempotent hn,
      dotProduct_center_right, <- squaredL2_eq_dotProduct]
  rw [hc, <- card_mul_mean hn v]
  ring

/-- Centering contracts the squared Euclidean norm. -/
theorem squaredL2_center_le {n : Nat} (hn : 0 < n) (v : Vector n) :
    squaredL2 (center v) <= squaredL2 v := by
  have hp : (0 : Real) <= (n : Real) * (mean v) ^ 2 := by positivity
  have he := squaredL2_center_identity hn v
  linarith

/-- Coordinate vectors converted to mathlib's actual Euclidean-space type. -/
def euclideanVector {n : Nat} (v : Vector n) : EuclideanSpace Real (Fin n) :=
  WithLp.toLp 2 v

/-- The Euclidean norm specified by its coordinate square-sum formula. -/
def euclideanSize {n : Nat} (v : Vector n) : Real := Real.sqrt (squaredL2 v)

/-- Representation bridge to the genuine Euclidean-space norm. -/
theorem euclideanSize_eq_norm {n : Nat} (v : Vector n) :
    euclideanSize v = Norm.norm (euclideanVector v) := by
  rw [EuclideanSpace.norm_eq]
  simp [euclideanSize, squaredL2, euclideanVector, PiLp.toLp_apply,
    Real.norm_eq_abs, sq_abs]

/-- Centering is a contraction for the Euclidean norm. -/
theorem center_euclideanSize_le {n : Nat} (hn : 0 < n) (v : Vector n) :
    euclideanSize (center v) <= euclideanSize v :=
  Real.sqrt_le_sqrt (squaredL2_center_le hn v)

/-- The same contraction stated directly using mathlib's Euclidean norm. -/
theorem center_euclideanNorm_le {n : Nat} (hn : 0 < n) (v : Vector n) :
    Norm.norm (euclideanVector (center v)) <= Norm.norm (euclideanVector v) := by
  rw [<- euclideanSize_eq_norm, <- euclideanSize_eq_norm]
  exact center_euclideanSize_le hn v

/-- The infinity-norm estimate in the literal matrix notation of the paper. -/
theorem centeringMatrix_infinityNorm_le {n : Nat} (hn : 0 < n) (v : Vector n) :
    Norm.norm (Matrix.mulVec (centeringMatrix n) v) <= 2 * Norm.norm v := by
  rw [centeringMatrix_mulVec]
  exact center_infinityNorm_le hn v

/-- Squared Euclidean size is nonnegative. -/
theorem squaredL2_nonneg {n : Nat} (v : Vector n) : 0 <= squaredL2 v := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (v i))

/-- The exact conversion between empirical mean square and Euclidean size. -/
theorem euclideanSize_eq_sqrt_card_mul {n : Nat} (hn : 0 < n) (v : Vector n) :
    euclideanSize v = Real.sqrt (n : Real) *
      Real.sqrt (squaredL2 v / (n : Real)) := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hc : (n : Real) * (squaredL2 v / (n : Real)) = squaredL2 v := by
    field_simp [ne_of_gt hnR]
  calc
    euclideanSize v = Real.sqrt ((n : Real) * (squaredL2 v / (n : Real))) :=
      congrArg Real.sqrt hc.symm
    _ = Real.sqrt (n : Real) * Real.sqrt (squaredL2 v / (n : Real)) :=
      Real.sqrt_mul hnR.le _

/-- The deterministic normalized residual estimate used in Section 4.
No convergence-in-probability assertion is hidden in this finite inequality. -/
theorem centered_euclideanSize_div_dimension_le {d n : Nat}
    (hd : 0 < d) (hn : 0 < n) (v : Vector n) :
    euclideanSize (center v) / (d : Real) <=
      (Real.sqrt (n : Real) / (d : Real)) *
        Real.sqrt (squaredL2 v / (n : Real)) := by
  have hdR : (0 : Real) <= (d : Real) := by positivity
  calc
    euclideanSize (center v) / (d : Real) <= euclideanSize v / (d : Real) :=
      div_le_div_of_nonneg_right (center_euclideanSize_le hn v) hdR
    _ = (Real.sqrt (n : Real) / (d : Real)) *
        Real.sqrt (squaredL2 v / (n : Real)) := by
      rw [euclideanSize_eq_sqrt_card_mul hn]
      ring

end GaussianEllipsoid
